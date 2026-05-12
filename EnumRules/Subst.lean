import EnumRules.Equiv
import EnumRules.Kbo

/-
# Substitutions: var + constP, mapping rule-construction terms to
# (rule-construction or runtime) terms

A substitution is a pair of maps:
* `varM    : S.V → Term S Ext` — variable substitution.
* `constPM : S.C → Term S Ext` — ConstPlaceholder substitution.

`apply σ : Term S Empty → Term S Ext` takes a rule-construction term
(no `ext` constructor on input) and produces a term over the same
extension as `σ`.

## The three intended substitution kinds

The `Subst` type is shared across three semantically-distinct uses,
distinguished by `Ext` and by what the maps' codomains *should* be:

1. **Rule-time variable substitution** (`Ext = Empty`):
   - `σ.varM : S.V → Term S Empty` — substitute into rule terms
     (var + constP + node, no ext). General term substitution.
   - `σ.constPM : S.C → Term S Empty` — at rule time, ConstPlaceholders
     stay as constPs (identity or a permutation), i.e.,
     `σ.constPM c = Term.constP _`.

2. **Runtime variable substitution** (`Ext` = an extension type):
   - `σ.varM : S.V → Term S Ext` — should map to *runtime* terms
     (only sig + sig-ext; output satisfies `Term.IsRuntime`).

3. **Runtime ConstPlaceholder substitution** (`Ext` = an extension type):
   - `σ.constPM : S.C → Term S Ext` — should map to *extension 0-ary
     symbols*, i.e., `σ.constPM c = Term.ext _`.

The structural definition of `Subst` doesn't enforce these constraints
in the type; they're invariants maintained by callers. The proofs in
`CanonicalLayer.lean` that consume substitutions either don't need
the invariants (e.g., generic `Step.equiv_of`/`kbo_of`) or take them
as hypotheses (e.g., runtime-preservation in
`Step.preserves_runtime`, via `smtMin_apply_runtime`).

## Axioms in this file (2)

* `kbo_subst` — substitution-monotonicity of `≺ₖ`. Given a rule's
  KBO-decrease at the schema level (`r ≺ₖ l` in `Term S Empty`), every
  instance `apply σ r ≺ₖ apply σ l` (in `Term S Ext`).
* `equiv_subst` — `≈ₜ` is closed under substitution.
-/

namespace EnumRules

variable {S : Signature}

/-! ## Substitutions -/

/-- A substitution is a pair of variable-map and constP-map. -/
structure Subst (S : Signature) (Ext : Type) where
  varM    : S.V → Term S Ext
  constPM : S.C → Term S Ext

namespace Subst

/-- The identity substitution: maps each variable to itself and each
ConstPlaceholder to itself. -/
def id : Subst S Empty :=
  { varM := Term.var, constPM := Term.constP }

end Subst

/-- Apply a substitution to a rule-construction term, producing a
runtime (or rule-construction) term. The `Term.ext` case can't arise
on input because the input is `Term S Empty`. -/
def apply {Ext : Type} (σ : Subst S Ext) : Term S Empty → Term S Ext
  | .var v       => σ.varM v
  | .constP c    => σ.constPM c
  | .node f args => .node f (fun i => apply σ (args i))
  | .ext e       => Empty.elim e
termination_by structural t => t

@[simp]
theorem apply_var {Ext : Type} (σ : Subst S Ext) (v : S.V) :
    apply σ (.var v) = σ.varM v := rfl

@[simp]
theorem apply_constP {Ext : Type} (σ : Subst S Ext) (c : S.C) :
    apply σ (.constP c) = σ.constPM c := rfl

@[simp]
theorem apply_node {Ext : Type} (σ : Subst S Ext) {f : S.σ}
    (args : Fin (S.arity f) → Term S Empty) :
    apply σ (.node f args) = .node f (fun i => apply σ (args i)) := rfl

/-! ### Identity acts trivially -/

theorem apply_id (t : Term S Empty) : apply Subst.id t = t := by
  induction t with
  | var v => rfl
  | constP c => rfl
  | node f args ih => simp [apply_node, ih]
  | ext e => exact Empty.elim e

/-! ## Composition -/

/-- Composition of substitutions: `(comp ρ σ) v = apply ρ (σ v)` for
the variable map, and similar for `constP`. Lets us compose a
construction-time substitution `σ : Subst S Empty` with a runtime
substitution `ρ : Subst S Ext`. -/
def Subst.comp {Ext : Type} (ρ : Subst S Ext) (σ : Subst S Empty) : Subst S Ext where
  varM    := fun v => apply ρ (σ.varM v)
  constPM := fun c => apply ρ (σ.constPM c)

theorem apply_comp {Ext : Type} (ρ : Subst S Ext) (σ : Subst S Empty)
    (t : Term S Empty) : apply (ρ.comp σ) t = apply ρ (apply σ t) := by
  induction t with
  | var v => rfl
  | constP c => rfl
  | node f args ih => simp [apply_node, ih]
  | ext e => exact Empty.elim e

/-! ## Behavioural axioms -/

/-- Substitution-monotonicity of `≺ₖ`: a rule's schema-level decrease
lifts to every substitution instance. -/
axiom kbo_subst {Ext : Type} {s t : Term S Empty}
    (h : s ≺ₖ t) (σ : Subst S Ext) :
    apply σ s ≺ₖ apply σ t

/-- `≈ₜ` is closed under substitution. -/
axiom equiv_subst {Ext : Type} {s t : Term S Empty}
    (h : s ≈ₜ t) (σ : Subst S Ext) :
    apply σ s ≈ₜ apply σ t

/-! ## Canonical substitution from an order embedding

Given an order embedding `embed : Ext ↪o S.C` (only available when
`|Ext| ≤ |S.C|`), the canonical "rename constPs along embed" runtime
substitution `σ_of_embed embed`:

* On variables: identity-ish (irrelevant — we apply only to terms
  with `NoVar`, so `varM` is never invoked).
* On ConstPlaceholders: `σ_of_embed.constPM c = e` when `embed e = c`,
  i.e., maps each `embed e ∈ S.C` back to `e ∈ Ext`. For `c` outside
  `embed`'s image, returns an arbitrary `Ext` element.

This substitution's effect is: `Term.constP (embed e)` becomes
`Term.ext e` after `apply`, so a construction-time template with
constP-leaves in `embed`'s image becomes the corresponding runtime
term with ext-leaves.

For terms whose constPs lie in `embed`'s image, the substitution is
"essentially a renaming" — an order-preserving bijection. SMT
equivalence and KBO commute with such renamings (see
`smtMin_commutes_embed` in `CanonicalLayer.lean`). -/
section OfEmbed
variable {Ext : Type} [Fintype Ext] [DecidableEq Ext] [LinearOrder Ext]
  [Inhabited Ext]

/-- The canonical runtime substitution from an order embedding. -/
noncomputable def Subst.of_embed (embed : Ext ↪o S.C) : Subst S Ext where
  varM := fun _ => Term.ext default  -- arbitrary (won't be used on NoVar input)
  constPM := fun c =>
    if h : ∃ e : Ext, embed e = c then
      Term.ext (Classical.choose h)
    else
      Term.ext default

end OfEmbed

end EnumRules
