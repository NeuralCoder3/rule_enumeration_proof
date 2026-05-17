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
as hypotheses (e.g., `Step.preserves_NoVar`, via `smtMin_apply_NoVar`).

## Axioms in this file (3)

* `kbo_subst` — substitution-monotonicity of `≺ₖ`. Given a rule's
  KBO-decrease at the schema level (`r ≺ₖ l` in `Term S Empty`), every
  instance `apply σ r ≺ₖ apply σ l` (in `Term S Ext`).
* `equiv_subst` — `≈ₜ` is closed under substitution (`Term S Empty
  → Term S Ext`).
* `equiv_embExt` — `≈ₜ` is invariant under the `Term S Ext → Term S
  Empty` lift `embExt` for a `Set.InjOn`-style injection. Used by
  the runtime completeness theorem.
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

/-! ## How `apply σ` interacts with `varSet` and `constPSet` -/

theorem apply_varSet {Ext : Type} (σ : Subst S Ext) (t : Term S Empty) :
    (apply σ t).varSet =
      t.varSet.biUnion (fun v => (σ.varM v).varSet) ∪
      t.constPSet.biUnion (fun c => (σ.constPM c).varSet) := by
  induction t with
  | var v =>
      simp [apply_var, Term.varSet_var, Term.constPSet_var]
  | constP c =>
      simp [apply_constP, Term.varSet_constP, Term.constPSet_constP]
  | node f args ih =>
      rw [apply_node, Term.varSet_node, Term.varSet_node, Term.constPSet_node]
      rw [Finset.biUnion_biUnion, Finset.biUnion_biUnion]
      rw [← Finset.biUnion_union]
      apply Finset.biUnion_congr rfl
      intro i _
      exact ih i
  | ext e => exact e.elim

theorem apply_constPSet {Ext : Type} (σ : Subst S Ext) (t : Term S Empty) :
    (apply σ t).constPSet =
      t.varSet.biUnion (fun v => (σ.varM v).constPSet) ∪
      t.constPSet.biUnion (fun c => (σ.constPM c).constPSet) := by
  induction t with
  | var v =>
      simp [apply_var, Term.varSet_var, Term.constPSet_var]
  | constP c =>
      simp [apply_constP, Term.varSet_constP, Term.constPSet_constP]
  | node f args ih =>
      rw [apply_node, Term.constPSet_node, Term.varSet_node, Term.constPSet_node]
      rw [Finset.biUnion_biUnion, Finset.biUnion_biUnion]
      rw [← Finset.biUnion_union]
      apply Finset.biUnion_congr rfl
      intro i _
      exact ih i
  | ext e => exact e.elim

/-- Monotonicity of `apply σ` on `varSet` and `constPSet`: if both sets
of `t₁` are contained in those of `t₂`, then so are those of
`apply σ t₁` in `apply σ t₂`. -/
theorem apply_varSet_subset {Ext : Type} (σ : Subst S Ext)
    {t₁ t₂ : Term S Empty}
    (hv : t₁.varSet ⊆ t₂.varSet) (hc : t₁.constPSet ⊆ t₂.constPSet) :
    (apply σ t₁).varSet ⊆ (apply σ t₂).varSet := by
  rw [apply_varSet, apply_varSet]
  exact Finset.union_subset_union (Finset.biUnion_subset_biUnion_of_subset_left _ hv)
                                   (Finset.biUnion_subset_biUnion_of_subset_left _ hc)

theorem apply_constPSet_subset {Ext : Type} (σ : Subst S Ext)
    {t₁ t₂ : Term S Empty}
    (hv : t₁.varSet ⊆ t₂.varSet) (hc : t₁.constPSet ⊆ t₂.constPSet) :
    (apply σ t₁).constPSet ⊆ (apply σ t₂).constPSet := by
  rw [apply_constPSet, apply_constPSet]
  exact Finset.union_subset_union (Finset.biUnion_subset_biUnion_of_subset_left _ hv)
                                   (Finset.biUnion_subset_biUnion_of_subset_left _ hc)

/-! ## Inverse substitution for `Term.embExt`

Given a Finset `E : Finset Ext` and `f : Ext → S.C` that is *injective
on E* (Set.InjOn-style), `Subst.invEmb E f` is the inverse of
`Term.embExt f` for terms whose ext-leaves lie in `E`. It sends
`constP c` back to `Term.ext e` when `c = f e` for some `e ∈ E`
(`e` chosen by classical choice, uniquely determined by injectivity on
`E`), and otherwise preserves `constP c`. -/

/-- The inverse substitution to `Term.embExt f` restricted to a Finset
`E`. Variables are preserved (irrelevant for `NoVar` inputs). -/
noncomputable def Subst.invEmb {Ext : Type} (E : Finset Ext)
    (f : Ext → S.C) : Subst S Ext where
  varM    := Term.var
  constPM := fun c =>
    open Classical in
    if h : ∃ e ∈ E, f e = c then
      Term.ext (Classical.choose h)
    else
      Term.constP c

/-- For `e ∈ E`, `(invEmb E f).constPM (f e) = Term.ext e` provided
`f` is injective on `E`. -/
theorem invEmb_constPM_image {Ext : Type} {E : Finset Ext} {f : Ext → S.C}
    (hinj : ∀ e₁ ∈ E, ∀ e₂ ∈ E, f e₁ = f e₂ → e₁ = e₂)
    {e : Ext} (he : e ∈ E) :
    (Subst.invEmb E f).constPM (f e) = Term.ext e := by
  have hex : ∃ e' ∈ E, f e' = f e := ⟨e, he, rfl⟩
  show (open Classical in
    if h : ∃ e' ∈ E, f e' = f e then Term.ext (Classical.choose h)
    else Term.constP (f e)) = Term.ext e
  rw [dif_pos hex]
  congr 1
  obtain ⟨hmem, hfeq⟩ := Classical.choose_spec hex
  exact hinj _ hmem _ he hfeq

/-- `apply (Subst.invEmb E f) ∘ Term.embExt f` is the identity on
`IsRuntime` terms whose ext-leaves lie in `E`, provided `f` is
injective on `E`. -/
theorem apply_invEmb_embExt {Ext : Type} [DecidableEq Ext]
    {E : Finset Ext} {f : Ext → S.C}
    (hinj : ∀ e₁ ∈ E, ∀ e₂ ∈ E, f e₁ = f e₂ → e₁ = e₂)
    {t : Term S Ext} (ht : Term.IsRuntime t) (hE : t.usedExt ⊆ E) :
    apply (Subst.invEmb E f) (Term.embExt f t) = t := by
  induction t with
  | var v       => exact ht.elim
  | constP c    => exact ht.elim
  | node f' args ih =>
      rw [Term.embExt_node, apply_node]
      refine Term.node_ext fun i => ih i (ht i) ?_
      exact subset_trans (Term.usedExt_arg_subset args i) hE
  | ext e       =>
      have he : e ∈ E := hE (by simp [Term.usedExt_ext])
      rw [Term.embExt_ext, apply_constP]
      exact invEmb_constPM_image hinj he

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

/-- ≈ₜ is invariant under the `embExt` renaming: replacing each
ext-leaf `e` by `constP (f e)` preserves equivalence, provided `f`
is injective on the union of `s.usedExt` and `t.usedExt`. The
semantic content: SMT treats ext-leaves and constP-leaves as
uninterpreted constants of the same kind, and a consistent injective
relabelling is invisible to the theory. -/
axiom equiv_embExt {Ext : Type} [DecidableEq Ext]
    {s t : Term S Ext} (hs : Term.IsRuntime s) (ht : Term.IsRuntime t)
    (f : Ext → S.C)
    (hinj : ∀ e₁ ∈ s.usedExt ∪ t.usedExt, ∀ e₂ ∈ s.usedExt ∪ t.usedExt,
              f e₁ = f e₂ → e₁ = e₂)
    (heq : s ≈ₜ t) :
    Term.embExt f s ≈ₜ Term.embExt f t

end EnumRules
