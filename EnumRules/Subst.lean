import EnumRules.Equiv
import EnumRules.Kbo

/-
# Substitutions

## Role
Abstract type `Subst S` with action `apply σ t`. Substitutions enter
the proof in two roles: rules fire under any substitution
(`Step.root σ` in Rewrite.lean), and α-equivalence is defined via
invertible substitutions (CanonicalLayer.lean). The four behavioural
axioms describe how `apply` interacts with the order, equivalence,
the identity substitution, composition, and term structure.

## Axioms (7 total)

Type-level (3):
* `Subst : Type` opaque, `Subst.nonempty` — needed only so that
  `idSubst` is well-typed; no proof uses the witness directly.
* `apply : Subst → Term → Term` opaque — the substitution action.
* `idSubst : Subst` opaque, `Subst.comp : Subst → Subst → Subst`
  opaque — concrete witnesses for identity and composition.

Behavioural (5):
* `apply_id : apply (idSubst S) t = t`. Makes ground rule-firing
  a special case of substitution-firing. Used in `Step.root_id`
  (Rewrite.lean) — the form `Correctness.lean` uses for a "ground"
  rule application — and in `AlphaEquiv.refl`.
* `kbo_subst : s ≺ₖ t → apply σ s ≺ₖ apply σ t`.
  Substitution-monotonicity of the order. Used in `Step.kbo_of`
  (Rewrite.lean) for the root case: `r ≺ₖ l` (skeleton) ⇒ `r·σ ≺ₖ l·σ`.
* `equiv_subst : s ≈ₜ t → apply σ s ≈ₜ apply σ t`.
  Substitution-monotonicity of `≈ₜ`. Used in `Step.equiv_of` for
  the root case: a rule `(l, r)` with `l ≈ₜ r` gives `l·σ ≈ₜ r·σ`.
* `apply_comp : apply (Subst.comp ρ σ) t = apply ρ (apply σ t)`.
  Used in `Step.subst` (Rewrite.lean) to absorb a renaming `ρ`
  into the rule's substitution: a step under `σ` becomes a step
  under `Subst.comp ρ σ`. Also used in `AlphaEquiv.trans`.
* `apply_node : apply σ (Term.node f args) = Term.node f (apply σ ∘ args)`.
  Used in `Step.subst` to push `apply ρ` through the contextual
  closure of one-step rewriting.
-/

namespace EnumRules

variable {S : Signature}

/-- Abstract type of substitutions over the signature `S`. -/
opaque Subst (S : Signature) : Type

axiom Subst.nonempty (S : Signature) : Nonempty (Subst S)

instance (S : Signature) : Nonempty (Subst S) := Subst.nonempty S

instance : Nonempty (Subst S → Term S → Term S) := ⟨fun _ t => t⟩

/-- Apply a substitution to a term. -/
noncomputable opaque apply : Subst S → Term S → Term S

/-- A designated identity substitution. -/
noncomputable opaque idSubst (S : Signature) : Subst S

/-- The identity substitution acts trivially. -/
axiom apply_id (t : Term S) : apply (idSubst S) t = t

/-- The reduction order respects every substitution. -/
axiom kbo_subst {s t : Term S} (h : s ≺ₖ t) (σ : Subst S) :
    apply σ s ≺ₖ apply σ t

/-- The SMT equivalence is closed under substitution. -/
axiom equiv_subst {s t : Term S} (h : s ≈ₜ t) (σ : Subst S) :
    apply σ s ≈ₜ apply σ t

/-! ## Composition of substitutions

These two axioms make `apply` a (right) action of substitutions on
terms: composition is associative-by-design and `apply` distributes
over function nodes. They are honest definitional truths in any
concrete model (variables drawn from a fixed set, function nodes
recursing structurally). -/

/-- Composition of substitutions. -/
noncomputable opaque Subst.comp : Subst S → Subst S → Subst S

/-- Composition acts on terms via right-to-left application. -/
axiom apply_comp (ρ σ : Subst S) (t : Term S) :
    apply (Subst.comp ρ σ) t = apply ρ (apply σ t)

/-- `apply` distributes over function nodes. -/
axiom apply_node {f : S.σ} (args : Fin (S.arity f) → Term S) (σ : Subst S) :
    apply σ (Term.node f args) = Term.node f (fun i => apply σ (args i))

end EnumRules
