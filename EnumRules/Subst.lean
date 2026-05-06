import EnumRules.Equiv
import EnumRules.Kbo

/-
# Substitutions and substitution-monotonicity

Abstract type of substitutions, with the two key axioms used everywhere
in the rewriting theory:

* `kbo_subst` — the reduction order respects every substitution.
  This is exactly the property that lets the SMT-synthesised order
  on rule skeletons (`r ≺ₖ l`) imply `r·σ ≺ₖ l·σ` for every `σ`.
* `equiv_subst` — the SMT equivalence is closed under substitution.

`idSubst` and `apply_id` give a definite identity element so that any
ground rewrite step is automatically a substitution-rewrite step under
the identity.
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

end EnumRules
