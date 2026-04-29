import EnumRules.Term

/-
# Opaque equivalence relation on terms

The SMT oracle decides some equivalence `∼` between terms. We axiomatize
it as an equivalence relation closed under congruence. Nothing else is
needed for the correctness proof.
-/

namespace EnumRules

variable {S : Signature}

/-- Opaque equivalence relation decided by the SMT oracle. -/
opaque Equiv : Term S → Term S → Prop

@[inherit_doc Equiv]
scoped infix:50 " ≈ₜ " => Equiv

axiom equiv_refl (t : Term S) : t ≈ₜ t

axiom equiv_symm {s t : Term S} : s ≈ₜ t → t ≈ₜ s

axiom equiv_trans {s t u : Term S} : s ≈ₜ t → t ≈ₜ u → s ≈ₜ u

/-- `∼` is closed under congruence: equivalent arguments give equivalent nodes. -/
axiom equiv_congr {f : S.σ} {as bs : Fin (S.arity f) → Term S}
    (h : ∀ i, as i ≈ₜ bs i) : (Term.node f as) ≈ₜ (Term.node f bs)

end EnumRules
