import EnumRules.Term

/-
# Opaque equivalence relation on terms

## Role
The semantic equivalence `≈ₜ`. Used to state soundness
of rewriting (`Step.equiv_of`) and the completeness conclusion

## Axioms (4)
* `equiv_refl`, `equiv_symm`, `equiv_trans` — `≈ₜ` is an equivalence relation.
  Used everywhere a chain of `≈ₜ`-equalities is built (e.g.
  `complete_common_normal_form` chains `s ≈ s' ≈ t' ≈ t` and applies
  `smtMin_resp` to the ground endpoints).
* `equiv_congr` — congruence over function nodes. Used in
  `Step.equiv_of` (Rewrite.lean) for the contextual case.
-/

namespace EnumRules

variable {S : Signature}

/-- Opaque equivalence relation -/
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
