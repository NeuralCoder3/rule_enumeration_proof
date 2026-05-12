import EnumRules.Term

/-
# Opaque equivalence relation on terms (parameterised by extension)

## Role
The semantic equivalence `≈ₜ` decided by SMT, indexed by the runtime
extension type `Ext`. At rule construction `Ext = Empty`; at runtime
`Ext` carries the new 0-ary symbols.

## Axioms (4) — each is a family indexed by `Ext`
* `equiv_refl`, `equiv_symm`, `equiv_trans` — `≈ₜ` is an equivalence
  relation (for every `Ext`).
* `equiv_congr` — congruence over function nodes (for every `Ext`).
-/

namespace EnumRules

variable {S : Signature} {Ext : Type}

/-- Opaque equivalence relation decided by the SMT oracle. -/
opaque Equiv : Term S Ext → Term S Ext → Prop

@[inherit_doc Equiv]
scoped infix:50 " ≈ₜ " => Equiv

axiom equiv_refl (t : Term S Ext) : t ≈ₜ t

axiom equiv_symm {s t : Term S Ext} : s ≈ₜ t → t ≈ₜ s

axiom equiv_trans {s t u : Term S Ext} : s ≈ₜ t → t ≈ₜ u → s ≈ₜ u

/-- `≈ₜ` is closed under congruence: equivalent arguments give equivalent nodes. -/
axiom equiv_congr {f : S.σ} {as bs : Fin (S.arity f) → Term S Ext}
    (h : ∀ i, as i ≈ₜ bs i) : (Term.node f as) ≈ₜ (Term.node f bs)

end EnumRules
