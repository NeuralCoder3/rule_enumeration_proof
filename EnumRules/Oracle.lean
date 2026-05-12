import EnumRules.Equiv
import EnumRules.Kbo

/-
# SMT oracle (parameterised by extension)

## Role
`smtMin t` is the SMT oracle's choice of `≺ₖ`-minimum element in
`t`'s `≈ₜ`-class. Indexed by the runtime extension type `Ext`.

## Axioms (3) — each is a family indexed by `Ext`
* `smtMin_equiv` — `smtMin t ≈ₜ t`.
* `smtMin_min` — no `≈ₜ`-equivalent term is `≺ₖ`-smaller than `smtMin t`.
* `smtMin_le` — `smtMin t = t ∨ smtMin t ≺ₖ t`.

## Derived theorems (each indexed by Ext)
* `smtMin_resp` — for runtime `s ≈ₜ t`, `smtMin s = smtMin t`.
* `smtMin_strict` — if `smtMin t ≠ t`, then `smtMin t ≺ₖ t`.
* `smtMin_size` — `size (smtMin t) ≤ size t`.
-/

namespace EnumRules

variable {S : Signature} {Ext : Type}

instance : Nonempty (Term S Ext → Term S Ext) := ⟨fun x => x⟩

noncomputable opaque smtMin : Term S Ext → Term S Ext

axiom smtMin_equiv (t : Term S Ext) : (smtMin t) ≈ₜ t

axiom smtMin_min {t : Term S Ext} (u : Term S Ext) (h : u ≈ₜ t) : ¬ (u ≺ₖ (smtMin t))

theorem smtMin_equiv_symm (t : Term S Ext) : t ≈ₜ smtMin t :=
  equiv_symm (smtMin_equiv t)

axiom smtMin_le (t : Term S Ext) : smtMin t = t ∨ (smtMin t) ≺ₖ t

theorem smtMin_resp {s t : Term S Ext}
    (hs : Term.NoVar (smtMin s)) (ht : Term.NoVar (smtMin t))
    (h : s ≈ₜ t) : smtMin s = smtMin t := by
  have hst : (smtMin s) ≈ₜ t := equiv_trans (smtMin_equiv s) h
  have hts : (smtMin t) ≈ₜ s := equiv_trans (smtMin_equiv t) (equiv_symm h)
  rcases kbo_total hs ht with heq | hlt | hlt
  · exact heq
  · exact absurd hlt (smtMin_min _ hst)
  · exact absurd hlt (smtMin_min _ hts)

theorem smtMin_strict {t : Term S Ext} (h : smtMin t ≠ t) : smtMin t ≺ₖ t :=
  (smtMin_le t).resolve_left h

theorem smtMin_size (t : Term S Ext) : Term.size (smtMin t) ≤ Term.size t := by
  rcases smtMin_le t with heq | hlt
  · rw [heq]
  · exact kbo_size_le hlt

end EnumRules
