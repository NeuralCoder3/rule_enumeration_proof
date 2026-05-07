import EnumRules.Equiv
import EnumRules.Kbo

/-
# SMT oracle: KBO-minimal representative of the ≈ₜ-class

## Role
`smtMin t` is the SMT oracle's choice of `≺ₖ`-minimum element in
`t`'s `≈ₜ`-class. Together with `kbo_total`, this minimum is unique
per class, giving `smtMin_resp`: `s ≈ₜ t → smtMin s = smtMin t`.
This is what makes Phase 2 (lookup) of the algorithm correct.

## Axioms (2)
* `smtMin_equiv` — `smtMin t ≈ₜ t`.
* `smtMin_min` — no `≈ₜ`-equivalent term is `≺ₖ`-smaller than `smtMin t`.

## Derived theorems
* `smtMin_resp` — `≈ₜ`-equivalents have equal `smtMin`s.
  Foundation of Phase 2 lookup correctness.
* `smtMin_le` — `smtMin t = t ∨ smtMin t ≺ₖ t`.
* `smtMin_strict` — if `smtMin t ≠ t`, then `smtMin t ≺ₖ t`.
* `smtMin_idem` — `smtMin (smtMin t) = smtMin t`.
* `smtMin_size` — `size (smtMin t) ≤ size t`.
-/

namespace EnumRules

variable {S : Signature}

instance : Nonempty (Term S → Term S) := ⟨fun x => x⟩

noncomputable opaque smtMin : Term S → Term S

axiom smtMin_equiv (t : Term S) : (smtMin t) ≈ₜ t

axiom smtMin_min {t : Term S} (u : Term S) (h : u ≈ₜ t) : ¬ (u ≺ₖ (smtMin t))

theorem smtMin_equiv_symm (t : Term S) : t ≈ₜ smtMin t :=
  equiv_symm (smtMin_equiv t)

/-- The oracle respects `≈ₜ`-equivalence. By `kbo_total` + `smtMin_min`,
two minima of the same class are KBO-comparable, but neither is
KBO-smaller than the other, so they are equal. -/
theorem smtMin_resp {s t : Term S} (h : s ≈ₜ t) : smtMin s = smtMin t := by
  have h1 : (smtMin s) ≈ₜ t := equiv_trans (smtMin_equiv s) h
  have h2 : ¬ ((smtMin s) ≺ₖ (smtMin t)) := smtMin_min (smtMin s) h1
  have h3 : (smtMin t) ≈ₜ s := equiv_trans (smtMin_equiv t) (equiv_symm h)
  have h4 : ¬ ((smtMin t) ≺ₖ (smtMin s)) := smtMin_min (smtMin t) h3
  rcases kbo_total (smtMin s) (smtMin t) with heq | hlt | hlt
  · exact heq
  · exact (h2 hlt).elim
  · exact (h4 hlt).elim

theorem smtMin_idem (t : Term S) : smtMin (smtMin t) = smtMin t :=
  smtMin_resp (smtMin_equiv t)

theorem smtMin_le (t : Term S) : smtMin t = t ∨ (smtMin t) ≺ₖ t := by
  rcases kbo_total (smtMin t) t with heq | hlt | hgt
  · exact Or.inl heq
  · exact Or.inr hlt
  · exact absurd hgt (smtMin_min t (equiv_refl t))

theorem smtMin_strict {t : Term S} (h : smtMin t ≠ t) : smtMin t ≺ₖ t := by
  rcases smtMin_le t with heq | hlt
  · exact (h heq).elim
  · exact hlt

theorem smtMin_size (t : Term S) : Term.size (smtMin t) ≤ Term.size t := by
  rcases smtMin_le t with heq | hlt
  · rw [heq]
  · exact kbo_size_le hlt

end EnumRules
