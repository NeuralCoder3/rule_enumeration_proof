import EnumRules.Equiv
import EnumRules.Kbo

/-
# SMT oracle: KBO-minimal representative of the ≈ₜ-class

## Role
`smtMin t` returns a `≺ₖ`-minimum element of `t`'s `≈ₜ`-class.
Foundation for both rule synthesis (rules are `(l, smtMin l)` with
`smtMin l ≠ l`) and the lookup phase of normalisation
(`smtMin_resp` makes lookup respect `≈ₜ`).

## Axioms (2)
* `smtMin_equiv` — `smtMin t ≈ₜ t`. The output is in the right class.
  Used in `rule_equiv` (Algorithm) to show every rule preserves `≈ₜ`,
  and inside `smtMin_resp` and `smtMin_le`.
* `smtMin_min` — no `≈ₜ`-equivalent term is `≺ₖ`-smaller than `smtMin t`.
  Used in `rule_kbo` (Algorithm) to show rules are `≺ₖ`-decreasing,
  in `subterm_of_minimal_is_minimal`, and inside `smtMin_resp`.

Everything else (`smtMin_resp`, `smtMin_idem`, `smtMin_le`,
`smtMin_size`, `smtMin_equiv_symm`) is derived from these two plus
the `Equiv` and `Kbo` axioms.
-/

namespace EnumRules

variable {S : Signature}

instance : Nonempty (Term S → Term S) :=
  ⟨fun x => x⟩
/-- SMT oracle returning the KBO-minimal term equivalent to its input. -/
noncomputable opaque smtMin : Term S → Term S

/-- The oracle returns an ∼-equivalent term. -/
axiom smtMin_equiv (t : Term S) : (smtMin t) ≈ₜ t

/-- The oracle's output is KBO-minimal in its ∼-class: no ∼-equivalent term
is strictly KBO-smaller. -/
axiom smtMin_min {t : Term S} (u : Term S) (h : u ≈ₜ t) : ¬ (u ≺ₖ (smtMin t))

/-- The oracle's output is also ∼-equivalent in the other direction. -/
theorem smtMin_equiv_symm (t : Term S) : t ≈ₜ smtMin t :=
  equiv_symm (smtMin_equiv t)

/-- KBO totality + minimality: the oracle respects the equivalence relation. -/
theorem smtMin_resp {s t : Term S} (h : s ≈ₜ t) : smtMin s = smtMin t := by
  -- smtMin s ≈ s ≈ t, so smtMin s is in the ∼-class of t, hence ¬ (smtMin s ≺ smtMin t).
  have h1 : (smtMin s) ≈ₜ t := equiv_trans (smtMin_equiv s) h
  have h2 : ¬ ((smtMin s) ≺ₖ (smtMin t)) := smtMin_min (smtMin s) h1
  -- Conversely, smtMin t ≈ t ≈ s, so ¬ (smtMin t ≺ smtMin s).
  have h3 : (smtMin t) ≈ₜ s := equiv_trans (smtMin_equiv t) (equiv_symm h)
  have h4 : ¬ ((smtMin t) ≺ₖ (smtMin s)) := smtMin_min (smtMin t) h3
  -- By totality, they must be equal.
  rcases kbo_total (smtMin s) (smtMin t) with heq | hlt | hlt
  · exact heq
  · exact (h2 hlt).elim
  · exact (h4 hlt).elim

/-- Idempotence of the oracle. -/
theorem smtMin_idem (t : Term S) : smtMin (smtMin t) = smtMin t := by
  exact smtMin_resp (smtMin_equiv t)

/-- Either the oracle returns its input unchanged, or strictly decreases it. -/
theorem smtMin_le (t : Term S) : smtMin t = t ∨ (smtMin t) ≺ₖ t := by
  rcases kbo_total (smtMin t) t with heq | hlt | hgt
  · exact Or.inl heq
  · exact Or.inr hlt
  · -- t ≺ smtMin t, but t is ∼-equivalent to t, contradicting minimality of smtMin t.
    exact absurd hgt (smtMin_min t (equiv_refl t))

/-- The oracle never grows the term: follows from `smtMin_le` and the KBO weight-1
property that KBO-smaller implies not larger in size. -/
theorem smtMin_size (t : Term S) : Term.size (smtMin t) ≤ Term.size t := by
  rcases smtMin_le t with (heq | hlt)
  · rw [heq]
  · exact kbo_size_le hlt

end EnumRules
