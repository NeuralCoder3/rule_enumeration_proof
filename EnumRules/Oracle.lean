import EnumRules.Equiv
import EnumRules.Kbo

/-
# SMT oracle: KBO-minimal representative of the ∼-class

`smtMin t` is the output of the SMT call: an ∼-equivalent term that is
KBO-minimal in its ∼-class and whose size does not exceed `size t`.
From these three axioms we derive:

* `smtMin_resp`     : `s ≈ₜ t → smtMin s = smtMin t`
* `smtMin_idem`     : `smtMin (smtMin t) = smtMin t`
* `smtMin_le`       : `smtMin t = t ∨ smtMin t ≺ₖ t`
* `smtMin_equiv_symm` : `t ≈ₜ smtMin t`
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

/-- The oracle never grows terms: `size (smtMin t) ≤ size t`. -/
axiom smtMin_size (t : Term S) : Term.size (smtMin t) ≤ Term.size t

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

end EnumRules
