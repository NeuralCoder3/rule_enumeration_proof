import EnumRules.Algorithm

/-
# Correctness theorems

* `terminates`        — `Step (R S n)` is well-founded (reverse direction).
* `reaches_smtMin`    — every term of size ≤ n rewrites to its `smtMin`.
* `confluent`         — any reduct of a size-≤-n term meets the `smtMin` reduct.
* `ground_complete`   — ∼-equivalent terms of size ≤ n share a common reduct.
-/

namespace EnumRules

variable {S : Signature}

/-! ## Termination -/

/-- The one-step rewrite relation `(Step (R S n))`, viewed with target before
source (i.e. the "strictly smaller" relation on terms), is well-founded. -/
theorem terminates (n : Nat) :
    WellFounded (fun t s : Term S => Step (R S n) s t) := by
  apply Subrelation.wf (r := fun t s : Term S => t ≺ₖ s)
  · intro t s h
    exact Step.kbo_of (fun hlr => rule_kbo hlr) h
  · exact InvImage.wf (f := id) kbo_wf

/-! ## Every size-≤-n term reaches its `smtMin` in one root step (or is already minimal). -/

theorem reaches_smtMin (n : Nat) (s : Term S) (h : Term.size s ≤ n) :
    StepStar (R S n) s (smtMin s) := by
  by_cases hfix : smtMin s = s
  · simpa [hfix] using (Relation.ReflTransGen.refl : StepStar (R S n) s s)
  · -- s ≠ smtMin s, so the rule (s, smtMin s) is in R n.
    have hmem : (s, smtMin s) ∈ R S n :=
      rule_mem_of_size h (fun h => hfix h)
    exact Relation.ReflTransGen.single (Step.root hmem)

/-! ## Confluence / unique normal forms -/

/-- Any reduct of a size-≤-n term `s` is itself ∼-equivalent to `s`, has
size ≤ n, and still reaches `smtMin s`. Combined, this gives that `s`
and any reduct meet at `smtMin s`. -/
theorem confluent (n : Nat) {s t : Term S}
    (hs : Term.size s ≤ n) (hst : StepStar (R S n) s t) :
    StepStar (R S n) s (smtMin s) ∧ StepStar (R S n) t (smtMin s) := by
  refine ⟨reaches_smtMin n s hs, ?_⟩
  -- t ≈ s, so smtMin t = smtMin s.
  have hequiv : s ≈ₜ t :=
    StepStar.equiv_of (fun hlr => rule_equiv hlr) hst
  have hsize : Term.size t ≤ Term.size s :=
    StepStar.size_of (fun hlr => rule_size hlr) hst
  have ht : Term.size t ≤ n := le_trans hsize hs
  have hmin : smtMin t = smtMin s := (smtMin_resp hequiv).symm
  have hreach : StepStar (R S n) t (smtMin t) := reaches_smtMin n t ht
  rw [hmin] at hreach
  exact hreach

/-! ## Ground-completeness: the target theorem. -/

theorem ground_complete (n : Nat) {s t : Term S}
    (hs : Term.size s ≤ n) (ht : Term.size t ≤ n) (hst : s ≈ₜ t) :
    ∃ u, StepStar (R S n) s u ∧ StepStar (R S n) t u := by
  refine ⟨smtMin s, reaches_smtMin n s hs, ?_⟩
  have h : smtMin t = smtMin s := smtMin_resp (equiv_symm hst)
  have hreach : StepStar (R S n) t (smtMin t) := reaches_smtMin n t ht
  rw [h] at hreach
  exact hreach

end EnumRules
