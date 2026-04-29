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

/-! ## Every size-≤-n term reaches its `smtMin`. -/

theorem reaches_smtMin (n : Nat) (s : Term S) (h : Term.size s ≤ n) :
    StepStar (R S n) s (smtMin s) := by
  let P : Term S → Prop := fun t => Term.size t ≤ n → StepStar (R S n) t (smtMin t)
  have hP : ∀ t, P t := by
    intro t
    refine kbo_wf.induction t (fun u ih => ?_)
    intro hu
    by_cases hfix : smtMin u = u
    · simpa [hfix] using (Relation.ReflTransGen.refl : StepStar (R S n) u u)
    · by_cases hmem : (u, smtMin u) ∈ R S n
      · exact Relation.ReflTransGen.single (Step.root hmem)
      · rcases not_mem_R_of_size hu hmem with (heq | hsp)
        · exact (hfix heq).elim
        · rcases hsp with ⟨v, huv, hsize_v⟩
          have h_le : Term.size u - 1 ≤ n := by omega
          have huv_n : StepStar (R S n) u v :=
            StepStar.lift (R_subset h_le) huv
          rcases StepStar.kbo_of (fun hlr => rule_kbo hlr) huv_n with (heq_uv | hlt_vu)
          · rw [heq_uv] at hsize_v
            exact absurd hsize_v (Nat.lt_irrefl _)
          · have hv_size : Term.size v ≤ n := by omega
            have hreach_v : StepStar (R S n) v (smtMin v) := ih v hlt_vu hv_size
            have hequiv_uv : u ≈ₜ v :=
              StepStar.equiv_of (fun hlr => rule_equiv hlr) huv_n
            have hmin_eq : smtMin v = smtMin u := (smtMin_resp hequiv_uv).symm
            rw [hmin_eq] at hreach_v
            exact Relation.ReflTransGen.trans huv_n hreach_v
  exact hP s h

/-! ## Confluence / unique normal forms -/

/-- Any reduct of a size-≤-n term `s` is itself ∼-equivalent to `s`, has
size ≤ n, and still reaches `smtMin s`. Combined, this gives that `s`
and any reduct meet at `smtMin s`. -/
theorem confluent (n : Nat) {s t : Term S}
    (hs : Term.size s ≤ n) (hst : StepStar (R S n) s t) :
    StepStar (R S n) s (smtMin s) ∧ StepStar (R S n) t (smtMin s) := by
  refine ⟨reaches_smtMin n s hs, ?_⟩
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
