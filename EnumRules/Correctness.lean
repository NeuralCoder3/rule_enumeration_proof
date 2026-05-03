import EnumRules.Algorithm

open scoped Classical

namespace EnumRules

variable {S : Signature}

/-! ## Embed StepStar into StepStarR -/
theorem StepStar.toStepStarR {R : RuleSet S} {s t : Term S}
    (h : StepStar R s t) : StepStarR R s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (StepR.step hstep)

/-! ## Termination -/
theorem terminates (n : Nat) :
    WellFounded (fun t s : Term S => Step (R S n) s t) := by
  apply Subrelation.wf (r := fun t s : Term S => t ≺ₖ s)
  · intro t s h; exact Step.kbo_of (fun hlr => rule_kbo hlr) h
  · exact InvImage.wf (f := id) kbo_wf

/-! ## Every minimal term has a canonical version in I -/

theorem minimal_has_canonical_in_I (m : Term S) (hmin : smtMin m = m)
    (hsize : Term.size m ≤ n) :
    ∃ c, m ≈ᵣ c ∧ Canonical c ∧ smtMin c = c ∧ c ∈ I S n := by
  revert m
  induction n with
  | zero =>
    intro m _ hsize
    have hpos : 1 ≤ Term.size m := Term.size_pos m; omega
  | succ n ih =>
    intro m hmin hsize
    rcases exists_canonical m with ⟨c, h_ren, hcan⟩
    have h_c_smteq : smtMin c ≈ᵣ c := by
      have h1 : smtMin c ≈ᵣ smtMin m := rename_smtMin (rename_symm h_ren)
      rw [hmin] at h1; exact rename_trans h1 h_ren
    have h_c_min : smtMin c = c := canonical_minimal hcan h_c_smteq
    have h_c_sz : Term.size c = Term.size m := (rename_size h_ren).symm
    rcases Nat.lt_or_eq_of_le (h_c_sz ▸ hsize) with (hlt | heq)
    · have hle_n : Term.size c ≤ n := by omega
      rcases ih c h_c_min hle_n with ⟨c', h_ren', hcan', hmin', hI⟩
      refine ⟨c', rename_trans h_ren h_ren', hcan', hmin', I_subset (by omega) hI⟩
    · rcases c with ⟨f, args⟩
      have h_sub_min : ∀ i, smtMin (args i) = args i :=
        subterm_of_minimal_is_minimal h_c_min
      have h_sub_sz : ∀ i, Term.size (args i) ≤ n := by
        intro i; have hlt := Term.size_arg_lt f args i; omega
      have h_sub_canon : ∀ i, ∃ ci, (args i) ≈ᵣ ci ∧ Canonical ci ∧
          smtMin ci = ci ∧ ci ∈ I S n :=
        fun i => ih (args i) (h_sub_min i) (h_sub_sz i)
      choose ac h_ac_ren h_ac_can h_ac_mi using h_sub_canon
      have h_ac_in_I : ∀ i, ac i ∈ I S n := fun i => (h_ac_mi i).2
      let c' := Term.node f ac
      have h_c'_can : Canonical c' := canonical_node h_ac_can
      have h_c'_ren : (Term.node f args) ≈ᵣ c' := rename_congr h_ac_ren
      have h_c'_sz : Term.size c' = n + 1 := by
        calc
          Term.size c' = Term.size (Term.node f args) := by rw [rename_size h_c'_ren]
          _ = n + 1 := heq
      have h_c'_irr : c' ∈ termsFromIrreducible S (I S n) (n + 1) := by
        rw [mem_termsFromIrreducible]; refine ⟨h_c'_sz, ?_⟩
        intro f' args' heq'
        have hf : f' = f := by injection heq'
        have ha : HEq args' ac := by injection heq'
        cases hf
        have ha_eq : args' = ac := eq_of_heq ha
        rw [ha_eq]
        exact h_ac_in_I
      have h_c'_enum : c' ∈ termsFromIrreducibleRenamings S (I S n) (n + 1) := by
        rw [mem_termsFromIrreducibleRenamings]
        exact ⟨h_c'_sz, c', h_c'_irr, rename_refl _⟩
      have h_c'_smteq : smtMin c' ≈ᵣ c' := by
        have h1 : smtMin c' ≈ᵣ smtMin (Term.node f args) :=
          rename_smtMin (rename_symm h_c'_ren)
        rw [h_c_min] at h1; exact rename_trans h1 h_c'_ren
      have h_c'_min : smtMin c' = c' := canonical_minimal h_c'_can h_c'_smteq
      have h_c'_not_simp : ¬ simplifiesWith (R S n) c' := by
        intro hsp
        rcases simplifiesWith.kbo_lt (fun hlr => rule_kbo hlr) hsp with
          ⟨u, htu, _, hlt_u⟩
        have hequiv : c' ≈ₜ u := StepStar.equiv_of (fun hlr => rule_equiv hlr) htu
        have hc := smtMin_min (t := c') (u := u) (equiv_symm hequiv)
        rw [h_c'_min] at hc; exact hc hlt_u
      have hmem_I : c' ∈ I S (n + 1) := by
        rw [I]
        have hmem : c' ∈ ((termsFromIrreducibleRenamings S (I S n) (n + 1)).filter
            (fun l => Canonical l ∧ ¬ simplifiesWith (R S n) l ∧ smtMin l = l)) :=
          Finset.mem_filter.mpr ⟨h_c'_enum, h_c'_can, h_c'_not_simp, h_c'_min⟩
        exact Finset.mem_union_right _ hmem
      exact ⟨c', rename_trans h_ren h_c'_ren, h_c'_can, h_c'_min, hmem_I⟩

/-! ## Helper: algorithm handles an enumerated canonical term -/

theorem enum_handles (n : Nat) (t : Term S) (hsz : Term.size t = n + 1)
    (hcan : Canonical t) (henum : t ∈ termsFromIrreducibleRenamings S (I S n) (n + 1))
    (ih : ∀ (s : Term S), Term.size s ≤ n → ∃ s', s ≈ᵣ s' ∧ Canonical s' ∧
      StepStarR (R S n) s' (smtMin s') ∧ smtMin s' ≈ᵣ smtMin s) :
    StepStarR (R S (n + 1)) t (smtMin t) := by
  by_cases h_min : smtMin t = t
  · rw [h_min]
  by_cases h_simp : simplifiesWith (R S n) t
  · rcases h_simp with ⟨v, htv, hsize_v⟩
    have hv_sz : Term.size v ≤ n := by omega
    rcases ih v hv_sz with ⟨v', h_ren_v, _, hreach_v', hsmteq_v'⟩
    have hequiv : t ≈ₜ v := StepStar.equiv_of (fun hlr => rule_equiv hlr) htv
    have hsmteq_v : smtMin v = smtMin t := (smtMin_resp hequiv).symm
    exact (StepStarR.lift (R_subset (Nat.le_succ _)) htv.toStepStarR).trans
      ((Relation.ReflTransGen.single (StepR.rename h_ren_v)).trans
        ((StepStarR.lift (R_subset (Nat.le_succ _)) hreach_v').trans
          (Relation.ReflTransGen.single (StepR.rename (hsmteq_v ▸ hsmteq_v')))))
  · have hmem : (t, smtMin t) ∈ R S (n + 1) :=
      mem_R.mpr ⟨n + 1, le_refl _, hsz, henum, hcan, rfl,
        fun h => h_min h.symm, h_simp⟩
    exact Relation.ReflTransGen.single (StepR.step (Step.root hmem))

/-! ## Main lemma -/

theorem reaches_smtMin_up_to_rename (n : Nat) (s : Term S)
    (hsize : Term.size s ≤ n) :
    ∃ s', s ≈ᵣ s' ∧ Canonical s' ∧
      StepStarR (R S n) s' (smtMin s') ∧ smtMin s' ≈ᵣ smtMin s := by
  revert s
  induction n with
  | zero =>
    intro s hsize
    have hpos : 1 ≤ Term.size s := Term.size_pos s; omega
  | succ n ih =>
    intro s hsize
    rcases exists_canonical s with ⟨s₀, hs_r, hcan₀⟩
    have hs₀_sz : Term.size s₀ ≤ n + 1 := by
      rw [← rename_size hs_r]; exact hsize
    have hsmineq : smtMin s₀ ≈ᵣ smtMin s :=
      rename_symm (rename_smtMin hs_r)
    by_cases h_small : Term.size s₀ < n + 1
    · -- size < n+1: use IH and StepR rename bridging
      have hle_n : Term.size s₀ ≤ n := by omega
      rcases ih s₀ hle_n with ⟨s'', h_rename, hcan'', hreach_s'', hsmteq_s''⟩
      have hpath : StepStarR (R S (n + 1)) s₀ (smtMin s₀) :=
        (Relation.ReflTransGen.single (StepR.rename h_rename)).trans
          ((StepStarR.lift (R_subset (Nat.le_succ _)) hreach_s'').trans
            (Relation.ReflTransGen.single (StepR.rename hsmteq_s'')))
      exact ⟨s₀, hs_r, hcan₀, hpath, hsmineq⟩
    · -- size = n+1
      have hsz_eq : Term.size s₀ = n + 1 := by omega
      match s₀ with
      | .node f args =>
      have harg_sz : ∀ i, Term.size (args i) ≤ n := by
        intro i; have hlt := Term.size_arg_lt f args i; omega
      have harg_ih : ∀ i, ∃ ai', (args i) ≈ᵣ ai' ∧ Canonical ai' ∧
          StepStarR (R S n) ai' (smtMin ai') ∧ smtMin ai' ≈ᵣ smtMin (args i) :=
        fun i => ih (args i) (harg_sz i)
      by_cases h_enum : (Term.node f args) ∈
          termsFromIrreducibleRenamings S (I S n) (n + 1)
      · -- In enumeration → algorithm handles directly
        have hpath := enum_handles n (Term.node f args) hsz_eq hcan₀ h_enum ih
        exact ⟨Term.node f args, hs_r, hcan₀, hpath, hsmineq⟩
      · -- s₀ NOT in enumeration → has subterm not in I n
        -- Build canonical-subterms node tc
        let ac : Fin (S.arity f) → Term S := fun i => (harg_ih i).choose
        have h_ac_ren : ∀ i, (args i) ≈ᵣ ac i := fun i => (harg_ih i).choose_spec.1
        have h_ac_can : ∀ i, Canonical (ac i) := fun i => (harg_ih i).choose_spec.2.1
        have h_ac_reach : ∀ i, StepStarR (R S n) (ac i) (smtMin (ac i)) :=
          fun i => (harg_ih i).choose_spec.2.2.1
        let tc := Term.node f ac
        have hcan_tc : Canonical tc := canonical_node h_ac_can
        have h_ren_tc : (Term.node f args) ≈ᵣ tc := rename_congr h_ac_ren
        have hsz_tc : Term.size tc = n + 1 := by
          rw [← rename_size h_ren_tc, hsz_eq]
        by_cases h_enum_tc : tc ∈
            termsFromIrreducibleRenamings S (I S n) (n + 1)
        · -- tc in enumeration → algorithm handles tc → compose paths
          have hpath_tc := enum_handles n tc hsz_tc hcan_tc h_enum_tc ih
          have hpath : StepStarR (R S (n + 1)) (Term.node f args)
              (smtMin (Term.node f args)) :=
            (Relation.ReflTransGen.single (StepR.rename h_ren_tc)).trans
              (hpath_tc.trans
                (Relation.ReflTransGen.single
                  (StepR.rename (rename_symm (rename_smtMin h_ren_tc)))))
          exact ⟨Term.node f args, hs_r, hcan₀, hpath, hsmineq⟩
        · -- tc ALSO not in enumeration.
          -- For each ac i: smtMin(ac i) minimal → canonical c_i ∈ I n.
          -- ac i →* c_i via StepStarR.  Build u = node f c_vec ∈ enumeration.
          have h_ci : ∀ i, ∃ c_i, StepStarR (R S n) (ac i) c_i ∧
              Canonical c_i ∧ c_i ∈ I S n ∧ smtMin (ac i) ≈ᵣ c_i := by
            intro i
            have hm_min : smtMin (smtMin (ac i)) = smtMin (ac i) := smtMin_idem _
            have hm_sz : Term.size (smtMin (ac i)) ≤ n :=
              le_trans (smtMin_size _) (by
                rw [← rename_size (h_ac_ren i)]; exact harg_sz i)
            rcases minimal_has_canonical_in_I (smtMin (ac i)) hm_min hm_sz with
              ⟨c_i, h_ren, hcan_ci, _, hI⟩
            have hpath : StepStarR (R S n) (ac i) c_i :=
              (h_ac_reach i).trans (Relation.ReflTransGen.single (StepR.rename h_ren))
            exact ⟨c_i, hpath, hcan_ci, hI, h_ren⟩
          choose c_vec hpath_ci hcan_cvec hren_ci_and_I using h_ci
          have hcvec_in_I : ∀ i, c_vec i ∈ I S n := fun i => (hren_ci_and_I i).1
          have hren_ci : ∀ i, smtMin (ac i) ≈ᵣ c_vec i := fun i => (hren_ci_and_I i).2
          let u := Term.node f c_vec
          have hcan_u : Canonical u := canonical_node hcan_cvec
          -- tc →* u via StepStarR.ctx on each position (Finset iteration)
          let go (s : Finset (Fin (S.arity f))) : Term S :=
            Term.node f (fun i => if i ∈ s then c_vec i else ac i)
          have hgo_empty : StepStarR (R S (n + 1)) tc (go ∅) := by
            dsimp [go, tc]; exact Relation.ReflTransGen.refl
          have hgo_step (s : Finset (Fin (S.arity f))) (i : Fin (S.arity f))
              (hi : i ∉ s) : StepStarR (R S (n + 1)) (go s) (go (insert i s)) := by
            have h_reach : StepStarR (R S (n + 1)) (ac i) (c_vec i) :=
              StepStarR.lift (R_subset (Nat.le_succ _)) (hpath_ci i)
            let args_s := fun j : Fin (S.arity f) => if j ∈ s then c_vec j else ac j
            have h_as_i : args_s i = ac i := by simp [args_s, hi]
            have h_reach_at_i : StepStarR (R S (n + 1)) (args_s i) (c_vec i) := by
              rw [h_as_i]; exact h_reach
            have h_ctx := StepStarR.ctx (h := h_reach_at_i)
            have h_target : (Term.node f (fun j => if j = i then c_vec i else args_s j)) =
                go (insert i s) := by
              dsimp [go, args_s]; congr; ext j
              by_cases hj : j = i
              · subst j; simp [hi]
              · simp [hj, Finset.mem_insert]
            have h_source : Term.node f args_s = go s := by dsimp [go, args_s]
            rw [h_source, h_target] at h_ctx; exact h_ctx
          have h_tc_u : StepStarR (R S (n + 1)) tc (go Finset.univ) := by
            refine Finset.induction_on (Finset.univ : Finset (Fin (S.arity f)))
              hgo_empty (fun i s hi ih => ih.trans (hgo_step s i hi))
          have h_go_univ : go Finset.univ = u := by
            dsimp [go, u]; congr; ext i; simp
          have h_tc_u' : StepStarR (R S (n + 1)) tc u := by
            rwa [h_go_univ] at h_tc_u
          -- smtMin s₀ ≈ᵣ smtMin u (via canonical_equiv on subterms)
          have h_smt_rel : smtMin (Term.node f args) ≈ᵣ smtMin u := by
            have h1 : smtMin (Term.node f args) ≈ᵣ smtMin tc := rename_smtMin h_ren_tc
            have h_equiv_tc_u : tc ≈ₜ u := by
              have h_sub : ∀ i, (ac i) ≈ₜ (c_vec i) := by
                intro i
                have h_ac_smt : (ac i) ≈ₜ smtMin (ac i) := smtMin_equiv_symm _
                have h_smt_ci : smtMin (ac i) ≈ₜ c_vec i := canonical_equiv (hcan_cvec i) (hren_ci i)
                exact equiv_trans h_ac_smt h_smt_ci
              exact equiv_congr h_sub
            have h_eq : smtMin tc = smtMin u := smtMin_resp h_equiv_tc_u
            rw [h_eq] at h1; exact h1
          -- u has subterms in I n.  Either size u < n+1 (use IH) or = n+1 (use enumeration).
          by_cases h_small_u : Term.size u < n + 1
          · have hle_n : Term.size u ≤ n := by omega
            rcases ih u hle_n with ⟨w, h_ren_w, hcan_w, hreach_w, hsmteq_w⟩
            have hpath : StepStarR (R S (n + 1)) (Term.node f args)
                (smtMin (Term.node f args)) :=
              (Relation.ReflTransGen.single (StepR.rename h_ren_tc)).trans
                (h_tc_u'.trans
                  ((Relation.ReflTransGen.single (StepR.rename h_ren_w)).trans
                    ((StepStarR.lift (R_subset (Nat.le_succ _)) hreach_w).trans
                      (Relation.ReflTransGen.single
                        (StepR.rename (rename_trans hsmteq_w
                          (rename_symm h_smt_rel)))))))
            exact ⟨Term.node f args, hs_r, hcan₀, hpath, hsmineq⟩
          · -- size u = n+1: u is in the enumeration
            have hsz_u : Term.size u = n + 1 := by
              have hsz_u_le : Term.size u ≤ n + 1 := by
                have h_sz_each : ∀ i, Term.size (c_vec i) ≤ Term.size (ac i) := by
                  intro i
                  have hsz_smt : Term.size (smtMin (ac i)) ≤ Term.size (ac i) := smtMin_size _
                  have hsz_ci : Term.size (c_vec i) = Term.size (smtMin (ac i)) :=
                    (rename_size (hren_ci i)).symm
                  omega
                have hsum : (∑ j : Fin (S.arity f), Term.size (c_vec j)) ≤
                            (∑ j : Fin (S.arity f), Term.size (ac j)) :=
                  Finset.sum_le_sum (fun j _ => h_sz_each j)
                have hsum_ac : (∑ j : Fin (S.arity f), Term.size (ac j)) = n := by
                  unfold Term.size at hsz_tc; omega
                dsimp [u]; unfold Term.size; omega
              omega
            have h_u_irr : u ∈ termsFromIrreducible S (I S n) (n + 1) := by
              rw [mem_termsFromIrreducible]; refine ⟨hsz_u, ?_⟩
              intro f' args' heq'
              have hf : f' = f := by injection heq'
              have ha : HEq args' c_vec := by injection heq'
              cases hf
              have ha_eq : args' = c_vec := eq_of_heq ha
              rw [ha_eq]
              exact hcvec_in_I
            have h_u_enum : u ∈ termsFromIrreducibleRenamings S (I S n) (n + 1) := by
              rw [mem_termsFromIrreducibleRenamings]
              exact ⟨hsz_u, u, h_u_irr, rename_refl _⟩
            have hpath_u := enum_handles n u hsz_u hcan_u h_u_enum ih
            have hpath : StepStarR (R S (n + 1)) (Term.node f args)
                (smtMin (Term.node f args)) :=
              (Relation.ReflTransGen.single (StepR.rename h_ren_tc)).trans
                (h_tc_u'.trans (hpath_u.trans
                  (Relation.ReflTransGen.single
                    (StepR.rename (rename_symm h_smt_rel)))))
            exact ⟨Term.node f args, hs_r, hcan₀, hpath, hsmineq⟩

/-! ## Ground-completeness up to renaming -/
theorem ground_complete_up_to_rename (n : Nat) {s t : Term S}
    (hs : Term.size s ≤ n) (ht : Term.size t ≤ n) (hst : s ≈ₜ t) :
    ∃ s' t', (s ≈ᵣ s') ∧ (t ≈ᵣ t') ∧
      StepStarR (R S n) s' (smtMin s') ∧
      StepStarR (R S n) t' (smtMin t') ∧
      smtMin s' ≈ᵣ smtMin t' := by
  rcases reaches_smtMin_up_to_rename n s hs with ⟨s', hs_r, _, hreach_s, hsmt⟩
  rcases reaches_smtMin_up_to_rename n t ht with ⟨t', ht_r, _, hreach_t, tsmt⟩
  have h_eq : smtMin s = smtMin t := smtMin_resp (s := s) (t := t) hst
  have hsmeq : smtMin s ≈ᵣ smtMin t := h_eq ▸ rename_refl _
  have hst_eq : smtMin t ≈ᵣ smtMin t' := rename_symm tsmt
  have hsmt' : smtMin s' ≈ᵣ smtMin t' :=
    rename_trans (rename_trans hsmt hsmeq) hst_eq
  exact ⟨s', t', hs_r, ht_r, hreach_s, hreach_t, hsmt'⟩

end EnumRules
