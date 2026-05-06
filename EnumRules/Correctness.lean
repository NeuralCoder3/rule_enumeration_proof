import EnumRules.Algorithm

open scoped Classical

/-
# Correctness

Three lemmas, by induction on the size bound `n`:

* `terminates`: `Step (R S n)` is well-founded.
* `minimal_in_I`: every `≈ₜ`-minimal term of size ≤ n is in `I S n`.
* `reaches_smtMin`: every term of size ≤ n rewrites to its `smtMin`
  via `StepStar (R S n)`.

The completeness theorem then follows from `smtMin_resp`: for any two
`≈ₜ`-equivalent terms, both rewrite to the *same* term `smtMin s = smtMin t`.

The proof uses no renaming relation: rule application is via
substitution (`Step.root σ`); the identity substitution `idSubst` covers
ground rule firing through `Step.root_id`.
-/

namespace EnumRules

variable {S : Signature}

/-! ## Termination -/

theorem terminates (n : Nat) :
    WellFounded (fun t s : Term S => Step (R S n) s t) := by
  apply Subrelation.wf (r := fun t s : Term S => t ≺ₖ s)
  · intro t s h; exact Step.kbo_of (fun hlr => rule_kbo hlr) h
  · exact InvImage.wf (f := id) kbo_wf

/-! ## Lifting subterm reductions to the whole term

Iteratively apply `StepStar.ctx` over a `Finset` of positions to rewrite
every argument of a node in turn. -/

theorem stepstar_node {R : RuleSet S} {f : S.σ}
    {args reduced : Fin (S.arity f) → Term S}
    (h : ∀ i, StepStar R (args i) (reduced i)) :
    StepStar R (Term.node f args) (Term.node f reduced) := by
  let go (s : Finset (Fin (S.arity f))) : Term S :=
    Term.node f (fun i => if i ∈ s then reduced i else args i)
  have hgo_step : ∀ (s : Finset (Fin (S.arity f))) (i : Fin (S.arity f)),
      i ∉ s → StepStar R (go s) (go (insert i s)) := by
    intro s i hi
    let as' := fun j : Fin (S.arity f) => if j ∈ s then reduced j else args j
    have h_as_i : as' i = args i := by simp [as', hi]
    have h_reach_at_i : StepStar R (as' i) (reduced i) := by
      rw [h_as_i]; exact h i
    have h_ctx := StepStar.ctx (h := h_reach_at_i)
    have h_target : (Term.node f (fun j => if j = i then reduced i else as' j)) =
        go (insert i s) := by
      dsimp [go, as']; congr; ext j
      by_cases hj : j = i
      · subst j; simp [hi]
      · simp [hj, Finset.mem_insert]
    have h_source : Term.node f as' = go s := by dsimp [go, as']
    rw [h_source, h_target] at h_ctx; exact h_ctx
  have h_init : StepStar R (Term.node f args) (go ∅) := by
    have h_eq : (fun i : Fin (S.arity f) => if i ∈ (∅ : Finset _) then reduced i else args i)
        = args := by funext i; simp
    show StepStar R (Term.node f args) (Term.node f _)
    rw [h_eq]
  have h_full : StepStar R (Term.node f args) (go Finset.univ) := by
    have hUniv : ∀ s : Finset (Fin (S.arity f)), StepStar R (go ∅) (go s) := by
      intro s
      refine Finset.induction_on s Relation.ReflTransGen.refl ?_
      intro i s' hi ih_s'
      exact ih_s'.trans (hgo_step s' i hi)
    exact h_init.trans (hUniv _)
  have h_eq : go Finset.univ = Term.node f reduced := by
    dsimp [go]; congr; funext i; simp
  rw [h_eq] at h_full; exact h_full

/-! ## Every minimal term is in I -/

theorem minimal_in_I (m : Term S) (hmin : smtMin m = m)
    (hsize : Term.size m ≤ n) : m ∈ I S n := by
  revert m
  induction n with
  | zero =>
    intro m _ hsize
    have : 1 ≤ Term.size m := Term.size_pos m; omega
  | succ n ih =>
    intro m hmin hsize
    rcases Nat.lt_or_eq_of_le hsize with hlt | heq
    · exact I_subset (Nat.le_succ _) (ih m hmin (Nat.le_of_lt_succ hlt))
    · match m, hmin with
      | .node f args, hmin =>
      have hsub_min : ∀ i, smtMin (args i) = args i :=
        subterm_of_minimal_is_minimal hmin
      have hsub_sz : ∀ i, Term.size (args i) ≤ n := by
        intro i; have := Term.size_arg_lt f args i; omega
      have hsub_in_I : ∀ i, args i ∈ I S n :=
        fun i => ih (args i) (hsub_min i) (hsub_sz i)
      have h_enum : Term.node f args ∈ termsFromIrreducible S (I S n) (n + 1) := by
        rw [mem_termsFromIrreducible]; refine ⟨heq, ?_⟩
        intro f' args' heq'
        have hf : f' = f := by injection heq'
        have ha : HEq args' args := by injection heq'
        cases hf
        have ha_eq : args' = args := eq_of_heq ha
        rw [ha_eq]; exact hsub_in_I
      have h_not_simp : ¬ simplifiesWith (R S n) (Term.node f args) := by
        intro hsp
        rcases simplifiesWith.kbo_lt (fun hlr => rule_kbo hlr) hsp with
          ⟨u, htu, _, hlt_u⟩
        have hequiv : Term.node f args ≈ₜ u :=
          StepStar.equiv_of (fun hlr => rule_equiv hlr) htu
        have := smtMin_min (t := Term.node f args) (u := u) (equiv_symm hequiv)
        rw [hmin] at this; exact this hlt_u
      rw [I]
      exact Finset.mem_union_right _ <|
        Finset.mem_filter.mpr ⟨h_enum, h_not_simp, hmin⟩

/-! ## Every term reaches its `smtMin` -/

theorem reaches_smtMin (s : Term S) (hsize : Term.size s ≤ n) :
    StepStar (R S n) s (smtMin s) := by
  revert s
  induction n with
  | zero =>
    intro s hsize
    have : 1 ≤ Term.size s := Term.size_pos s; omega
  | succ n ih =>
    intro s hsize
    rcases Nat.lt_or_eq_of_le hsize with hlt | heq
    · exact StepStar.lift (R_subset (Nat.le_succ _)) (ih s (Nat.le_of_lt_succ hlt))
    · match s with
      | .node f args =>
      have hsub_sz : ∀ i, Term.size (args i) ≤ n := by
        intro i; have := Term.size_arg_lt f args i; omega
      -- Step 1: rewrite each subterm to its smtMin (using IH at n).
      have hsub_path : ∀ i, StepStar (R S (n + 1)) (args i) (smtMin (args i)) :=
        fun i => StepStar.lift (R_subset (Nat.le_succ _)) (ih (args i) (hsub_sz i))
      let s' : Term S := Term.node f (fun i => smtMin (args i))
      have hs_to_s' : StepStar (R S (n + 1)) (Term.node f args) s' :=
        stepstar_node hsub_path
      -- s' is ≈ₜ-equivalent to s, so smtMin s' = smtMin s.
      have h_s'_equiv : Term.node f args ≈ₜ s' := by
        dsimp [s']; exact equiv_congr (fun i => equiv_symm (smtMin_equiv (args i)))
      have h_smtMin_eq : smtMin s' = smtMin (Term.node f args) :=
        (smtMin_resp h_s'_equiv).symm
      -- Size bound on s' (via smtMin_size componentwise).
      have hs'_sz : Term.size s' ≤ n + 1 := by
        have hsub_le : ∀ i, Term.size (smtMin (args i)) ≤ Term.size (args i) :=
          fun i => smtMin_size (args i)
        have hsum : (∑ i : Fin (S.arity f), Term.size (smtMin (args i))) ≤
            (∑ i : Fin (S.arity f), Term.size (args i)) :=
          Finset.sum_le_sum (fun j _ => hsub_le j)
        dsimp [s', Term.size]
        unfold Term.size at heq; omega
      -- Step 2: finish by getting s' →* smtMin s'.
      -- Either s' has size ≤ n (use IH directly), or size = n+1 (use enumeration).
      by_cases h_lt : Term.size s' ≤ n
      · -- size s' ≤ n: IH gives s' →* smtMin s'.
        have hpath : StepStar (R S (n + 1)) s' (smtMin s') :=
          StepStar.lift (R_subset (Nat.le_succ _)) (ih s' h_lt)
        rw [h_smtMin_eq] at hpath
        exact hs_to_s'.trans hpath
      · -- size s' = n + 1 exactly.
        have hsz_eq : Term.size s' = n + 1 := by omega
        -- Each subterm of s' is smtMin-fixed (by smtMin_idem).
        have hsub_min : ∀ i, smtMin (smtMin (args i)) = smtMin (args i) :=
          fun i => smtMin_idem _
        -- Each subterm of s' has size ≤ n (since smtMin_size ≤ args i size ≤ n).
        have hsub_sz' : ∀ i, Term.size (smtMin (args i)) ≤ n :=
          fun i => le_trans (smtMin_size (args i)) (hsub_sz i)
        -- Each subterm is in I S n by `minimal_in_I`.
        have hsub_in_I : ∀ i, smtMin (args i) ∈ I S n :=
          fun i => minimal_in_I (smtMin (args i)) (hsub_min i) (hsub_sz' i)
        have h_enum : s' ∈ termsFromIrreducible S (I S n) (n + 1) := by
          rw [mem_termsFromIrreducible]; refine ⟨hsz_eq, ?_⟩
          intro f' args' heq'
          have hf : f' = f := by injection heq'
          have ha : HEq args' (fun i => smtMin (args i)) := by injection heq'
          cases hf
          have ha_eq : args' = (fun i => smtMin (args i)) := eq_of_heq ha
          rw [ha_eq]; exact hsub_in_I
        -- Three sub-cases on s': simplifies, minimal, or has a rule.
        by_cases h_simp : simplifiesWith (R S n) s'
        · -- simplifies → use simplifying reduct (size < n+1 ≤ n) and IH.
          rcases simplifiesWith.kbo_lt (fun hlr => rule_kbo hlr) h_simp with
            ⟨u, hsu, hsz_u, _⟩
          have hu_sz : Term.size u ≤ n := by omega
          have hpath_u : StepStar (R S (n + 1)) u (smtMin u) :=
            StepStar.lift (R_subset (Nat.le_succ _)) (ih u hu_sz)
          have h_u_equiv : s' ≈ₜ u :=
            StepStar.equiv_of (fun hlr => rule_equiv hlr) hsu
          have h_smt_u : smtMin u = smtMin s' := (smtMin_resp h_u_equiv).symm
          rw [h_smt_u, h_smtMin_eq] at hpath_u
          exact hs_to_s'.trans
            ((StepStar.lift (R_subset (Nat.le_succ _)) hsu).trans hpath_u)
        · -- doesn't simplify
          by_cases h_min : smtMin s' = s'
          · -- s' is its own smtMin → smtMin s = s'.
            have : smtMin (Term.node f args) = s' := by
              rw [← h_smtMin_eq]; exact h_min
            rw [this]; exact hs_to_s'
          · -- rule (s', smtMin s') ∈ R S (n + 1).
            have hmem : (s', smtMin s') ∈ R S (n + 1) :=
              mem_R.mpr ⟨n + 1, le_refl _, hsz_eq, h_enum, rfl,
                fun h => h_min h.symm, h_simp⟩
            have hstep : Step (R S (n + 1)) s' (smtMin s') := Step.root_id hmem
            have h_target : smtMin s' = smtMin (Term.node f args) := h_smtMin_eq
            rw [h_target] at hstep
            exact hs_to_s'.trans (Relation.ReflTransGen.single hstep)

/-! ## Completeness -/

/-- For any two `≈ₜ`-equivalent terms of size ≤ n, both rewrite (via
substitution-based steps) to the same term — namely the SMT-minimum of
their common `≈ₜ`-class. -/
theorem complete (n : Nat) {s t : Term S}
    (hs : Term.size s ≤ n) (ht : Term.size t ≤ n) (hst : s ≈ₜ t) :
    ∃ u, StepStar (R S n) s u ∧ StepStar (R S n) t u := by
  refine ⟨smtMin s, reaches_smtMin s hs, ?_⟩
  rw [smtMin_resp hst]
  exact reaches_smtMin t ht

end EnumRules
