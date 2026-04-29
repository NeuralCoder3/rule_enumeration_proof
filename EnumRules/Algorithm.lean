import Mathlib.Data.Finset.Basic
import EnumRules.Rewrite

open scoped Classical

/-
# The enumeration algorithm

We build up the rule set `R n` and the irreducible set `I n` by processing
sizes `1, 2, …, n` in order.

At size `k`, we only enumerate terms built from irreducible subterms
(terms already found to be in normal form at smaller sizes). For each such
term `l`:
- If `l` simplifies with rules from smaller sizes (strict size decrease),
  we discard it — it is already covered.
- Otherwise we call SMT to obtain `smtMin l`.
  - If `smtMin l = l`, we add `l` to the irreducible set `I`.
  - If `smtMin l ≠ l`, we add the rule `(l, smtMin l)` to `R`.

Any term that contains a reducible subterm can be reduced by existing rules,
so restricting the enumeration to irreducible subterms does not lose
completeness.
-/

namespace EnumRules

variable {S : Signature}

/-- Enumeration of all terms of a given size. -/
opaque termsOfSize (S : Signature) : Nat → Finset (Term S)

/-- Specification of `termsOfSize`: it is exactly the set of terms of that size. -/
axiom mem_termsOfSize {S : Signature} {n : Nat} {t : Term S} :
    t ∈ termsOfSize S n ↔ Term.size t = n

/-- Enumeration of terms of size `n` whose direct subterms all belong to
the given set `subterms`. This is the restricted enumeration that only
builds from irreducible subterms. -/
opaque termsFromIrreducible (S : Signature) (subterms : Finset (Term S)) (n : Nat) :
    Finset (Term S)

/-- Specification of `termsFromIrreducible`. -/
axiom mem_termsFromIrreducible {S : Signature} {subterms : Finset (Term S)} {n : Nat}
    {t : Term S} :
    t ∈ termsFromIrreducible S subterms n ↔
      Term.size t = n ∧
      ∀ (f : S.σ) (args : Fin (S.arity f) → Term S),
        Term.node f args = t → ∀ i, args i ∈ subterms

/-- If a term is not built from the given set, it has a subterm outside that set. -/
theorem not_mem_termsFromIrreducible {S : Signature} {I : Finset (Term S)} {n : Nat}
    {t : Term S} (hsize : Term.size t = n)
    (hnot : t ∉ termsFromIrreducible S I n) :
    ∃ (f : S.σ) (args : Fin (S.arity f) → Term S) (i : Fin (S.arity f)),
      Term.node f args = t ∧ args i ∉ I := by
  rw [mem_termsFromIrreducible] at hnot
  by_cases hsize_eq : Term.size t = n
  · -- size matches, so the subterm condition must fail
    have hforall : ¬ ∀ (f : S.σ) (args : Fin (S.arity f) → Term S),
        Term.node f args = t → ∀ i, args i ∈ I := by
      intro h; apply hnot; exact ⟨hsize_eq, h⟩
    push Not at hforall
    rcases hforall with ⟨f, args, heq, i, hi⟩
    exact ⟨f, args, i, heq, hi⟩
  · exact absurd hsize hsize_eq

mutual
  /-- The rule set after processing all sizes `≤ n`. -/
  noncomputable def R (S : Signature) : Nat → RuleSet S
    | 0     => ∅
    | n + 1 => R S n ∪ (
        (termsFromIrreducible S (I S n) (n + 1)).filter (fun l =>
          ¬ simplifiesWith (R S n) l ∧ smtMin l ≠ l)
          |>.image (fun l => (l, smtMin l)))

  /-- The irreducible (already-minimal) set after processing all sizes `≤ n`. -/
  noncomputable def I (S : Signature) : Nat → Finset (Term S)
    | 0     => ∅
    | n + 1 => I S n ∪ (
        (termsFromIrreducible S (I S n) (n + 1)).filter (fun l =>
          ¬ simplifiesWith (R S n) l ∧ smtMin l = l))
end

/-- Rules contributed at size `n`: terms of size `n`, built from irreducible
subterms, that do not simplify and are not already in normal form. -/
noncomputable def newRulesAt (S : Signature) (n : Nat) : RuleSet S :=
    (termsFromIrreducible S (I S (n - 1)) n).filter (fun l =>
      ¬ simplifiesWith (R S (n - 1)) l ∧ smtMin l ≠ l)
      |>.image (fun l => (l, smtMin l))

/-- `R` is monotone: rules from smaller sizes are included at larger sizes. -/
theorem R_subset {S : Signature} {m n : Nat} (h : m ≤ n) : R S m ⊆ R S n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih =>
    intro x hx
    rw [R]
    exact Finset.mem_union_left _ (ih hx)

/-- `I` is monotone: irreducible terms from smaller sizes persist. -/
theorem I_subset {S : Signature} {m n : Nat} (h : m ≤ n) : I S m ⊆ I S n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih =>
    intro x hx
    rw [I]
    exact Finset.mem_union_left _ (ih hx)

/-- Decompose `R S (n+1)` into `R S n` and the new rules at size `n+1`. -/
theorem R_succ_eq {S : Signature} (n : Nat) :
    R S (n + 1) = R S n ∪ newRulesAt S (n + 1) := by
  ext x
  simp [R, newRulesAt, Finset.mem_union, Finset.mem_image, Finset.mem_filter]

/-- Characterization of membership in `R n`. -/
theorem mem_R {S : Signature} {n : Nat} {l r : Term S} :
    (l, r) ∈ R S n ↔
      ∃ m, m ≤ n ∧ Term.size l = m ∧ l ∈ termsFromIrreducible S (I S (m - 1)) m ∧
      r = smtMin l ∧ l ≠ r ∧ ¬ simplifiesWith (R S (m - 1)) l := by
  induction n with
  | zero =>
    rw [R]
    have hRHS : ¬ ∃ m, m ≤ (0 : Nat) ∧ Term.size l = m ∧
        l ∈ termsFromIrreducible S (I S (m - 1)) m ∧
        r = smtMin l ∧ l ≠ r ∧ ¬ simplifiesWith (R S (m - 1)) l := by
      rintro ⟨m, hm, hsize, _, _, _, _⟩
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst hm0
      have hpos : 1 ≤ Term.size l := Term.size_pos l
      omega
    constructor
    · intro h; simp at h
    · intro h; exact absurd h hRHS
  | succ n ih =>
    rw [R_succ_eq, Finset.mem_union]
    constructor
    · rintro (hRprev | hNew)
      · rcases ih.mp hRprev with ⟨m, hm, hsize, hen, hr, hne, hnsp⟩
        exact ⟨m, Nat.le_succ_of_le hm, hsize, hen, hr, hne, hnsp⟩
      · -- In new rules at size n+1
        dsimp [newRulesAt, I] at hNew
        rcases Finset.mem_image.1 hNew with ⟨l', hfilter, heq⟩
        rcases Finset.mem_filter.1 hfilter with ⟨hmem_l', ⟨hnsp, hne'⟩⟩
        have hl_eq : l' = l := congrArg Prod.fst heq
        have hr_eq : smtMin l' = r := congrArg Prod.snd heq
        rw [hl_eq] at hmem_l' hne' hr_eq hnsp
        have hne_lr : l ≠ r := by
          rw [← hr_eq]
          exact Ne.symm hne'
        refine ⟨n + 1, le_refl _, (mem_termsFromIrreducible.mp hmem_l').1, hmem_l', hr_eq.symm, hne_lr, hnsp⟩
    · rintro ⟨m, hm, hsize, hen, hr, hne, hnsp⟩
      rcases Nat.lt_or_eq_of_le hm with (hlt | heq)
      · left
        apply ih.mpr
        exact ⟨m, Nat.le_of_lt_succ hlt, hsize, hen, hr, hne, hnsp⟩
      · subst heq
        have hmem_l : l ∈ termsFromIrreducible S (I S n) (n + 1) := hen
        have hne_symm : smtMin l ≠ l := fun h => hne (h.symm.trans hr.symm)
        right
        dsimp [newRulesAt, I]
        refine Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨hmem_l, hnsp, hne_symm⟩, ?_⟩
        simp [hr]

/-- Every rule `(l, r)` in `R n` satisfies `r ≈ₜ l`. -/
theorem rule_equiv_symm {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : r ≈ₜ l := by
  rcases mem_R.mp h with ⟨_, _, _, _, hr, _, _⟩
  subst hr
  exact smtMin_equiv l

/-- Every rule `(l, r)` in `R n` satisfies `l ≈ₜ r`. -/
theorem rule_equiv {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : l ≈ₜ r :=
  equiv_symm (rule_equiv_symm h)

/-- Every rule is KBO-decreasing. -/
theorem rule_kbo {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : r ≺ₖ l := by
  rcases mem_R.mp h with ⟨_, _, _, _, hr, hne, _⟩
  subst hr
  rcases smtMin_le l with heq | hlt
  · exact (hne heq.symm).elim
  · exact hlt

/-- Every rule does not increase size. -/
theorem rule_size {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : Term.size r ≤ Term.size l := by
  rcases mem_R.mp h with ⟨_, _, _, _, hr, _, _⟩
  subst hr
  exact smtMin_size l

/-- If a node is minimal, all its subterms are also minimal. -/
theorem subterm_of_minimal_is_minimal {S : Signature} {f : S.σ}
    {args : Fin (S.arity f) → Term S} (hmin : smtMin (Term.node f args) = Term.node f args)
    (i : Fin (S.arity f)) : smtMin (args i) = args i := by
  by_contra hne
  have hlt : smtMin (args i) ≺ₖ args i := by
    rcases smtMin_le (args i) with (heq | hlt)
    · exact (hne heq).elim
    · exact hlt
  -- Build args' replacing position i with smtMin (args i)
  let args' : Fin (S.arity f) → Term S :=
    fun j => if j = i then smtMin (args i) else args j
  have hrest : ∀ j, j ≠ i → args j = args' j := by
    intro j hj; simp [args', hj]
  have hi_eq : args' i = smtMin (args i) := by simp [args']
  -- By kbo_mono_ctx: node f args' ≺ₖ node f args
  have hkbo_node : (Term.node f args') ≺ₖ (Term.node f args) :=
    kbo_mono_ctx (as := args) (bs := args') (i := i) hrest (by
      dsimp [args']; simpa using hlt)
  -- Also node f args' ≈ node f args (by congruence of equivalence)
  have hequiv_node : smtMin (args i) ≈ₜ args i := smtMin_equiv (args i)
  have hequiv_args : ∀ j, args' j ≈ₜ args j := by
    intro j
    dsimp [args']
    split_ifs with h
    · subst h; exact hequiv_node
    · exact equiv_refl _
  have hequiv : (Term.node f args') ≈ₜ (Term.node f args) := equiv_congr hequiv_args
  -- node f args' is KBO-smaller and equivalent, contradicting minimality
  have h_contra := smtMin_min (t := Term.node f args) (u := Term.node f args') hequiv
  apply h_contra
  -- h_contra expects ¬ (node f args' ≺ₖ smtMin (node f args)) = ¬ (node f args' ≺ₖ node f args)
  rw [hmin]
  exact hkbo_node

/-- `I` contains every minimal term whose size is bounded by `n`. -/
theorem I_contains_minimal {S : Signature} {n : Nat} {t : Term S}
    (hsize : Term.size t ≤ n) (hmin : smtMin t = t) : t ∈ I S n := by
  revert t
  induction n with
  | zero =>
    intro t hsize hmin
    have hsz : Term.size t = 0 := Nat.eq_zero_of_le_zero hsize
    have hpos : 1 ≤ Term.size t := Term.size_pos t
    omega
  | succ n ih =>
    intro t hsize hmin
    rw [I]
    rcases Nat.lt_or_eq_of_le hsize with (hlt | heq)
    · have hsize_n : Term.size t ≤ n := by omega
      have hmem_n : t ∈ I S n := ih (t := t) hsize_n hmin
      simp [hmem_n]
    · -- size t = n+1
      have hmem_irr : t ∈ termsFromIrreducible S (I S n) (n + 1) := by
        rw [mem_termsFromIrreducible]
        constructor
        · exact heq
        · intro f args heq_t i
          subst heq_t
          have hsize_arg : Term.size (args i) ≤ n := by
            have h := Term.size_arg_lt f args i
            rw [heq] at h
            omega
          have hmin_arg : smtMin (args i) = args i :=
            subterm_of_minimal_is_minimal hmin i
          exact ih (t := args i) hsize_arg hmin_arg
      have hnsp : ¬ simplifiesWith (R S n) t := by
        intro hsp
        rcases simplifiesWith.kbo_lt (fun hlr => rule_kbo hlr) hsp with
          ⟨u, htu, _, hlt_u⟩
        have hequiv_tu : t ≈ₜ u :=
          StepStar.equiv_of (fun hlr => rule_equiv hlr) htu
        have hcontra := smtMin_min (t := t) (u := u) (equiv_symm hequiv_tu)
        rw [hmin] at hcontra
        exact hcontra hlt_u
      have hmem_filter : t ∈ {l ∈ termsFromIrreducible S (I S n) (n + 1) | ¬ simplifiesWith (R S n) l ∧ smtMin l = l} :=
        Finset.mem_filter.mpr ⟨hmem_irr, ⟨hnsp, hmin⟩⟩
      simp [hmem_filter]

/-- If `l` has the right size, is not already minimal, does not simplify,
and is built from irreducible subterms, then `(l, smtMin l) ∈ R n`. -/
theorem rule_mem_of_size {S : Signature} {n : Nat} {l : Term S}
    (hsize : Term.size l ≤ n)
    (hen : l ∈ termsFromIrreducible S (I S (Term.size l - 1)) (Term.size l))
    (hne : smtMin l ≠ l)
    (hnsp : ¬ simplifiesWith (R S (Term.size l - 1)) l) :
    (l, smtMin l) ∈ R S n :=
  mem_R.mpr ⟨Term.size l, hsize, rfl, hen, rfl, fun h => hne h.symm, hnsp⟩

/-- If `l` has size `≤ n` and `(l, smtMin l) ∉ R n`, then either `l` is already
minimal, or it simplifies with earlier rules, or it is not built from
irreducible subterms (so it has a reducible subterm). -/
theorem not_mem_R_of_size {S : Signature} {n : Nat} {l : Term S}
    (hsize : Term.size l ≤ n) (hnotmem : (l, smtMin l) ∉ R S n) :
    smtMin l = l ∨ simplifiesWith (R S (Term.size l - 1)) l ∨
    l ∉ termsFromIrreducible S (I S (Term.size l - 1)) (Term.size l) := by
  by_cases hne : smtMin l = l
  · exact Or.inl hne
  · by_cases hnsp : simplifiesWith (R S (Term.size l - 1)) l
    · exact Or.inr (Or.inl hnsp)
    · by_cases hen : l ∈ termsFromIrreducible S (I S (Term.size l - 1)) (Term.size l)
      · exfalso
        apply hnotmem
        exact rule_mem_of_size hsize hen hne hnsp
      · exact Or.inr (Or.inr hen)

end EnumRules
