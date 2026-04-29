import Mathlib.Data.Finset.Basic
import EnumRules.Rewrite

open scoped Classical

/-
# The enumeration algorithm

We axiomatize a term-enumerator `termsOfSize` and build up the rule set
`R n` by processing sizes `1, 2, …, n` in order. For each term `l` of size
`k`, we first check whether it simplifies with rules from smaller sizes;
only if it does not simplify do we call SMT to obtain `smtMin l` and
possibly add the rule `(l, smtMin l)`.
-/

namespace EnumRules

variable {S : Signature}

/-- Enumeration of all terms of a given size. -/
opaque termsOfSize (S : Signature) : Nat → Finset (Term S)

/-- Specification of `termsOfSize`: it is exactly the set of terms of that size. -/
axiom mem_termsOfSize {S : Signature} {n : Nat} {t : Term S} :
    t ∈ termsOfSize S n ↔ Term.size t = n

/-- The rule set after processing all sizes `≤ n`. At each size, we first
simplify the term using previous rules; only if no simplification to a smaller
size is possible do we consult the SMT oracle. -/
noncomputable def R (S : Signature) : Nat → RuleSet S
  | 0     => ∅
  | n + 1 => R S n ∪ (
      (termsOfSize S (n + 1)).filter (fun l =>
        ¬ simplifiesWith (R S n) l ∧ smtMin l ≠ l)
        |>.image (fun l => (l, smtMin l)))

/-- Rules contributed at size `n`: terms of size `n` that do not simplify
via earlier rules and are not already in normal form. -/
noncomputable def newRulesAt (S : Signature) (n : Nat) : RuleSet S :=
    (termsOfSize S n).filter (fun l =>
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

/-- Decompose `R S (n+1)` into `R S n` and the new rules at size `n+1`. -/
theorem R_succ_eq {S : Signature} (n : Nat) :
    R S (n + 1) = R S n ∪ newRulesAt S (n + 1) := by
  ext x
  simp [R, newRulesAt, Finset.mem_union, Finset.mem_image, Finset.mem_filter]

/-- Characterization of membership in `R n`. -/
theorem mem_R {S : Signature} {n : Nat} {l r : Term S} :
    (l, r) ∈ R S n ↔
      ∃ m, m ≤ n ∧ Term.size l = m ∧ r = smtMin l ∧ l ≠ r ∧
      ¬ simplifiesWith (R S (m - 1)) l := by
  induction n with
  | zero =>
    rw [R]
    have hRHS : ¬ ∃ m, m ≤ (0 : Nat) ∧ Term.size l = m ∧ r = smtMin l ∧ l ≠ r ∧
      ¬ simplifiesWith (R S (m - 1)) l := by
      rintro ⟨m, hm, hsize, _, _, _⟩
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
      · rcases ih.mp hRprev with ⟨m, hm, hsize, hr, hne, hnsp⟩
        exact ⟨m, Nat.le_succ_of_le hm, hsize, hr, hne, hnsp⟩
      · -- In new rules at size n+1: expand via mem_image and mem_filter
        rw [newRulesAt] at hNew
        rcases Finset.mem_image.1 hNew with ⟨l', hfilter, heq⟩
        rcases Finset.mem_filter.1 hfilter with ⟨hl'size, ⟨hnsp, hne'⟩⟩
        have hl_eq : l' = l := congrArg Prod.fst heq
        have hr_eq : smtMin l' = r := congrArg Prod.snd heq
        rw [hl_eq] at hl'size hne' hr_eq hnsp
        have hne_lr : l ≠ r := by
          rw [← hr_eq]
          exact Ne.symm hne'
        refine ⟨n + 1, le_refl _, (mem_termsOfSize.mp hl'size), hr_eq.symm, hne_lr, hnsp⟩
    · rintro ⟨m, hm, hsize, hr, hne, hnsp⟩
      rcases Nat.lt_or_eq_of_le hm with (hlt | heq)
      · left
        apply ih.mpr
        exact ⟨m, Nat.le_of_lt_succ hlt, hsize, hr, hne, hnsp⟩
      · subst heq
        have hmem : l ∈ termsOfSize S (n + 1) := mem_termsOfSize.mpr hsize
        have hne_symm : smtMin l ≠ l := fun h => hne (h.symm.trans hr.symm)
        right
        rw [newRulesAt]
        refine Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨hmem, hnsp, hne_symm⟩, by simp [hr]⟩

/-- Every rule `(l, r)` in `R n` satisfies `r ≈ₜ l`. -/
theorem rule_equiv_symm {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : r ≈ₜ l := by
  rcases mem_R.mp h with ⟨_, _, _, hr, _, _⟩
  subst hr
  exact smtMin_equiv l

/-- Every rule `(l, r)` in `R n` satisfies `l ≈ₜ r`. -/
theorem rule_equiv {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : l ≈ₜ r :=
  equiv_symm (rule_equiv_symm h)

/-- Every rule is KBO-decreasing. -/
theorem rule_kbo {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : r ≺ₖ l := by
  rcases mem_R.mp h with ⟨_, _, _, hr, hne, _⟩
  subst hr
  rcases smtMin_le l with heq | hlt
  · exact (hne heq.symm).elim
  · exact hlt

/-- Every rule does not increase size. -/
theorem rule_size {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : Term.size r ≤ Term.size l := by
  rcases mem_R.mp h with ⟨_, _, _, hr, _, _⟩
  subst hr
  exact smtMin_size l

/-- If `l` has size `≤ n`, is not already minimal, and does not simplify with
earlier rules, then `(l, smtMin l) ∈ R n`. -/
theorem rule_mem_of_size {S : Signature} {n : Nat} {l : Term S}
    (hsize : Term.size l ≤ n) (hne : smtMin l ≠ l)
    (hnsp : ¬ simplifiesWith (R S (Term.size l - 1)) l) :
    (l, smtMin l) ∈ R S n :=
  mem_R.mpr ⟨Term.size l, hsize, rfl, rfl, fun h => hne h.symm, hnsp⟩

/-- If `l` has size `≤ n` and `(l, smtMin l) ∉ R n`, then either `l` is already
minimal or it simplifies with earlier rules. -/
theorem not_mem_R_of_size {S : Signature} {n : Nat} {l : Term S}
    (hsize : Term.size l ≤ n) (hnotmem : (l, smtMin l) ∉ R S n) :
    smtMin l = l ∨ simplifiesWith (R S (Term.size l - 1)) l := by
  by_cases hne : smtMin l = l
  · exact Or.inl hne
  · by_cases hnsp : simplifiesWith (R S (Term.size l - 1)) l
    · exact Or.inr hnsp
    · exfalso
      apply hnotmem
      exact rule_mem_of_size hsize hne hnsp

end EnumRules
