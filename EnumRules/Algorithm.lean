import Mathlib.Data.Finset.Basic
import EnumRules.Rewrite

/-
# The enumeration algorithm

We axiomatize a term-enumerator `termsOfSize` and build up the rule set
`R n` by processing sizes `1, 2, …, n` in order. Each term `l` of size
`k ≤ n` either equals its SMT-minimal representative `smtMin l` (a
normal form) or contributes the rule `(l, smtMin l)` to `R n`.
-/

namespace EnumRules

variable {S : Signature}

/-- Enumeration of all terms of a given size. -/
opaque termsOfSize (S : Signature) : Nat → Finset (Term S)

/-- Specification of `termsOfSize`: it is exactly the set of terms of that size. -/
axiom mem_termsOfSize {S : Signature} {n : Nat} {t : Term S} :
    t ∈ termsOfSize S n ↔ Term.size t = n

/-- Rules contributed by a single size `n`. For each term `l` of size `n`
with `smtMin l ≠ l`, we add the pair `(l, smtMin l)`. -/
noncomputable def newRulesAt (S : Signature) (n : Nat) : RuleSet S :=
  (termsOfSize S n).filter (fun l => smtMin l ≠ l)
    |>.image (fun l => (l, smtMin l))

/-- The rule set after processing all sizes `≤ n`. -/
noncomputable def R (S : Signature) : Nat → RuleSet S
  | 0     => ∅
  | n + 1 => R S n ∪ newRulesAt S (n + 1)

/-- Characterization of membership in `R n`. -/
theorem mem_R {S : Signature} {n : Nat} {l r : Term S} :
    (l, r) ∈ R S n ↔
      ∃ m, m ≤ n ∧ Term.size l = m ∧ r = smtMin l ∧ l ≠ r := by
  induction n with
  | zero =>
    rw [R]
    have hRHS : ¬ ∃ m, m ≤ (0 : Nat) ∧ Term.size l = m ∧ r = smtMin l ∧ l ≠ r := by
      rintro ⟨m, hm, hsize, _, _⟩
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst hm0
      have hpos : 1 ≤ Term.size l := Term.size_pos l
      omega
    constructor
    · intro h; simp at h
    · intro h; exact absurd h hRHS
  | succ n ih =>
    constructor
    · intro h
      rw [R, Finset.mem_union] at h
      rcases h with (hR | hNew)
      · rcases ih.mp hR with ⟨m, hm, hsize, hr, hne⟩
        exact ⟨m, Nat.le_succ_of_le hm, hsize, hr, hne⟩
      · rw [newRulesAt, Finset.mem_image] at hNew
        rcases hNew with ⟨l', hl'filter, heq⟩
        rw [Finset.mem_filter] at hl'filter
        rcases hl'filter with ⟨hl'size, hne'⟩
        have heq_pair := Prod.mk.inj heq
        rcases heq_pair with ⟨hl, hr'⟩
        -- hl : l' = l, hr' : smtMin l' = r
        rw [hl] at hl'size hne' hr'
        -- hl'size : l ∈ termsOfSize S (n+1), hne' : smtMin l ≠ l, hr' : smtMin l = r
        have hne_lr : l ≠ r := by
          rw [← hr']
          exact Ne.symm hne'
        refine ⟨n + 1, le_refl _, (mem_termsOfSize.mp hl'size), hr'.symm, hne_lr⟩
    · rintro ⟨m, hm, hsize, hr, hne⟩
      rw [R, Finset.mem_union]
      rcases Nat.lt_or_eq_of_le hm with (hlt | heq)
      · left
        apply ih.mpr
        exact ⟨m, Nat.le_of_lt_succ hlt, hsize, hr, hne⟩
      · subst heq
        have hne_symm : smtMin l ≠ l := fun h => hne (by rw [← h, hr])
        right
        rw [newRulesAt, Finset.mem_image]
        refine ⟨l, ?_, by simp [hr]⟩
        rw [Finset.mem_filter]
        exact ⟨mem_termsOfSize.mpr hsize, hne_symm⟩

/-- Every rule `(l, r)` in `R n` satisfies `r ≈ₜ l`. -/
theorem rule_equiv_symm {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : r ≈ₜ l := by
  rcases mem_R.mp h with ⟨_, _, _, hr, _⟩
  subst hr
  exact smtMin_equiv l

/-- Every rule `(l, r)` in `R n` satisfies `l ≈ₜ r`. -/
theorem rule_equiv {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : l ≈ₜ r :=
  equiv_symm (rule_equiv_symm h)

/-- Every rule is KBO-decreasing. -/
theorem rule_kbo {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : r ≺ₖ l := by
  rcases mem_R.mp h with ⟨_, _, _, hr, hne⟩
  subst hr
  rcases smtMin_le l with heq | hlt
  · exact (hne heq.symm).elim
  · exact hlt

/-- Every rule does not increase size. -/
theorem rule_size {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : Term.size r ≤ Term.size l := by
  rcases mem_R.mp h with ⟨_, _, _, hr, _⟩
  subst hr
  exact smtMin_size l

/-- If `l` has size `≤ n` and `smtMin l ≠ l`, then `(l, smtMin l) ∈ R n`. -/
theorem rule_mem_of_size {S : Signature} {n : Nat} {l : Term S}
    (hsize : Term.size l ≤ n) (hne : smtMin l ≠ l) :
    (l, smtMin l) ∈ R S n :=
  mem_R.mpr ⟨Term.size l, hsize, rfl, rfl, fun h => hne h.symm⟩

end EnumRules
