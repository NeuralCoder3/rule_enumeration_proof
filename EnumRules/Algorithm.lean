import Mathlib.Data.Finset.Basic
import EnumRules.Rewrite

open scoped Classical

/-
# The enumeration algorithm

We build up the rule set `R n` and the irreducible set `I n` by
processing sizes `1, 2, …, n` in order.

At size `k`, we enumerate terms whose strict subterms all belong to the
irreducible set `I (k-1)` from the previous iteration.

For each such term `l`:
- If `l` simplifies with rules from smaller sizes (strict size decrease),
  we discard it — it is already covered.
- Otherwise we call SMT to obtain `smtMin l`.
  - If `smtMin l = l`, we add `l` to the irreducible set `I`.
  - If `smtMin l ≠ l`, we add the rule `(l, smtMin l)` to `R`.

Rule application is via *substitution*: a rule `(l, r) ∈ R` fires
whenever a subterm matches `apply σ l`, replacing it by `apply σ r`.
The substitution-monotonicity axiom `kbo_subst` guarantees that the
synthesised order on rule skeletons (`r ≺ₖ l`) lifts to every
substitution instance.
-/

namespace EnumRules

variable {S : Signature}

/-- Enumeration of terms of size `n` whose direct subterms all belong to
the given set `subterms`. -/
opaque termsFromIrreducible (S : Signature) (subterms : Finset (Term S)) (n : Nat) :
    Finset (Term S)

/-- Specification of `termsFromIrreducible`. -/
axiom mem_termsFromIrreducible {S : Signature} {subterms : Finset (Term S)} {n : Nat}
    {t : Term S} :
    t ∈ termsFromIrreducible S subterms n ↔
      Term.size t = n ∧
      ∀ (f : S.σ) (args : Fin (S.arity f) → Term S),
        Term.node f args = t → ∀ i, args i ∈ subterms

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

/-- `R` is monotone. -/
theorem R_subset {S : Signature} {m n : Nat} (h : m ≤ n) : R S m ⊆ R S n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih =>
    intro x hx
    rw [R]
    exact Finset.mem_union_left _ (ih hx)

/-- `I` is monotone. -/
theorem I_subset {S : Signature} {m n : Nat} (h : m ≤ n) : I S m ⊆ I S n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih =>
    intro x hx
    rw [I]
    exact Finset.mem_union_left _ (ih hx)

/-- Characterization of membership in `R n`. -/
theorem mem_R {S : Signature} {n : Nat} {l r : Term S} :
    (l, r) ∈ R S n ↔
      ∃ m, m ≤ n ∧ Term.size l = m ∧
      l ∈ termsFromIrreducible S (I S (m - 1)) m ∧
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
    rw [R, Finset.mem_union]
    constructor
    · rintro (hRprev | hNew)
      · rcases ih.mp hRprev with ⟨m, hm, hsize, hen, hr, hne, hnsp⟩
        exact ⟨m, Nat.le_succ_of_le hm, hsize, hen, hr, hne, hnsp⟩
      · rcases Finset.mem_image.1 hNew with ⟨l', hfilter, heq⟩
        rcases Finset.mem_filter.1 hfilter with ⟨hmem_l', ⟨hnsp, hne'⟩⟩
        have hl_eq : l' = l := congrArg Prod.fst heq
        have hr_eq : smtMin l' = r := congrArg Prod.snd heq
        rw [hl_eq] at hmem_l' hne' hr_eq hnsp
        have hne_lr : l ≠ r := by
          rw [← hr_eq]; exact Ne.symm hne'
        refine ⟨n + 1, le_refl _, ?_, hmem_l', hr_eq.symm, hne_lr, hnsp⟩
        rcases mem_termsFromIrreducible.mp hmem_l' with ⟨hsize, _⟩
        exact hsize
    · rintro ⟨m, hm, hsize, hen, hr, hne, hnsp⟩
      rcases Nat.lt_or_eq_of_le hm with (hlt | heq)
      · left
        exact ih.mpr ⟨m, Nat.le_of_lt_succ hlt, hsize, hen, hr, hne, hnsp⟩
      · subst heq
        have hne_symm : smtMin l ≠ l := fun h => hne (h.symm.trans hr.symm)
        right
        refine Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨hen, hnsp, hne_symm⟩, ?_⟩
        simp [hr]

/-- Every rule `(l, r)` in `R n` satisfies `l ≈ₜ r`. -/
theorem rule_equiv {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : l ≈ₜ r := by
  rcases mem_R.mp h with ⟨_, _, _, _, hr, _, _⟩
  subst hr
  exact equiv_symm (smtMin_equiv l)

/-- Every rule is KBO-decreasing on its skeleton. -/
theorem rule_kbo {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) : r ≺ₖ l := by
  rcases mem_R.mp h with ⟨_, _, _, _, hr, hne, _⟩
  subst hr
  rcases smtMin_le l with heq | hlt
  · exact (hne heq.symm).elim
  · exact hlt

/-- If a node is minimal, all its subterms are also minimal. -/
theorem subterm_of_minimal_is_minimal {S : Signature} {f : S.σ}
    {args : Fin (S.arity f) → Term S} (hmin : smtMin (Term.node f args) = Term.node f args)
    (i : Fin (S.arity f)) : smtMin (args i) = args i := by
  by_contra hne
  have hlt : smtMin (args i) ≺ₖ args i := by
    rcases smtMin_le (args i) with (heq | hlt)
    · exact (hne heq).elim
    · exact hlt
  let args' : Fin (S.arity f) → Term S :=
    fun j => if j = i then smtMin (args i) else args j
  have hrest : ∀ j, j ≠ i → args j = args' j := by
    intro j hj; simp [args', hj]
  have hkbo_node : (Term.node f args') ≺ₖ (Term.node f args) :=
    kbo_mono_ctx (as := args) (bs := args') (i := i) hrest (by
      dsimp [args']; simpa using hlt)
  have hequiv_node : smtMin (args i) ≈ₜ args i := smtMin_equiv (args i)
  have hequiv_args : ∀ j, args' j ≈ₜ args j := by
    intro j
    dsimp [args']
    split_ifs with h
    · subst h; exact hequiv_node
    · exact equiv_refl _
  have hequiv : (Term.node f args') ≈ₜ (Term.node f args) := equiv_congr hequiv_args
  have h_contra := smtMin_min (t := Term.node f args) (u := Term.node f args') hequiv
  apply h_contra
  rw [hmin]; exact hkbo_node

end EnumRules
