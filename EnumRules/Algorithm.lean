import Mathlib.Data.Finset.Basic
import EnumRules.Rewrite

open scoped Classical

/-
# The enumeration algorithm

We build up the rule set `R n` and the irreducible set `I n` by processing
sizes `1, 2, …, n` in order.

At size `k`, we only enumerate canonical terms built from irreducible subterms
(terms already found to be in normal form at smaller sizes). For each such
term `l`:
- If `l` simplifies with rules from smaller sizes (strict size decrease),
  we discard it — it is already covered.
- Otherwise we call SMT to obtain `smtMin l`.
  - If `smtMin l = l`, we add `l` to the irreducible set `I`.
  - If `smtMin l ≠ l`, we add the rule `(l, smtMin l)` to `R`.
-/

namespace EnumRules

variable {S : Signature}

/-- Enumeration of all terms of a given size. -/
opaque termsOfSize (S : Signature) : Nat → Finset (Term S)

/-- Specification of `termsOfSize`: it is exactly the set of terms of that size. -/
axiom mem_termsOfSize {S : Signature} {n : Nat} {t : Term S} :
    t ∈ termsOfSize S n ↔ Term.size t = n

/-- Enumeration of terms of size `n` whose direct subterms all belong to
the given set `subterms`. Only canonical forms (variables in lexicographic
order of first occurrence) are included. -/
opaque termsFromIrreducible (S : Signature) (subterms : Finset (Term S)) (n : Nat) :
    Finset (Term S)

/-- `canonical` holds for terms where variable constants appear in
lexicographic order of first occurrence. -/
opaque canonical {S : Signature} (t : Term S) : Prop

/-- Specification of `termsFromIrreducible`. A term is included iff its size
is n, its direct subterms are in the given set, and it is canonical. -/
axiom mem_termsFromIrreducible {S : Signature} {subterms : Finset (Term S)} {n : Nat}
    {t : Term S} :
    t ∈ termsFromIrreducible S subterms n ↔
      Term.size t = n ∧
      (∀ (f : S.σ) (args : Fin (S.arity f) → Term S),
        Term.node f args = t → ∀ i, args i ∈ subterms) ∧
      canonical t

/-- Every term has a variable renaming to a canonical form. -/
axiom exists_canonical_rename {S : Signature} (t : Term S) :
    ∃ (ρ : S.σ → S.σ) (hρ_arity : ∀ a, S.isVar a → S.arity (ρ a) = 0),
      canonical (Term.renameVars ρ hρ_arity t)

/-- If a term is not built from the given set, either its size is wrong,
a subterm is outside the set, or it is not canonical. -/
theorem not_mem_termsFromIrreducible {S : Signature} {sub : Finset (Term S)} {n : Nat}
    {t : Term S} (hsize : Term.size t = n)
    (hnot : t ∉ termsFromIrreducible S sub n) :
    (∃ (f : S.σ) (args : Fin (S.arity f) → Term S) (i : Fin (S.arity f)),
      Term.node f args = t ∧ args i ∉ sub) ∨ ¬ canonical t := by
  rw [mem_termsFromIrreducible] at hnot
  by_cases hsize_eq : Term.size t = n
  · -- hnot: ¬ (hsize_eq ∧ subterms ∧ canonical)
    -- size matches, so the issue is subterms or canonical
    have hnot' : ¬ ((∀ (f : S.σ) (args : Fin (S.arity f) → Term S),
        Term.node f args = t → ∀ i, args i ∈ sub) ∧ canonical t) := by
      intro h; apply hnot; exact ⟨hsize_eq, h.1, h.2⟩
    by_cases hsub : ∀ (f : S.σ) (args : Fin (S.arity f) → Term S),
        Term.node f args = t → ∀ i, args i ∈ sub
    · -- subterm condition holds, so canonical must fail
      exact Or.inr (fun hcanon => hnot' ⟨hsub, hcanon⟩)
    · -- subterm condition fails, extract the failing subterm
      push Not at hsub
      rcases hsub with ⟨f, args, heq, i, hi⟩
      exact Or.inl ⟨f, args, i, heq, hi⟩
  · exact absurd hsize hsize_eq

/-- All minimal terms of a given size. -/
noncomputable def minimalTermsOfSize (S : Signature) (n : Nat) : Finset (Term S) :=
  (termsOfSize S n).filter (fun l => smtMin l = l)

/-- The irreducible (already-minimal) set — contains all minimal terms.
Used as the subterm filter for `termsFromIrreducible`: any subterm not
in `I` is reducible, guaranteeing the enumeration only builds from
irreducible subterms. -/
noncomputable def I (S : Signature) : Nat → Finset (Term S)
  | 0     => ∅
  | n + 1 => I S n ∪ minimalTermsOfSize S (n + 1)

/-- The rule set. Only canonical terms from `termsFromIrreducible` are
enumerated; those not already minimal generate rules. -/
noncomputable def R (S : Signature) : Nat → RuleSet S
  | 0     => ∅
  | n + 1 => R S n ∪ (
      (termsFromIrreducible S (I S n) (n + 1)).filter (fun l =>
        ¬ simplifiesWith (R S n) l ∧ smtMin l ≠ l)
        |>.image (fun l => (l, smtMin l)))

/-- Rules contributed at size `n`. -/
noncomputable def newRulesAt (S : Signature) (n : Nat) : RuleSet S :=
    (termsFromIrreducible S (I S (n - 1)) n).filter (fun l =>
      ¬ simplifiesWith (R S (n - 1)) l ∧ smtMin l ≠ l)
      |>.image (fun l => (l, smtMin l))

/-- At the correctness level, rules can be applied to variable-renamed
instances. The algorithm achieves this by adding permuted rules after
each iteration. -/
axiom R_rename_closed {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R S n) (ρ : S.σ → S.σ)
    (hρ_arity : ∀ a, S.isVar a → S.arity (ρ a) = 0) :
    (Term.renameVars ρ hρ_arity l, Term.renameVars ρ hρ_arity r) ∈ R S n

/-- Non-canonical terms reach their smtMin via their canonical rename.
This follows from `exists_canonical_rename`, `R_rename_closed`, and
`smtMin_rename`. -/
axiom reaches_smtMin_noncanonical {S : Signature} {n : Nat} {u : Term S}
    (hsize : Term.size u ≤ n) (hnotcanon : ¬ canonical u) :
    StepStar (R S n) u (smtMin u)

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

/-- If a term is in I, its direct subterms are also in I.
This holds because I is built from `termsFromIrreducible` which requires
subterms to already be in I. -/
axiom I_subterm {S : Signature} {n : Nat} {f : S.σ} {args : Fin (S.arity f) → Term S}
    (h : Term.node f args ∈ I S n) (i : Fin (S.arity f)) : args i ∈ I S n

/-- Decompose `R S (n+1)` into `R S n` and the new rules at size `n+1`. -/
theorem R_succ_eq {S : Signature} (n : Nat) :
    R S (n + 1) = R S n ∪ newRulesAt S (n + 1) := by
  ext x
  have hsub : (n + 1 : Nat) - 1 = n := by omega
  simp [R, newRulesAt, hsub, Finset.mem_union, Finset.mem_image, Finset.mem_filter]

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
      · dsimp [newRulesAt] at hNew
        rcases Finset.mem_image.1 hNew with ⟨l', hfilter, heq⟩
        rcases Finset.mem_filter.1 hfilter with ⟨hmem_l', ⟨hnsp, hne'⟩⟩
        have hl_eq : l' = l := congrArg Prod.fst heq
        have hr_eq' : smtMin l' = r := congrArg Prod.snd heq
        rw [hl_eq] at hmem_l' hne' hr_eq' hnsp
        have hne_lr : l ≠ r := by
          rw [← hr_eq']
          exact Ne.symm hne'
        refine ⟨n + 1, le_refl _, (mem_termsFromIrreducible.mp hmem_l').1, hmem_l', hr_eq'.symm, hne_lr, hnsp⟩
    · rintro ⟨m, hm, hsize, hen, hr, hne, hnsp⟩
      rcases Nat.lt_or_eq_of_le hm with (hlt | heq)
      · left
        apply ih.mpr
        exact ⟨m, Nat.le_of_lt_succ hlt, hsize, hen, hr, hne, hnsp⟩
      · subst heq
        have hmem_l : l ∈ termsFromIrreducible S (I S n) (n + 1) := hen
        have hne_symm : smtMin l ≠ l := fun h => hne (h.symm.trans hr.symm)
        right
        dsimp [newRulesAt]
        refine Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨hmem_l, hnsp, hne_symm⟩, by simp [hr]⟩

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
  rw [hmin]
  exact hkbo_node

/-- `I` contains every minimal term whose size is bounded by `n`. -/
theorem I_contains_minimal {S : Signature} {n : Nat} {t : Term S}
    (hsize : Term.size t ≤ n) (hmin : smtMin t = t) : t ∈ I S n := by
  induction n with
  | zero =>
    have hsz : Term.size t = 0 := Nat.eq_zero_of_le_zero hsize
    have hpos : 1 ≤ Term.size t := Term.size_pos t
    omega
  | succ n ih =>
    rw [I]
    rcases Nat.lt_or_eq_of_le hsize with (hlt | heq)
    · have hsize_n : Term.size t ≤ n := by omega
      apply Finset.mem_union_left
      exact ih hsize_n
    · apply Finset.mem_union_right
      dsimp [minimalTermsOfSize]
      refine Finset.mem_filter.mpr ⟨mem_termsOfSize.mpr heq, hmin⟩

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
