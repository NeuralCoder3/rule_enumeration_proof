import EnumRules.Algorithm

open scoped Classical

/-
# Algorithm correctness: construction-saturation + common normal form

## Role
Proves two completeness theorems for the k-bounded rule set
`R_can S k n` (size ≤ n, distinct-VC count ≤ k):

* `complete_common_normal_form` (construction level) — for
  `≈ₜ`-equivalent `Term S Empty` inputs `s, t` with `NoVar`, size ≤ n,
  and `numDistinctVCs ≤ k`, both reach the same irreducible normal
  form `c` via rule rewriting under `R_can S k n`.

* `complete_runtime` (runtime level) — for `≈ₜ`-equivalent runtime
  `Term S Ext` inputs `s, t` with `IsRuntime`, size ≤ n, and with
  `(s.usedExt ∪ t.usedExt).card ≤ |S.C|`, both reach a common
  rewrite-end-point via `R_can S |S.C| n` rewriting on `Term S Ext`.
  The proof lifts to `Term S Empty` via an injection `↑E ↪ S.C`,
  invokes the construction-level theorem (with `k = |S.C|`), and
  pushes the rewrites back via `StepStar.subst`.

The proof of `complete_common_normal_form` rests on
**construction-saturation** (`construction_saturation`, proved as a
theorem): for `c : Term S Empty` with `NoVar`, `numDistinctVCs c ≤ k`,
and R_can-irreducible at size ≤ n, we have `smtMin c = c`. The
structural induction `construction_irreducible_in_I_can_at_size`
shows that every `NoVar` irreducible term satisfying the k-bound lies
in `I_can`, from which `smtMin`-fixedness is immediate.

The k-bound is preserved through rewriting (`Step.preserves_VCs`,
`StepStar.preserves_VCs`), using the `smtMin_varSet` /
`smtMin_constPSet` axioms.

## Axioms (2)
* `smtMin_apply_NoVar` — `smtMin` doesn't introduce S.V variables
  (used in `Step.preserves_NoVar`).
* `canonical_of_NoVar` — `NoVar` terms satisfy the `Canonical` filter
  (per-orbit selector, doesn't affect soundness).

Depends also on `equiv_embExt` (in `Subst.lean`) and `smtMin_varSet`,
`smtMin_constPSet` (in `Oracle.lean`).

## Theorems
* `Step.preserves_NoVar` / `StepStar.preserves_NoVar`.
* `Step.preserves_VCs` / `StepStar.preserves_VCs` /
  `StepStar.preserves_numDistinctVCs_le`.
* `construction_irreducible_in_I_can_at_size` (private) /
  `construction_irreducible_in_I_can`.
* `construction_saturation` — proved.
* `complete_common_normal_form` — proved.
* `complete_runtime` — proved.
-/

namespace EnumRules

variable {S : Signature}

/-! ## Structural facts about R_can / I_can over Term S Empty -/

theorem R_can_subset {S : Signature} {k m n : Nat} (h : m ≤ n) :
    R_can S k m ⊆ R_can S k n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => intro x hx; rw [R_can]; exact Finset.mem_union_left _ (ih hx)

theorem I_can_subset {S : Signature} {k m n : Nat} (h : m ≤ n) :
    I_can S k m ⊆ I_can S k n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => intro x hx; rw [I_can]; exact Finset.mem_union_left _ (ih hx)

@[aesop safe forward]
theorem mem_R_can_props {k n : Nat} {l r : Term S Empty} (h : (l, r) ∈ R_can S k n) :
    r = smtMin l ∧ l ≠ r := by
  induction n with
  | zero => simp [R_can] at h
  | succ n ih =>
      simp only [R_can, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
                 Prod.mk.injEq] at h
      obtain hPrev | ⟨l', ⟨_, _, _, hne⟩, rfl, rfl⟩ := h
      · exact ih hPrev
      · exact ⟨rfl, Ne.symm hne⟩

theorem mem_R_can_intro {k n : Nat} {l : Term S Empty}
    (hsize : Term.size l ≤ n)
    (hen : l ∈ renamingOrbit (termsFromIrreducible S (I_can S k (Term.size l - 1))
                              k (Term.size l)))
    (hcan : Canonical l)
    (hnsp : ¬ simplifiesWith (R_can S k (Term.size l - 1)) l)
    (hne : smtMin l ≠ l) :
    (l, smtMin l) ∈ R_can S k n := by
  refine R_can_subset hsize ?_
  have hsucc : Term.size l - 1 + 1 = Term.size l := by
    have := Term.size_pos l; omega
  rw [← hsucc, R_can]
  refine Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨l, Finset.mem_filter.mpr ⟨?_, hcan, hnsp, hne⟩, rfl⟩)
  rwa [hsucc]

theorem rule_equiv_can {k n : Nat} {l r : Term S Empty} (h : (l, r) ∈ R_can S k n) :
    l ≈ₜ r := by
  obtain ⟨rfl, _⟩ := mem_R_can_props h
  exact equiv_symm (smtMin_equiv l)

theorem rule_kbo_can {k n : Nat} {l r : Term S Empty} (h : (l, r) ∈ R_can S k n) :
    r ≺ₖ l := by
  obtain ⟨rfl, hne⟩ := mem_R_can_props h
  exact smtMin_strict (Ne.symm hne)

/-! ## Termination + reaching a normal form -/

theorem terminates_can {Ext : Type} (k n : Nat) :
    WellFounded (fun t s : Term S Ext => Step (R_can S k n) s t) :=
  Subrelation.wf (fun h => Step.kbo_of (fun hlr => rule_kbo_can hlr) h) kbo_wf

theorem reaches_normal_form_can {Ext : Type} (k n : Nat) (s : Term S Ext) :
    ∃ s', StepStar (R_can S k n) s s' ∧ ∀ u, ¬ Step (R_can S k n) s' u := by
  induction s using (terminates_can k n).induction with
  | _ s ih =>
      by_cases h : ∃ u, Step (R_can S k n) s u
      · obtain ⟨u, hu⟩ := h
        obtain ⟨s', hsu, hirr⟩ := ih u hu
        exact ⟨s', .head hu hsu, hirr⟩
      · exact ⟨s, .refl, fun u hu => h ⟨u, hu⟩⟩

/-- `I_can` members are smtMin-fixed (built into the I_can filter). -/
@[aesop safe forward]
theorem I_can_smtMin_fixed {k n : Nat} {c : Term S Empty} (hc : c ∈ I_can S k n) :
    smtMin c = c := by
  induction n with
  | zero => simp [I_can] at hc
  | succ n ih =>
      rw [I_can, Finset.mem_union] at hc
      aesop

/-! ## Behavioural axioms

`smtMin_apply_NoVar` says `smtMin` doesn't introduce S.V variables.
This is the only behavioural axiom about `smtMin` needed (apart from
`smtMin_equiv` / `smtMin_min` / `smtMin_le` from `Oracle.lean`). -/

/-- `smtMin` doesn't introduce S.V variables: if `apply σ l` has no
variable, neither does `apply σ (smtMin l)`. -/
axiom smtMin_apply_NoVar {l : Term S Empty} {σ : Subst S Empty}
    (h : Term.NoVar (apply σ l)) : Term.NoVar (apply σ (smtMin l))

/-! ## Step.preserves_NoVar — Step keeps the NoVar property -/

/-- `Step (R_can S k n)` preserves the `NoVar` property. -/
theorem Step.preserves_NoVar {k n : Nat} {s t : Term S Empty}
    (h : Step (R_can S k n) s t) (hg : Term.NoVar s) : Term.NoVar t := by
  induction h with
  | @root l r σ hmem =>
      obtain ⟨rfl, _⟩ := mem_R_can_props hmem
      exact smtMin_apply_NoVar hg
  | @ctx f as bs i hstep hrest ih =>
      intro j
      by_cases hj : j = i
      · exact hj ▸ ih (hg i)
      · exact (hrest j hj).symm ▸ hg j

/-- `StepStar (R_can S k n)` preserves the `NoVar` property. -/
theorem StepStar.preserves_NoVar {k n : Nat} {s t : Term S Empty}
    (h : StepStar (R_can S k n) s t) (hg : Term.NoVar s) : Term.NoVar t := by
  induction h with
  | refl => exact hg
  | tail _ hstep ih => exact Step.preserves_NoVar hstep ih

/-- Rewriting under `R_can` doesn't grow size. -/
theorem StepStar.size_le {Ext : Type} {k n : Nat} {s t : Term S Ext}
    (h : StepStar (R_can S k n) s t) : Term.size t ≤ Term.size s := by
  rcases StepStar.kbo_of (fun hlr => rule_kbo_can hlr) h with heq | hlt
  · rw [heq]
  · exact kbo_size_le hlt

/-! ## `Step (R_can)` doesn't introduce new vars or constPs

Combined with `smtMin_varSet` / `smtMin_constPSet`, each step is
`varSet ⊆`- and `constPSet ⊆`-shrinking, hence doesn't increase
`numDistinctVCs`. This is essential to preserve the `k`-bound through
rewriting. -/

/-- `Step (R_can S k n)` doesn't introduce new variables or
ConstPlaceholders. -/
theorem Step.preserves_VCs {k n : Nat} {s t : Term S Empty}
    (h : Step (R_can S k n) s t) :
    t.varSet ⊆ s.varSet ∧ t.constPSet ⊆ s.constPSet := by
  induction h with
  | @root l r σ hmem =>
      obtain ⟨rfl, _⟩ := mem_R_can_props hmem
      exact ⟨apply_varSet_subset σ (smtMin_varSet l) (smtMin_constPSet l),
             apply_constPSet_subset σ (smtMin_varSet l) (smtMin_constPSet l)⟩
  | @ctx f as bs i _ hrest ih =>
      refine ⟨?_, ?_⟩ <;> intro x hx
      · rw [Term.varSet_node, Finset.mem_biUnion] at hx
        obtain ⟨j, _, hj⟩ := hx
        rw [Term.varSet_node, Finset.mem_biUnion]
        refine ⟨j, Finset.mem_univ _, ?_⟩
        by_cases hji : j = i
        · exact hji ▸ ih.1 (hji ▸ hj)
        · exact (hrest j hji).symm ▸ hj
      · rw [Term.constPSet_node, Finset.mem_biUnion] at hx
        obtain ⟨j, _, hj⟩ := hx
        rw [Term.constPSet_node, Finset.mem_biUnion]
        refine ⟨j, Finset.mem_univ _, ?_⟩
        by_cases hji : j = i
        · exact hji ▸ ih.2 (hji ▸ hj)
        · exact (hrest j hji).symm ▸ hj

/-- `StepStar (R_can S k n)` doesn't introduce new variables or
ConstPlaceholders. -/
theorem StepStar.preserves_VCs {k n : Nat} {s t : Term S Empty}
    (h : StepStar (R_can S k n) s t) :
    t.varSet ⊆ s.varSet ∧ t.constPSet ⊆ s.constPSet := by
  induction h with
  | refl => exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | tail _ hstep ih =>
      have := Step.preserves_VCs hstep
      exact ⟨subset_trans this.1 ih.1, subset_trans this.2 ih.2⟩

/-- `StepStar (R_can S k n)` doesn't increase `numDistinctVCs`. -/
theorem StepStar.preserves_numDistinctVCs_le {k n : Nat} {s t : Term S Empty}
    (h : StepStar (R_can S k n) s t) :
    Term.numDistinctVCs t ≤ Term.numDistinctVCs s := by
  have := StepStar.preserves_VCs h
  unfold Term.numDistinctVCs
  exact Nat.add_le_add (Finset.card_le_card this.1) (Finset.card_le_card this.2)

/-! ## Construction-saturation: irreducible `NoVar` terms are smtMin-fixed -/

/-- Every `NoVar` term satisfies the `Canonical` filter. Justification:
`Canonical` is intended as an opaque per-renaming-orbit selector; for
`NoVar` terms (no S.V variables) there's no orbit ambiguity that
affects soundness. (The old framework's `canonical_of_ground` had the
same shape, on the older `IsGround` predicate.) -/
axiom canonical_of_NoVar {t : Term S Empty} (h : Term.NoVar t) : Canonical t

/-- The identity renaming is the identity on terms. -/
theorem renameTerm_id (t : Term S Empty) : renameTerm id id t = t := by
  induction t with
  | var v       => rfl
  | constP c    => rfl
  | node f args ih =>
      show Term.node f (fun i => renameTerm id id (args i)) = Term.node f args
      exact Term.node_ext ih
  | ext e       => exact e.elim

/-- A term in `s` is also in `renamingOrbit s` (via identity renaming). -/
theorem self_mem_renamingOrbit {t : Term S Empty} {s : Finset (Term S Empty)}
    (ht : t ∈ s) : t ∈ renamingOrbit s := by
  rw [renamingOrbit, Finset.mem_biUnion]
  refine ⟨t, ht, ?_⟩
  rw [Finset.mem_image]
  exact ⟨(id, id), by simp, renameTerm_id t⟩

/-- `Step` over the empty rule set is impossible. -/
theorem Step.not_empty {Ext : Type} {s t : Term S Ext} :
    ¬ Step (∅ : RuleSet S) s t := by
  intro h
  induction h with
  | @root _ _ _ hmem => simp at hmem
  | ctx _ _ ih       => exact ih

/-- `StepStar` over the empty rule set is identity. -/
theorem StepStar.empty_eq {Ext : Type} {s t : Term S Ext}
    (h : StepStar (∅ : RuleSet S) s t) : s = t := by
  induction h with
  | refl              => rfl
  | tail _ hstep _    => exact absurd hstep Step.not_empty

/-- A term doesn't simplify under the empty rule set. -/
theorem not_simplifiesWith_empty {Ext : Type} {t : Term S Ext} :
    ¬ simplifiesWith (∅ : RuleSet S) t := by
  rintro ⟨u, hStep, hsize⟩
  have heq := StepStar.empty_eq hStep
  subst heq; omega

/-- Auxiliary lemma: for a `NoVar`, R_can-irreducible term `t` of
size ≤ n and `numDistinctVCs t ≤ k`, `t ∈ I_can S k (Term.size t)`.
Proof by structural induction on `t`. -/
private theorem construction_irreducible_in_I_can_at_size (k : Nat) :
    ∀ (t : Term S Empty),
      Term.NoVar t →
      Term.numDistinctVCs t ≤ k →
      (∀ u, ¬ Step (R_can S k (Term.size t)) t u) →
      t ∈ I_can S k (Term.size t) := by
  intro t
  induction t with
  | var v => intro hg _ _; exact hg.elim
  | ext e => intro _ _ _; exact e.elim
  | constP c =>
      intro hg hk hirr
      have hen : Term.constP (S := S) (Ext := Empty) c ∈
          termsFromIrreducible S (I_can S k 0) k 1 := by
        rw [mem_termsFromIrreducible]
        exact ⟨rfl, hk, fun f' args' heq _ => by cases heq⟩
      have hen_orbit :
          Term.constP c ∈ renamingOrbit (termsFromIrreducible S (I_can S k 0) k 1) :=
        self_mem_renamingOrbit hen
      have hcan : Canonical (Term.constP (S := S) (Ext := Empty) c) :=
        canonical_of_NoVar hg
      have hnsp : ¬ simplifiesWith (R_can S k 0) (Term.constP (S := S) (Ext := Empty) c) := by
        show ¬ simplifiesWith (∅ : RuleSet S) _
        exact not_simplifiesWith_empty
      have hsmt : smtMin (Term.constP (S := S) (Ext := Empty) c) = Term.constP c := by
        by_contra hne
        have hrule : (Term.constP c, smtMin (Term.constP (S := S) (Ext := Empty) c)) ∈
                      R_can S k 1 :=
          mem_R_can_intro (le_refl _) (by simpa using hen_orbit) hcan
            (by simpa using hnsp) hne
        exact hirr _ (Step.root_id hrule)
      show Term.constP c ∈ I_can S k 1
      rw [show (1 : Nat) = 0 + 1 from rfl, I_can]
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hen_orbit, hcan, hnsp, hsmt⟩)
  | node f args ih =>
      intro hg hk hirr
      set N := Term.size (Term.node f args : Term S Empty)
      have hargs_k : ∀ i, Term.numDistinctVCs (args i) ≤ k := fun i =>
        le_trans (Term.numDistinctVCs_arg_le args i) hk
      have hargs_mem : ∀ i, args i ∈ I_can S k (N - 1) := fun i =>
        I_can_subset (by have := Term.size_arg_lt f args i; omega)
          (ih i (hg i) (hargs_k i) fun u hstep => Step.irreducible_arg hirr u
            (Step.lift (R_can_subset (Term.size_arg_lt f args i).le) hstep))
      have hen : (Term.node f args : Term S Empty) ∈
          termsFromIrreducible S (I_can S k (N - 1)) k N :=
        mem_termsFromIrreducible.mpr ⟨rfl, hk, by aesop⟩
      have hen_orbit : (Term.node f args : Term S Empty) ∈
          renamingOrbit (termsFromIrreducible S (I_can S k (N - 1)) k N) :=
        self_mem_renamingOrbit hen
      have hcan : Canonical (Term.node f args : Term S Empty) := canonical_of_NoVar hg
      have hnsp : ¬ simplifiesWith (R_can S k (N - 1)) (Term.node f args : Term S Empty) :=
        not_simplifiesWith_of_irreducible fun u hstep =>
          hirr u (Step.lift (R_can_subset (by omega)) hstep)
      have hsmt : smtMin (Term.node f args : Term S Empty) = Term.node f args := by
        by_contra hne
        have hrule : (Term.node f args, smtMin (Term.node f args : Term S Empty)) ∈
                      R_can S k N :=
          mem_R_can_intro (le_refl _) hen_orbit hcan hnsp hne
        exact hirr _ (Step.root_id hrule)
      have hsucc : N - 1 + 1 = N := by have := Term.size_pos (Term.node f args); omega
      rw [show N = N - 1 + 1 from hsucc.symm, I_can]
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hsucc ▸ hen_orbit, hcan, hnsp, hsmt⟩)

/-- For a `NoVar` `t : Term S Empty` of size ≤ n with `numDistinctVCs t ≤ k`
that is R_can-irreducible, `t ∈ I_can S k n`. -/
theorem construction_irreducible_in_I_can {k n : Nat} {t : Term S Empty}
    (hsize : Term.size t ≤ n)
    (hg : Term.NoVar t) (hk : Term.numDistinctVCs t ≤ k)
    (hirr : ∀ u, ¬ Step (R_can S k n) t u) : t ∈ I_can S k n := by
  apply I_can_subset hsize
  apply construction_irreducible_in_I_can_at_size k t hg hk
  intro u hstep
  exact hirr u (Step.lift (R_can_subset hsize) hstep)

/-- **Construction-saturation**: a `NoVar` term in `Term S Empty` with
`numDistinctVCs t ≤ k` that is R_can-irreducible at size ≤ n is its
own `smtMin`. -/
theorem construction_saturation {k n : Nat} {c : Term S Empty}
    (hsize : Term.size c ≤ n)
    (hg : Term.NoVar c) (hk : Term.numDistinctVCs c ≤ k)
    (hirr : ∀ u, ¬ Step (R_can S k n) c u) : smtMin c = c := by
  have hc_mem : c ∈ I_can S k n :=
    construction_irreducible_in_I_can hsize hg hk hirr
  exact I_can_smtMin_fixed hc_mem

/-! ## Common normal form theorem (construction level, `Term S Empty`) -/

/-- **Common normal form theorem at `Term S Empty`**: for any pair of
`≈ₜ`-equivalent `Term S Empty` terms with no S.V variables (`NoVar`),
size ≤ n, and distinct-VC count ≤ k, both reach the same irreducible
normal form via rule rewriting alone. -/
theorem complete_common_normal_form
    (k n : Nat) {s t : Term S Empty}
    (hs_NoVar : Term.NoVar s) (ht_NoVar : Term.NoVar t)
    (hs_size : Term.size s ≤ n) (ht_size : Term.size t ≤ n)
    (hs_k : Term.numDistinctVCs s ≤ k) (ht_k : Term.numDistinctVCs t ≤ k)
    (hst : s ≈ₜ t) :
    ∃ c, Term.NoVar c ∧
         StepStar (R_can S k n) s c ∧
         StepStar (R_can S k n) t c := by
  obtain ⟨s', hss', hs_irr⟩ := reaches_normal_form_can k n s
  obtain ⟨t', htt', ht_irr⟩ := reaches_normal_form_can k n t
  have hs'_g := StepStar.preserves_NoVar hss' hs_NoVar
  have ht'_g := StepStar.preserves_NoVar htt' ht_NoVar
  have hs'_size := le_trans (StepStar.size_le hss') hs_size
  have ht'_size := le_trans (StepStar.size_le htt') ht_size
  have hs'_k := le_trans (StepStar.preserves_numDistinctVCs_le hss') hs_k
  have ht'_k := le_trans (StepStar.preserves_numDistinctVCs_le htt') ht_k
  have hs_eq := StepStar.equiv_of (fun h => rule_equiv_can h) hss'
  have ht_eq := StepStar.equiv_of (fun h => rule_equiv_can h) htt'
  have hst' : s' ≈ₜ t' :=
    equiv_trans (equiv_symm hs_eq) (equiv_trans hst ht_eq)
  have hsm_s : smtMin s' = s' := construction_saturation hs'_size hs'_g hs'_k hs_irr
  have hsm_t : smtMin t' = t' := construction_saturation ht'_size ht'_g ht'_k ht_irr
  have h_eq : smtMin s' = smtMin t' :=
    smtMin_resp (hsm_s.symm ▸ hs'_g) (hsm_t.symm ▸ ht'_g) hst'
  have hs't' : s' = t' := by
    calc s' = smtMin s' := hsm_s.symm
      _ = smtMin t' := h_eq
      _ = t' := hsm_t
  exact ⟨s', hs'_g, hss', hs't' ▸ htt'⟩

/-! ## Runtime common normal form theorem

For runtime terms `s, t : Term S Ext` with arbitrary `Ext`, if the
number of distinct ext-leaves used in `s` and `t` together is at
most `|S.C|`, both reach a common normal form via runtime rewriting.

The proof embeds each ext-leaf as a fresh ConstPlaceholder via an
injection `↑(s.usedExt ∪ t.usedExt) ↪ S.C`, invokes the construction-
level theorem at `Term S Empty`, and pushes the rewrite sequence
back to `Term S Ext` via `StepStar.subst` along the inverse
substitution. -/

/-- **Common normal form theorem at `Term S Ext` (runtime)**: for any
pair of `≈ₜ`-equivalent runtime terms whose distinct ext-leaves fit
into `|S.C|`, both reach the same rewrite-end-point via
`R_can S |S.C| n`. -/
theorem complete_runtime
    {Ext : Type} [DecidableEq Ext] [Nonempty S.C]
    (n : Nat) {s t : Term S Ext}
    (hs : Term.IsRuntime s) (ht : Term.IsRuntime t)
    (hs_size : Term.size s ≤ n) (ht_size : Term.size t ≤ n)
    (hcard : (s.usedExt ∪ t.usedExt).card ≤ Fintype.card S.C)
    (hst : s ≈ₜ t) :
    ∃ c, StepStar (R_can S (Fintype.card S.C) n) s c ∧
         StepStar (R_can S (Fintype.card S.C) n) t c := by
  set E := s.usedExt ∪ t.usedExt with hE_def
  have hE_card : Fintype.card (↑E : Type _) ≤ Fintype.card S.C := by
    simpa [Fintype.card_coe] using hcard
  obtain ⟨g⟩ : Nonempty (↑E ↪ S.C) := Function.Embedding.nonempty_of_card_le hE_card
  let f : Ext → S.C := fun e =>
    open Classical in
    if h : e ∈ E then g ⟨e, h⟩ else Classical.arbitrary S.C
  have hf_E : ∀ e (he : e ∈ E), f e = g ⟨e, he⟩ := by
    intro e he
    simp [f, he]
  have hf_inj : ∀ e₁ ∈ E, ∀ e₂ ∈ E, f e₁ = f e₂ → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ heq
    rw [hf_E _ he₁, hf_E _ he₂] at heq
    exact Subtype.mk.inj (g.injective heq)
  -- Lift to Term S Empty.
  set s' := Term.embExt f s with hs'_def
  set t' := Term.embExt f t with ht'_def
  have hs'_NoVar : Term.NoVar s' := Term.NoVar_embExt f (Term.NoVar_of_IsRuntime hs)
  have ht'_NoVar : Term.NoVar t' := Term.NoVar_embExt f (Term.NoVar_of_IsRuntime ht)
  have hs'_size : Term.size s' ≤ n := by rw [hs'_def, Term.size_embExt]; exact hs_size
  have ht'_size : Term.size t' ≤ n := by rw [ht'_def, Term.size_embExt]; exact ht_size
  have hst' : s' ≈ₜ t' := equiv_embExt hs ht f hf_inj hst
  -- The lifted terms' distinct-VC count is bounded by |S.C| (no vars,
  -- constPs all from `f`'s image which has card ≤ |S.C|).
  have hs'_k : Term.numDistinctVCs s' ≤ Fintype.card S.C := by
    rw [Term.numDistinctVCs_of_NoVar hs'_NoVar]
    exact le_trans (Finset.card_le_univ _) (le_refl _)
  have ht'_k : Term.numDistinctVCs t' ≤ Fintype.card S.C := by
    rw [Term.numDistinctVCs_of_NoVar ht'_NoVar]
    exact le_trans (Finset.card_le_univ _) (le_refl _)
  -- Apply the construction-level theorem.
  obtain ⟨c', _, hsc', htc'⟩ :=
    complete_common_normal_form (Fintype.card S.C) n
      hs'_NoVar ht'_NoVar hs'_size ht'_size hs'_k ht'_k hst'
  -- Push the rewrites back via the inverse substitution.
  let σ := Subst.invEmb E f
  have hs_inv : apply σ s' = s :=
    apply_invEmb_embExt hf_inj hs (Finset.subset_union_left)
  have ht_inv : apply σ t' = t :=
    apply_invEmb_embExt hf_inj ht (Finset.subset_union_right)
  refine ⟨apply σ c', ?_, ?_⟩
  · rw [← hs_inv]; exact StepStar.subst hsc' σ
  · rw [← ht_inv]; exact StepStar.subst htc' σ

end EnumRules
