import EnumRules.Algorithm

open scoped Classical

/-
# Algorithm correctness on top of `Algorithm.lean`'s definitions

## Role
Proves the algorithm's completeness theorem:

* `complete_common_normal_form` — for *S.V-ground* `≈ₜ`-equivalent
  inputs of bounded size, the algorithm reaches the **same**
  representative `c ∈ I_can S n`.

`R_can`, `I_can`, `ExtStep`, `ExtStepStar`, and `Canonical` are
defined in `Algorithm.lean`; this file proves their properties.

## Axioms (2)
* `canonical_of_ground` — every ground term is canonical. Vacuously
  true: `Canonical` constrains how S.V variables appear, but ground
  terms have none.
* `smtMin_apply_ground` — `smtMin` doesn't introduce new variables:
  if `apply σ l` is ground, so is `apply σ (smtMin l)`. Used to derive
  ground-preservation of `Step (R_can S n)`.

## Theorems-from-axioms (previously axioms)
* `ground_irreducible_in_I_can` — every R_can-irreducible ground term
  of size ≤ n is in `I_can S n`. Proved by structural induction
  (subterms enter `I_can` at smaller sizes; `smtMin t = t` follows by
  contradiction with `mem_R_can_intro` + `Step.root_id`).
* `Step.preserves_ground` / `StepStar.preserves_ground` —
  ground-preservation of rewriting (uses `smtMin_apply_ground`).

## Runtime convention
At runtime, inputs are S.V-ground: user-level "variables" in input
formulas are 0-ary symbols of `S.σ`, *not* `Term.var v`. `Term.var`
exists only for algorithm-internal rule schemas; substitution at
runtime instantiates these against ground subterms. With this
convention, `Canonical` is vacuous on inputs and the common-normal-form
theorem reaches *exact* equality (no α-quotient).
-/

namespace EnumRules

variable {S : Signature}

theorem R_can_subset {S : Signature} {m n : Nat} (h : m ≤ n) :
    R_can S m ⊆ R_can S n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => intro x hx; rw [R_can]; exact Finset.mem_union_left _ (ih hx)

theorem I_can_subset {S : Signature} {m n : Nat} (h : m ≤ n) :
    I_can S m ⊆ I_can S n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => intro x hx; rw [I_can]; exact Finset.mem_union_left _ (ih hx)

theorem mem_R_can_props {n : Nat} {l r : Term S} (h : (l, r) ∈ R_can S n) :
    r = smtMin l ∧ l ≠ r := by
  induction n with
  | zero => rw [R_can] at h; simp at h
  | succ n ih =>
      rw [R_can, Finset.mem_union] at h
      rcases h with hPrev | hNew
      · exact ih hPrev
      · rcases Finset.mem_image.1 hNew with ⟨l', hfilter, heq⟩
        rcases Finset.mem_filter.1 hfilter with ⟨_, _, _, hne'⟩
        have hl_eq : l' = l := congrArg Prod.fst heq
        have hr_eq : smtMin l' = r := congrArg Prod.snd heq
        rw [hl_eq] at hne' hr_eq
        exact ⟨hr_eq.symm, fun hlr => hne' (hr_eq.trans hlr.symm)⟩

theorem mem_R_can_intro {n : Nat} {l : Term S}
    (hsize : Term.size l ≤ n)
    (hen : l ∈ termsFromIrreducible S (I_can S (Term.size l - 1)) (Term.size l))
    (hcan : Canonical l)
    (hnsp : ¬ simplifiesWith (R_can S (Term.size l - 1)) l)
    (hne : smtMin l ≠ l) :
    (l, smtMin l) ∈ R_can S n := by
  have h_at_size : (l, smtMin l) ∈ R_can S (Term.size l) := by
    set k := Term.size l - 1 with hk
    have hk_succ : k + 1 = Term.size l := by
      simp [hk]; have := Term.size_pos l; omega
    rw [← hk_succ, R_can]
    refine Finset.mem_union_right _ <| Finset.mem_image.mpr
      ⟨l, Finset.mem_filter.mpr ⟨?_, hcan, ?_, hne⟩, rfl⟩
    · rw [hk_succ]; exact hen
    · exact hnsp
  exact R_can_subset hsize h_at_size

theorem rule_equiv_can {n : Nat} {l r : Term S} (h : (l, r) ∈ R_can S n) :
    l ≈ₜ r := by
  rcases mem_R_can_props h with ⟨hr, _⟩
  subst hr; exact equiv_symm (smtMin_equiv l)

theorem rule_kbo_can {n : Nat} {l r : Term S} (h : (l, r) ∈ R_can S n) :
    r ≺ₖ l := by
  rcases mem_R_can_props h with ⟨hr, hne⟩
  subst hr
  exact smtMin_strict (Ne.symm hne)

/-! ## Termination + reaching a normal form -/

theorem terminates_can (n : Nat) :
    WellFounded (fun t s : Term S => Step (R_can S n) s t) := by
  apply Subrelation.wf (r := fun t s : Term S => t ≺ₖ s)
  · intro t s h; exact Step.kbo_of (fun hlr => rule_kbo_can hlr) h
  · exact InvImage.wf (f := id) kbo_wf

theorem reaches_normal_form_can (n : Nat) (s : Term S) :
    ∃ s', StepStar (R_can S n) s s' ∧ ∀ u, ¬ Step (R_can S n) s' u := by
  induction s using (terminates_can n).induction with
  | _ s ih =>
      by_cases h : ∃ u, Step (R_can S n) s u
      · rcases h with ⟨u, hu⟩
        rcases ih u hu with ⟨s', hsu, hirr⟩
        exact ⟨s', Relation.ReflTransGen.head hu hsu, hirr⟩
      · push Not at h
        exact ⟨s, Relation.ReflTransGen.refl, h⟩

/-- **Saturation**: every well-formed canonical reducible term has a
rule in `R_can` (one-step reduction). -/
theorem saturated_can {n : Nat} {l : Term S} (hsize : Term.size l ≤ n)
    (hen : l ∈ termsFromIrreducible S (I_can S (Term.size l - 1)) (Term.size l))
    (hcan : Canonical l)
    (hnsp : ¬ simplifiesWith (R_can S (Term.size l - 1)) l)
    (hne : smtMin l ≠ l) :
    Step (R_can S n) l (smtMin l) :=
  Step.root_id (mem_R_can_intro hsize hen hcan hnsp hne)

/-! ## ExtStep / ExtStepStar properties

The two operational steps (`ExtStep.rule`, `ExtStep.class_lookup`)
are defined in `Algorithm.lean`. Both preserve `≈ₜ` (rules by
`rule_equiv_can`; class lookup by hypothesis). A `smtMin` runtime
step is **not** included — `smtMin t` is recovered as the *unique*
representative `c ∈ I_can` with `c ≈ₜ t`, found via `class_lookup`.

For *ground* inputs, the source `t` of a `class_lookup` step is itself
the irreducible normal form `s'`, and `s' ∈ I_can S n` directly (by
`ground_irreducible_in_I_can`). Then by `I_can_unique_per_class`, two
ground inputs `s ≈ₜ t` reach the **same** `c = s' = t' ∈ I_can` — the
common normal form, with no `class_lookup` step needed at all
(see `complete_common_normal_form`). -/

/-- `I_can` members are smtMin-fixed (built into the I_can filter). -/
theorem I_can_smtMin_fixed {n : Nat} {c : Term S} (hc : c ∈ I_can S n) :
    smtMin c = c := by
  induction n with
  | zero => rw [I_can] at hc; simp at hc
  | succ n ih =>
      rw [I_can, Finset.mem_union] at hc
      rcases hc with hPrev | hNew
      · exact ih hPrev
      · exact (Finset.mem_filter.1 hNew).2.2.2

/-- `I_can` has **at most one** representative per `≈ₜ`-class
among **ground** members: two ground `I_can` members in the same
`≈ₜ`-class are equal, because each is its own `smtMin` and `smtMin`
respects `≈ₜ` on ground inputs. -/
theorem I_can_unique_per_class {n : Nat} {c d : Term S}
    (hc_ground : Term.IsGround c) (hd_ground : Term.IsGround d)
    (hc : c ∈ I_can S n) (hd : d ∈ I_can S n) (h : c ≈ₜ d) : c = d := by
  have hsm_c : smtMin c = c := I_can_smtMin_fixed hc
  have hsm_d : smtMin d = d := I_can_smtMin_fixed hd
  have hg_smc : Term.IsGround (smtMin c) := hsm_c.symm ▸ hc_ground
  have hg_smd : Term.IsGround (smtMin d) := hsm_d.symm ▸ hd_ground
  have h_eq : smtMin c = smtMin d := smtMin_resp hg_smc hg_smd h
  rw [hsm_c, hsm_d] at h_eq
  exact h_eq

/-! ## Ground-restricted completeness

Runtime inputs are S.V-ground: user-level "variables" in input
formulas are 0-ary symbols of `S.σ`, never `Term.var v`. With this
convention, `I_can_complete_subst` reduces to a single fact —
ground R_can-irreducibles of size ≤ n are stored in `I_can` — and
both anchors (source pre-image and destination representative)
collapse to `t` itself.

Two supporting facts about `R_can` rules:

* `smtMin_apply_ground` (axiom) — `smtMin` doesn't introduce
  variables. Justification: with positive KBO weights, the
  KBO-minimum has no more variables than the original.
* `canonical_of_ground` (axiom) — ground terms are canonical
  (vacuously). The canonical filter orders S.V variables; ground
  terms have none, so any ordering trivially holds.

From these two, plus the algorithm's saturation properties
(`mem_R_can_intro`, `mem_termsFromIrreducible`),
`ground_irreducible_in_I_can` is **provable** — see below.

`Step (R_can S n)` ground-preservation follows from
`smtMin_apply_ground` (since R_can rules have shape `(l, smtMin l)`
per `mem_R_can_props`). -/

/-- `smtMin` doesn't introduce new variables. Equivalently: if a
ground instance of `l` is ground, the corresponding instance of
`smtMin l` is ground too. -/
axiom smtMin_apply_ground {l : Term S} {σ : Subst S}
    (h : Term.IsGround (apply σ l)) : Term.IsGround (apply σ (smtMin l))

/-- Ground terms are canonical (vacuously: no S.V variables to
misorder). -/
axiom canonical_of_ground {t : Term S} (h : Term.IsGround t) : Canonical t

/-- `Step (R_can S n)` preserves groundness. -/
theorem Step.preserves_ground {n : Nat} {s t : Term S}
    (h : Step (R_can S n) s t) (hg : Term.IsGround s) : Term.IsGround t := by
  induction h with
  | @root l r σ hmem =>
      rcases mem_R_can_props hmem with ⟨hr, _⟩
      subst hr
      exact smtMin_apply_ground hg
  | @ctx f as bs i hstep hrest ih =>
      intro j
      by_cases hj : j = i
      · rw [hj]; exact ih (hg i)
      · rw [← hrest j hj]; exact hg j

/-- `StepStar (R_can S n)` preserves groundness. -/
theorem StepStar.preserves_ground {n : Nat} {s t : Term S}
    (h : StepStar (R_can S n) s t) (hg : Term.IsGround s) : Term.IsGround t := by
  induction h with
  | refl => exact hg
  | tail _ hstep ih => exact Step.preserves_ground hstep ih

/-- **Enumeration completeness for ground inputs** (induct-on-size
auxiliary): for ground `t`, R_can-irreducibility wrt `R_can S (size t)`
implies `t ∈ I_can S (size t)`. The general `ground_irreducible_in_I_can`
follows by `I_can_subset` + downcasting irreducibility via `R_can_subset`. -/
private theorem ground_irreducible_in_I_can_at_size : ∀ (t : Term S),
    Term.IsGround t →
    (∀ u, ¬ Step (R_can S (Term.size t)) t u) →
    t ∈ I_can S (Term.size t) := by
  intro t
  induction t with
  | var v => intro hg _; exact hg.elim
  | node f args ih =>
      intro hg hirr
      have hm_pos : 0 < Term.size (Term.node f args) := Term.size_pos _
      -- IH: each subterm is in I_can at its own size; lift to I_can S (size t - 1).
      have hargs_mem : ∀ i, args i ∈ I_can S (Term.size (Term.node f args) - 1) := by
        intro i
        have hsi_lt : Term.size (args i) < Term.size (Term.node f args) :=
          Term.size_arg_lt f args i
        have hg_i : Term.IsGround (args i) := hg i
        have hirr_i : ∀ u, ¬ Step (R_can S (Term.size (args i))) (args i) u := by
          intro u hstep
          have hstep_lift : Step (R_can S (Term.size (Term.node f args))) (args i) u :=
            Step.lift (R_can_subset (le_of_lt hsi_lt)) hstep
          exact Step.irreducible_arg hirr u hstep_lift
        exact I_can_subset (by omega) (ih i hg_i hirr_i)
      -- Enumeration witness.
      have hen : Term.node f args ∈
          termsFromIrreducible S (I_can S (Term.size (Term.node f args) - 1))
                                 (Term.size (Term.node f args)) := by
        rw [mem_termsFromIrreducible]
        refine ⟨rfl, ?_⟩
        intro f' args' heq i
        injection heq with hf ha
        subst hf
        have ha' : args' = args := eq_of_heq ha
        subst ha'
        exact hargs_mem i
      have hcan : Canonical (Term.node f args) := canonical_of_ground hg
      have hnsp : ¬ simplifiesWith (R_can S (Term.size (Term.node f args) - 1))
                                    (Term.node f args) := by
        apply not_simplifiesWith_of_irreducible
        intro u hstep
        exact hirr u (Step.lift (R_can_subset (by omega)) hstep)
      -- smtMin t = t: otherwise the rule (t, smtMin t) ∈ R_can S (size t) would fire on t.
      have hsmt : smtMin (Term.node f args) = Term.node f args := by
        by_contra hne
        have hrule : (Term.node f args, smtMin (Term.node f args)) ∈
                      R_can S (Term.size (Term.node f args)) :=
          mem_R_can_intro (le_refl _) hen hcan hnsp hne
        exact hirr _ (Step.root_id hrule)
      -- Assemble: t ∈ I_can S (size t).
      have h_eq : Term.size (Term.node f args) = (Term.size (Term.node f args) - 1) + 1 := by
        omega
      rw [h_eq, I_can]
      apply Finset.mem_union_right
      rw [Finset.mem_filter]
      refine ⟨?_, hcan, hnsp, hsmt⟩
      rw [← h_eq]
      exact hen

/-- **Enumeration completeness** for ground inputs: every R_can-irreducible
ground term of size ≤ n is in `I_can S n`.

Proof: by `ground_irreducible_in_I_can_at_size` we get `t ∈ I_can S (size t)`,
which by `I_can_subset` lifts to `t ∈ I_can S n`. The premise downcast
uses `R_can_subset` (rules in a smaller bound are a subset of those in a
larger bound, so non-stepping wrt the larger bound implies non-stepping
wrt the smaller). -/
theorem ground_irreducible_in_I_can {n : Nat} {t : Term S}
    (hsize : Term.size t ≤ n)
    (hground : Term.IsGround t)
    (hirr : ∀ u, ¬ Step (R_can S n) t u) : t ∈ I_can S n := by
  apply I_can_subset hsize
  apply ground_irreducible_in_I_can_at_size t hground
  intro u hstep
  exact hirr u (Step.lift (R_can_subset hsize) hstep)

/-- **Algorithm completeness theorem**: every ground R_can-irreducible
term `t` of size ≤ n has both
* a *substitution pre-image* in `I_can` — some `m ∈ I_can` with
  `apply σ m = t`, and
* a *canonical class representative* in `I_can` — some `c ∈ I_can`
  with `c ≈ₜ t`.

For ground `t`, both anchors are `t` itself (using `Subst.id` and
`apply_id` for the source instantiation, and `equiv_refl` for the
destination equivalence). -/
theorem I_can_complete_subst {n : Nat} {t : Term S}
    (hground : Term.IsGround t)
    (hsize : Term.size t ≤ n)
    (hirr : ∀ u, ¬ Step (R_can S n) t u) :
    (∃ m σ, m ∈ I_can S n ∧ apply σ m = t) ∧
    (∃ c, c ∈ I_can S n ∧ c ≈ₜ t) := by
  have ht_mem : t ∈ I_can S n := ground_irreducible_in_I_can hsize hground hirr
  exact ⟨⟨t, Subst.id, ht_mem, apply_id t⟩, ⟨t, ht_mem, equiv_refl t⟩⟩

namespace ExtStep

theorem equiv_of {n : Nat} {s t : Term S} (hst : ExtStep n s t) : s ≈ₜ t := by
  cases hst with
  | rule h => exact Step.equiv_of (fun hlr => rule_equiv_can hlr) h
  | class_lookup _ _ _ h_eq => exact h_eq

end ExtStep

namespace ExtStepStar

theorem equiv_of {n : Nat} {s t : Term S} (hst : ExtStepStar n s t) :
    s ≈ₜ t := by
  induction hst with
  | refl => exact equiv_refl _
  | tail _ hlast ih => exact equiv_trans ih (ExtStep.equiv_of hlast)

end ExtStepStar

/-- Lift a `StepStar (R_can S n)` path to an `ExtStepStar n` path. -/
theorem StepStar.toExtStepStar {n : Nat} {s t : Term S}
    (h : StepStar (R_can S n) s t) : ExtStepStar (S := S) n s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih =>
      exact Relation.ReflTransGen.tail ih (ExtStep.rule hlast)

/-- Rewriting under `R_can` doesn't grow size. -/
theorem StepStar.size_le {n : Nat} {s t : Term S}
    (h : StepStar (R_can S n) s t) : Term.size t ≤ Term.size s := by
  rcases StepStar.kbo_of (fun hlr => rule_kbo_can hlr) h with heq | hlt
  · rw [heq]
  · exact kbo_size_le hlt

/-- **Common normal form theorem**: for any pair of ground,
`≈ₜ`-equivalent terms of size ≤ n, both reach **the same** term
`c ∈ I_can S n` via the algorithm's operational steps.

Proof: Phase 1 reaches `R_can`-irreducibles `s', t'` (still ground by
`StepStar.preserves_ground`) with `s' ≈ₜ t'`. By
`ground_irreducible_in_I_can`, both `s'` and `t'` are in `I_can S n`.
By `I_can_unique_per_class`, `s' = t'` — that's the common normal
form, reached by Phase-1 rule rewriting alone. -/
theorem complete_common_normal_form (n : Nat) {s t : Term S}
    (hs_ground : Term.IsGround s) (ht_ground : Term.IsGround t)
    (hs_size : Term.size s ≤ n) (ht_size : Term.size t ≤ n) (hst : s ≈ₜ t) :
    ∃ c, c ∈ I_can S n ∧
         ExtStepStar (S := S) n s c ∧ ExtStepStar (S := S) n t c := by
  rcases reaches_normal_form_can n s with ⟨s', hss', hs_irr⟩
  rcases reaches_normal_form_can n t with ⟨t', htt', ht_irr⟩
  -- Groundness and size are preserved by R_can-rewriting.
  have hs'_ground : Term.IsGround s' := StepStar.preserves_ground hss' hs_ground
  have ht'_ground : Term.IsGround t' := StepStar.preserves_ground htt' ht_ground
  have hs'_size : Term.size s' ≤ n := le_trans (StepStar.size_le hss') hs_size
  have ht'_size : Term.size t' ≤ n := le_trans (StepStar.size_le htt') ht_size
  -- Soundness: s ≈ₜ s', t ≈ₜ t', so s' ≈ₜ t'.
  have hs_eq : s ≈ₜ s' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) hss'
  have ht_eq : t ≈ₜ t' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) htt'
  have hst' : s' ≈ₜ t' :=
    equiv_trans (equiv_symm hs_eq) (equiv_trans hst ht_eq)
  -- s' and t' are both in I_can (ground irreducible).
  have hs'_mem : s' ∈ I_can S n := ground_irreducible_in_I_can hs'_size hs'_ground hs_irr
  have ht'_mem : t' ∈ I_can S n := ground_irreducible_in_I_can ht'_size ht'_ground ht_irr
  -- Uniqueness: s' = t' since both are ground I_can members in the same ≈ₜ-class.
  have hs't' : s' = t' :=
    I_can_unique_per_class hs'_ground ht'_ground hs'_mem ht'_mem hst'
  refine ⟨s', hs'_mem, hss'.toExtStepStar, ?_⟩
  rw [hs't']
  exact htt'.toExtStepStar

end EnumRules
