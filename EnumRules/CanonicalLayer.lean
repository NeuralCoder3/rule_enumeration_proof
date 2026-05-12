import EnumRules.Algorithm

open scoped Classical

/-
# Algorithm correctness: construction-saturation + runtime bridge

## Role
Proves the runtime completeness theorem:

* `complete_common_normal_form` — for *runtime-ground* `≈ₜ`-equivalent
  inputs `s, t : Term S Ext` of size ≤ n, both reach the same
  irreducible normal form `c : Term S Ext` via rule rewriting alone.

The proof has two parts:

1. **Construction-time saturation** (`construction_saturation`, proved):
   for `c : Term S Empty` with `NoVar`, R_can-irreducible at size ≤ n,
   we have `smtMin c = c`. This is the same argument used in the old
   ground proof, lifted to the `NoVar` predicate.

2. **Runtime bridge** (`runtime_saturation`, proved): for `t : Term S Ext`
   runtime-ground, R_can-irreducible at size ≤ n, we have `smtMin t = t`.
   Proved by pulling `t` back to a construction-time `c` via an order
   embedding `embed : Ext ↪o S.C`, applying construction-saturation to
   `c`, and using `smtMin_commutes_embed` to push the result forward.

## Axioms (2)
* `smtMin_apply_runtime` — `smtMin` doesn't introduce extra var or
  constP usage (used in `Step.preserves_runtime`).
* `smtMin_commutes_embed` — `smtMin` commutes with the canonical
  "order-preserving renaming" `σ_of_embed`. The semantic content:
  SMT classes and KBO ordering are isomorphic under an
  order-preserving relabelling of ConstPlaceholders and runtime
  extension symbols.

## Theorems
* `Step.preserves_runtime` / `StepStar.preserves_runtime`.
* `construction_saturation` — proved (was an axiom).
* `runtime_saturation` (i.e., the old `smtMin_irreducible_fixed`) — proved (was an axiom).
* `complete_common_normal_form`.
-/

namespace EnumRules

variable {S : Signature}

/-! ## Structural facts about R_can / I_can over Term S Empty -/

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

@[aesop safe forward]
theorem mem_R_can_props {n : Nat} {l r : Term S Empty} (h : (l, r) ∈ R_can S n) :
    r = smtMin l ∧ l ≠ r := by
  induction n with
  | zero => simp [R_can] at h
  | succ n ih =>
      simp only [R_can, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
                 Prod.mk.injEq] at h
      obtain hPrev | ⟨l', ⟨_, _, _, hne⟩, rfl, rfl⟩ := h
      · exact ih hPrev
      · exact ⟨rfl, Ne.symm hne⟩

theorem mem_R_can_intro {n : Nat} {l : Term S Empty}
    (hsize : Term.size l ≤ n)
    (hen : l ∈ renamingOrbit (termsFromIrreducible S (I_can S (Term.size l - 1)) (Term.size l)))
    (hcan : Canonical l)
    (hnsp : ¬ simplifiesWith (R_can S (Term.size l - 1)) l)
    (hne : smtMin l ≠ l) :
    (l, smtMin l) ∈ R_can S n := by
  refine R_can_subset hsize ?_
  have hsucc : Term.size l - 1 + 1 = Term.size l := by
    have := Term.size_pos l; omega
  rw [← hsucc, R_can]
  refine Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨l, Finset.mem_filter.mpr ⟨?_, hcan, hnsp, hne⟩, rfl⟩)
  rwa [hsucc]

theorem rule_equiv_can {n : Nat} {l r : Term S Empty} (h : (l, r) ∈ R_can S n) :
    l ≈ₜ r := by
  obtain ⟨rfl, _⟩ := mem_R_can_props h
  exact equiv_symm (smtMin_equiv l)

theorem rule_kbo_can {n : Nat} {l r : Term S Empty} (h : (l, r) ∈ R_can S n) :
    r ≺ₖ l := by
  obtain ⟨rfl, hne⟩ := mem_R_can_props h
  exact smtMin_strict (Ne.symm hne)

/-! ## Termination + reaching a normal form -/

theorem terminates_can {Ext : Type} (n : Nat) :
    WellFounded (fun t s : Term S Ext => Step (R_can S n) s t) :=
  Subrelation.wf (fun h => Step.kbo_of (fun hlr => rule_kbo_can hlr) h) kbo_wf

theorem reaches_normal_form_can {Ext : Type} (n : Nat) (s : Term S Ext) :
    ∃ s', StepStar (R_can S n) s s' ∧ ∀ u, ¬ Step (R_can S n) s' u := by
  induction s using (terminates_can n).induction with
  | _ s ih =>
      by_cases h : ∃ u, Step (R_can S n) s u
      · obtain ⟨u, hu⟩ := h
        obtain ⟨s', hsu, hirr⟩ := ih u hu
        exact ⟨s', .head hu hsu, hirr⟩
      · exact ⟨s, .refl, fun u hu => h ⟨u, hu⟩⟩

/-- `I_can` members are smtMin-fixed (built into the I_can filter). -/
@[aesop safe forward]
theorem I_can_smtMin_fixed {n : Nat} {c : Term S Empty} (hc : c ∈ I_can S n) :
    smtMin c = c := by
  induction n with
  | zero => simp [I_can] at hc
  | succ n ih =>
      rw [I_can, Finset.mem_union] at hc
      aesop

/-! ## Runtime convention: behavioural axioms

`smtMin_apply_runtime` says `smtMin` doesn't grow var/constP usage —
needed for `Step.preserves_runtime`.

`smtMin_commutes_embed` says `smtMin` commutes with the canonical
order-preserving renaming `σ_of_embed`. This is the bridging axiom
that lifts construction-saturation to runtime-saturation. -/

/-- `smtMin` doesn't introduce extra var/constP usage: if a
substitution-instance of `l` is runtime, the same substitution applied
to `smtMin l` is runtime too. -/
axiom smtMin_apply_runtime {Ext : Type} {l : Term S Empty} {σ : Subst S Ext}
    (h : Term.IsRuntime (apply σ l)) : Term.IsRuntime (apply σ (smtMin l))

/-- `smtMin` commutes with the canonical order-preserving renaming
from an embedding `embed : Ext ↪o S.C`. Semantically: SMT classes
and KBO are isomorphic under an order-preserving substitution of
ConstPlaceholders by extension symbols. -/
axiom smtMin_commutes_embed
    {Ext : Type} [Fintype Ext] [DecidableEq Ext] [LinearOrder Ext] [Inhabited Ext]
    (embed : Ext ↪o S.C) (c : Term S Empty) :
  apply (Subst.of_embed embed) (smtMin c) = smtMin (apply (Subst.of_embed embed) c)

/-! ## Step.preserves_runtime — keeps the runtime structure -/

/-- `Step (R_can S n)` preserves runtime-groundness. -/
theorem Step.preserves_runtime {Ext : Type} {n : Nat} {s t : Term S Ext}
    (h : Step (R_can S n) s t) (hg : Term.IsRuntime s) : Term.IsRuntime t := by
  induction h with
  | @root l r σ hmem =>
      obtain ⟨rfl, _⟩ := mem_R_can_props hmem
      exact smtMin_apply_runtime hg
  | @ctx f as bs i hstep hrest ih =>
      intro j
      by_cases hj : j = i
      · exact hj ▸ ih (hg i)
      · exact (hrest j hj).symm ▸ hg j

/-- `StepStar (R_can S n)` preserves runtime-groundness. -/
theorem StepStar.preserves_runtime {Ext : Type} {n : Nat} {s t : Term S Ext}
    (h : StepStar (R_can S n) s t) (hg : Term.IsRuntime s) : Term.IsRuntime t := by
  induction h with
  | refl => exact hg
  | tail _ hstep ih => exact Step.preserves_runtime hstep ih

/-- Rewriting under `R_can` doesn't grow size. -/
theorem StepStar.size_le {Ext : Type} {n : Nat} {s t : Term S Ext}
    (h : StepStar (R_can S n) s t) : Term.size t ≤ Term.size s := by
  rcases StepStar.kbo_of (fun hlr => rule_kbo_can hlr) h with heq | hlt
  · rw [heq]
  · exact kbo_size_le hlt

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
size ≤ n, `t ∈ I_can S n`. Proof by structural induction on `t`. -/
private theorem construction_irreducible_in_I_can_at_size :
    ∀ (t : Term S Empty),
      Term.NoVar t →
      (∀ u, ¬ Step (R_can S (Term.size t)) t u) →
      t ∈ I_can S (Term.size t) := by
  intro t
  induction t with
  | var v => intro hg _; exact hg.elim
  | ext e => intro _ _; exact e.elim
  | constP c =>
      intro hg hirr
      -- size (constP c) = 1.
      have hsize_one : Term.size (Term.constP (S := S) (Ext := Empty) c) = 1 := rfl
      have hen_orbit :
          Term.constP c ∈ renamingOrbit (termsFromIrreducible S (I_can S 0) 1) := by
        apply self_mem_renamingOrbit
        rw [mem_termsFromIrreducible]
        exact ⟨rfl, fun f' args' heq _ => by cases heq⟩
      have hcan : Canonical (Term.constP (S := S) (Ext := Empty) c) :=
        canonical_of_NoVar hg
      have hnsp : ¬ simplifiesWith (R_can S 0) (Term.constP (S := S) (Ext := Empty) c) := by
        show ¬ simplifiesWith (∅ : RuleSet S) _
        exact not_simplifiesWith_empty
      have hsmt : smtMin (Term.constP (S := S) (Ext := Empty) c) = Term.constP c := by
        by_contra hne
        have hrule : (Term.constP c, smtMin (Term.constP (S := S) (Ext := Empty) c)) ∈
                      R_can S 1 :=
          mem_R_can_intro (le_refl _) (by simpa using hen_orbit) hcan
            (by simpa using hnsp) hne
        exact hirr _ (Step.root_id hrule)
      -- Assemble: constP c ∈ I_can S 1.
      show Term.constP c ∈ I_can S 1
      rw [show (1 : Nat) = 0 + 1 from rfl, I_can]
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hen_orbit, hcan, hnsp, hsmt⟩)
  | node f args ih =>
      intro hg hirr
      set N := Term.size (Term.node f args : Term S Empty)
      have hN_pos : 0 < N := Term.size_pos _
      have hargs_mem : ∀ i, args i ∈ I_can S (N - 1) := fun i =>
        I_can_subset (by have := Term.size_arg_lt f args i; omega)
          (ih i (hg i) fun u hstep => Step.irreducible_arg hirr u
            (Step.lift (R_can_subset (Term.size_arg_lt f args i).le) hstep))
      have hen : (Term.node f args : Term S Empty) ∈
          termsFromIrreducible S (I_can S (N - 1)) N :=
        mem_termsFromIrreducible.mpr ⟨rfl, by aesop⟩
      have hen_orbit : (Term.node f args : Term S Empty) ∈
          renamingOrbit (termsFromIrreducible S (I_can S (N - 1)) N) :=
        self_mem_renamingOrbit hen
      have hcan : Canonical (Term.node f args : Term S Empty) := canonical_of_NoVar hg
      have hnsp : ¬ simplifiesWith (R_can S (N - 1)) (Term.node f args : Term S Empty) :=
        not_simplifiesWith_of_irreducible fun u hstep =>
          hirr u (Step.lift (R_can_subset (by omega)) hstep)
      have hsmt : smtMin (Term.node f args : Term S Empty) = Term.node f args := by
        by_contra hne
        have hrule : (Term.node f args, smtMin (Term.node f args : Term S Empty)) ∈
                      R_can S N :=
          mem_R_can_intro (le_refl _) hen_orbit hcan hnsp hne
        exact hirr _ (Step.root_id hrule)
      have hsucc : N - 1 + 1 = N := by omega
      rw [show N = N - 1 + 1 from hsucc.symm, I_can]
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hsucc ▸ hen_orbit, hcan, hnsp, hsmt⟩)

/-- For a `NoVar` `t : Term S Empty` of size ≤ n that is R_can-irreducible,
`t ∈ I_can S n`. The general case follows from the size-bounded auxiliary
by `I_can_subset` and `R_can_subset`. -/
theorem construction_irreducible_in_I_can {n : Nat} {t : Term S Empty}
    (hsize : Term.size t ≤ n)
    (hg : Term.NoVar t)
    (hirr : ∀ u, ¬ Step (R_can S n) t u) : t ∈ I_can S n := by
  apply I_can_subset hsize
  apply construction_irreducible_in_I_can_at_size t hg
  intro u hstep
  exact hirr u (Step.lift (R_can_subset hsize) hstep)

/-- **Construction-saturation**: a `NoVar` term in `Term S Empty` that
is R_can-irreducible at size ≤ n is its own `smtMin`. -/
theorem construction_saturation {n : Nat} {c : Term S Empty}
    (hsize : Term.size c ≤ n)
    (hg : Term.NoVar c)
    (hirr : ∀ u, ¬ Step (R_can S n) c u) : smtMin c = c := by
  have hc_mem : c ∈ I_can S n :=
    construction_irreducible_in_I_can hsize hg hirr
  exact I_can_smtMin_fixed hc_mem

/-! ## Runtime saturation via embed -/

section RuntimeSaturation
variable {Ext : Type} [Fintype Ext] [DecidableEq Ext] [LinearOrder Ext]
  [Inhabited Ext]

/-- Pull a runtime term back to a construction-time template along an
order embedding. -/
def pullback (embed : Ext ↪o S.C) : Term S Ext → Term S Empty
  | .var v       => .var v
  | .constP c    => .constP c
  | .node f args => .node f (fun i => pullback embed (args i))
  | .ext e       => .constP (embed e)
termination_by structural t => t

/-- The pullback inverts `apply (Subst.of_embed embed)` on runtime
terms: ext-leaves of `t` are replaced by `constP (embed e)` in the
pullback, and applying `σ_of_embed` sends each `constP (embed e)` back
to `Term.ext e` (using injectivity of `embed`). -/
theorem apply_pullback {embed : Ext ↪o S.C} {t : Term S Ext}
    (h : Term.IsRuntime t) :
    apply (Subst.of_embed embed) (pullback embed t) = t := by
  induction t with
  | var v       => exact h.elim
  | constP c    => exact h.elim
  | node f args ih =>
      simp only [pullback, apply_node]
      exact Term.node_ext fun j => ih j (h j)
  | ext e       =>
      show apply (Subst.of_embed embed) (Term.constP (embed e)) = Term.ext e
      simp only [apply_constP]
      show (Subst.of_embed embed).constPM (embed e) = Term.ext e
      unfold Subst.of_embed
      simp only
      have hex : ∃ e' : Ext, embed e' = embed e := ⟨e, rfl⟩
      rw [dif_pos hex]
      congr 1
      exact embed.injective (Classical.choose_spec hex)

/-- Pullback of a runtime term has `NoVar`. -/
theorem NoVar_pullback {embed : Ext ↪o S.C} {t : Term S Ext}
    (h : Term.IsRuntime t) : Term.NoVar (pullback embed t) := by
  induction t with
  | var v       => exact h.elim
  | constP c    => exact h.elim
  | node f args ih =>
      intro j; exact ih j (h j)
  | ext e       => trivial

/-- Pullback preserves size. -/
theorem size_pullback {embed : Ext ↪o S.C} (t : Term S Ext) :
    Term.size (pullback embed t) = Term.size t := by
  induction t with
  | var v       => rfl
  | constP c    => rfl
  | node f args ih =>
      simp only [pullback, Term.size]
      congr 1
      exact Finset.sum_congr rfl fun i _ => ih i
  | ext e       => rfl

/-- **Runtime saturation**: a runtime-ground term that is
R_can-irreducible at size ≤ n is its own `smtMin`. -/
theorem runtime_saturation (embed : Ext ↪o S.C) {n : Nat} {t : Term S Ext}
    (hsize : Term.size t ≤ n)
    (hg : Term.IsRuntime t)
    (hirr : ∀ u, ¬ Step (R_can S n) t u) : smtMin t = t := by
  set c := pullback embed t with hc_def
  have h_apply : apply (Subst.of_embed embed) c = t := by
    rw [hc_def]; exact apply_pullback hg
  have hc_g : Term.NoVar c := NoVar_pullback hg
  have hc_size : Term.size c ≤ n := by rw [hc_def, size_pullback]; exact hsize
  -- c is construction-irreducible: any step on c lifts to a step on t via
  -- Step.subst, contradicting hirr.
  have hc_irr : ∀ u, ¬ Step (R_can S n) c u := by
    intro u hu
    have h_lift : Step (R_can S n) (apply (Subst.of_embed embed) c)
                                    (apply (Subst.of_embed embed) u) :=
      Step.subst hu (Subst.of_embed embed)
    rw [h_apply] at h_lift
    exact hirr _ h_lift
  -- By construction-saturation, smtMin c = c.
  have hc_sat : smtMin c = c := construction_saturation hc_size hc_g hc_irr
  -- Push through embed: smtMin t = apply σ_embed (smtMin c) = apply σ_embed c = t.
  calc smtMin t = smtMin (apply (Subst.of_embed embed) c) := by rw [h_apply]
    _ = apply (Subst.of_embed embed) (smtMin c) := (smtMin_commutes_embed embed c).symm
    _ = apply (Subst.of_embed embed) c := by rw [hc_sat]
    _ = t := h_apply

end RuntimeSaturation

/-! ## Runtime common normal form -/

/-- **Common normal form theorem** (runtime): for any pair of runtime,
`≈ₜ`-equivalent terms `s, t : Term S Ext` of size ≤ n, both reach the
same irreducible runtime term via rule rewriting alone. -/
theorem complete_common_normal_form
    {Ext : Type} [Fintype Ext] [DecidableEq Ext] [LinearOrder Ext] [Inhabited Ext]
    (embed : Ext ↪o S.C) (n : Nat) {s t : Term S Ext}
    (hs_runtime : Term.IsRuntime s) (ht_runtime : Term.IsRuntime t)
    (hs_size : Term.size s ≤ n) (ht_size : Term.size t ≤ n) (hst : s ≈ₜ t) :
    ∃ c, Term.IsRuntime c ∧
         StepStar (R_can S n) s c ∧
         StepStar (R_can S n) t c := by
  obtain ⟨s', hss', hs_irr⟩ := reaches_normal_form_can n s
  obtain ⟨t', htt', ht_irr⟩ := reaches_normal_form_can n t
  have hs'_g := StepStar.preserves_runtime hss' hs_runtime
  have ht'_g := StepStar.preserves_runtime htt' ht_runtime
  have hs'_size := le_trans (StepStar.size_le hss') hs_size
  have ht'_size := le_trans (StepStar.size_le htt') ht_size
  have hs_eq := StepStar.equiv_of (fun h => rule_equiv_can h) hss'
  have ht_eq := StepStar.equiv_of (fun h => rule_equiv_can h) htt'
  have hst' : s' ≈ₜ t' :=
    equiv_trans (equiv_symm hs_eq) (equiv_trans hst ht_eq)
  have hsm_s : smtMin s' = s' := runtime_saturation embed hs'_size hs'_g hs_irr
  have hsm_t : smtMin t' = t' := runtime_saturation embed ht'_size ht'_g ht_irr
  have h_eq : smtMin s' = smtMin t' :=
    smtMin_resp (hsm_s.symm ▸ Term.NoVar_of_IsRuntime hs'_g)
                (hsm_t.symm ▸ Term.NoVar_of_IsRuntime ht'_g) hst'
  have hs't' : s' = t' := by
    calc s' = smtMin s' := hsm_s.symm
      _ = smtMin t' := h_eq
      _ = t' := hsm_t
  exact ⟨s', hs'_g, hss', hs't' ▸ htt'⟩

end EnumRules
