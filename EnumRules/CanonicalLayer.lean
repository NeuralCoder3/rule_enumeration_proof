import EnumRules.Algorithm

open scoped Classical

/-
# Canonical-filtered algorithm + completeness modulo `≈ₜ`

## Role
Defines `R_can S n` and `I_can S n` (canonical-filtered rule and
irreducible sets), proves the universal completeness theorem:

```
complete_can :
  s ≈ₜ t →
  ∃ s' t', s →* s' ∧ t →* t' ∧ s' ≈ₜ t' ∧ smtMin s' = smtMin t'
```

For any signature, `≈ₜ`-equivalent inputs reach `R_can`-irreducibles
that are themselves `≈ₜ`-equivalent. `smtMin` agreement (Phase 2 of
the algorithm) follows from `smtMin_resp`.

## Axioms (3)
* `Canonical : Term S → Prop` opaque, no behavioural axioms.
  The `Canonical` filter doesn't appear in `complete_can` (universal
  completeness). It does appear in the *common normal form* result
  via the two axioms below.
* `exists_canonical_alpha_rep` — every term has a canonical
  α-representative. Property of the `Canonical` filter: it picks one
  member from each α-orbit.
* `canonical_irreducible_in_I_can` — every canonical, R_can-irreducible
  term of size ≤ n is in `I_can S n`. Enumeration completeness of the
  algorithm's saturating construction.

## Optional non-AC extension
For signatures where `≈ₜ`-classes coincide with α-classes
(non-commutative, pure-commutative), `complete_modulo_renaming`
strengthens the conclusion to α-equivalent normal forms when the
**inputs** are α-equivalent. It is *not* available for arbitrary
`≈ₜ`-equivalent inputs (that would require AC-failing axioms).
-/

namespace EnumRules

variable {S : Signature}

opaque Canonical : Term S → Prop

/-! ## Canonical-filtered rule and irreducible sets -/

mutual
  noncomputable def R_can (S : Signature) : Nat → RuleSet S
    | 0     => ∅
    | n + 1 => R_can S n ∪ (
        (termsFromIrreducible S (I_can S n) (n + 1)).filter (fun l =>
          Canonical l ∧ ¬ simplifiesWith (R_can S n) l ∧ smtMin l ≠ l)
          |>.image (fun l => (l, smtMin l)))

  noncomputable def I_can (S : Signature) : Nat → Finset (Term S)
    | 0     => ∅
    | n + 1 => I_can S n ∪ (
        (termsFromIrreducible S (I_can S n) (n + 1)).filter (fun l =>
          Canonical l ∧ ¬ simplifiesWith (R_can S n) l ∧ smtMin l = l))
end

theorem R_can_subset {S : Signature} {m n : Nat} (h : m ≤ n) :
    R_can S m ⊆ R_can S n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => intro x hx; rw [R_can]; exact Finset.mem_union_left _ (ih hx)

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

/-! ## Universal completeness (any signature, including AC)

The algorithm produces:
1. **Phase 1**: a normal form `s'` with `s ≈ₜ s'` (rewriting alone).
2. **Phase 2**: `smtMin s'`, which by `smtMin_resp` equals `smtMin s` —
   a canonical representative of the `≈ₜ`-class.

For `s ≈ₜ t`, Phase 1 produces normal forms `s', t'` with
`s' ≈ₜ s ≈ₜ t ≈ₜ t'`, hence `s' ≈ₜ t'`. Phase 2 (lookup) uses
`smtMin_resp` to compare: `smtMin s' = smtMin t'`. -/
theorem complete_can (n : Nat) {s t : Term S} (hst : s ≈ₜ t) :
    ∃ s' t',
      StepStar (R_can S n) s s' ∧ StepStar (R_can S n) t t' ∧
      (∀ u, ¬ Step (R_can S n) s' u) ∧ (∀ u, ¬ Step (R_can S n) t' u) ∧
      s ≈ₜ s' ∧ t ≈ₜ t' ∧
      s' ≈ₜ t' ∧
      smtMin s' = smtMin t' := by
  rcases reaches_normal_form_can n s with ⟨s', hs', hs_irr⟩
  rcases reaches_normal_form_can n t with ⟨t', ht', ht_irr⟩
  have hs_eq : s ≈ₜ s' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) hs'
  have ht_eq : t ≈ₜ t' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) ht'
  have hst' : s' ≈ₜ t' :=
    equiv_trans (equiv_symm hs_eq) (equiv_trans hst ht_eq)
  exact ⟨s', t', hs', ht', hs_irr, ht_irr, hs_eq, ht_eq, hst', smtMin_resp hst'⟩

/-! ## Optional non-AC extension: α-equivalent inputs

For α-equivalent inputs, the rewrite path is α-equivariant
(`Step.subst`), and the result is α-equivalent. This holds *without*
any AC-failing axiom — only relies on substitution-stability of
rewriting (`Step.subst` from `Rewrite.lean`).

Note this requires the **inputs** to be α-equivalent. Two `≈ₜ`-equivalent
inputs that are not α-equivalent (the AC case) cannot be related this way. -/

theorem IsRenaming.preserves_step_irreducible {R : RuleSet S} {s' : Term S}
    {ρ : Subst S} (hρ : IsRenaming ρ) (hirr : ∀ u, ¬ Step R s' u) :
    ∀ u, ¬ Step R (apply ρ s') u :=
  hρ.preserves_irreducible (fun h τ => Step.subst h τ) hirr

theorem complete_modulo_renaming (n : Nat) {s t : Term S} (h : s ≈ᵅ t) :
    ∃ s' t', StepStar (R_can S n) s s' ∧
             (∀ u, ¬ Step (R_can S n) s' u) ∧
             StepStar (R_can S n) t t' ∧
             (∀ u, ¬ Step (R_can S n) t' u) ∧
             s' ≈ᵅ t' := by
  rcases h with ⟨ρ, hρ_ren, hρ⟩
  rcases reaches_normal_form_can n s with ⟨s', hss', hs_irr⟩
  exact ⟨s', apply ρ s', hss', hs_irr,
    hρ ▸ StepStar.subst hss' ρ,
    hρ_ren.preserves_step_irreducible hs_irr,
    ρ, hρ_ren, rfl⟩

/-! ## Extended rewriting and common normal form

The algorithm's operational steps are exactly three — none invokes
`smtMin` at runtime; the SMT work is all done at enumeration time when
constructing the rule set `R_can` and the irreducible groups stored
inside `I_can`:

1. **Rule rewriting** (`Step R_can`) — fire a synthesised rule under
   any substitution. Phase 1.
2. **Equivalence-class step** (`ExtStep.class_lookup`) — replace `t`
   with a stored canonical class member `c ∈ I_can` such that `t ≈ₜ c`.
   This is the *only* equivalence-class operation the algorithm does
   at runtime. The `c ≈ₜ t` decision is the SMT check made at
   enumeration time and stored in the group structure.
3. **Renaming** (`ExtStep.rename_eq`) — apply a `≈ₜ`-preserving renaming
   substitution.

Every step preserves `≈ₜ` (the `class_lookup` step lands in the same
class by hypothesis; rules and renamings are sound by construction).

A `smtMin`-step is **not** included — `smtMin t` is recovered as the
*unique* representative `c ∈ I_can` with `c ≈ₜ t`, found via `class_lookup`. -/

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

/-- `I_can` has **at most one** representative per `≈ₜ`-class:
two `I_can` members in the same class are equal, because each is its
own `smtMin` and `smtMin` respects `≈ₜ`. -/
theorem I_can_unique_per_class {n : Nat} {c d : Term S}
    (hc : c ∈ I_can S n) (hd : d ∈ I_can S n) (h : c ≈ₜ d) : c = d := by
  have h_eq : smtMin c = smtMin d := smtMin_resp h
  rw [I_can_smtMin_fixed hc, I_can_smtMin_fixed hd] at h_eq
  exact h_eq

/-! ## Canonical α-representatives and enumeration completeness

`I_can_complete_subst` was previously an axiom. We now derive it from
two more elementary facts plus the renaming-stability of `≈ₜ`
(`equiv_rename`, in `Subst.lean`):

* **Existence of a canonical α-rep** — every term has a `Canonical`
  α-representative. This is a property of the `Canonical` filter
  (every α-orbit contains one).
* **Enumeration completeness for I_can** — every canonical,
  R_can-irreducible term of size ≤ n is stored in `I_can S n`. This
  holds by the algorithm's saturating construction: the term is
  enumerated in `termsFromIrreducible` at its size, passes the
  Canonical and ¬simplifies filters by hypothesis, and has
  `smtMin c = c` (otherwise the rule `(c, smtMin c)` would be in
  `R_can` and `c` would not be irreducible). -/

/-- **Canonical α-rep existence**: every term has a canonical term
related to it via a renaming. -/
axiom exists_canonical_alpha_rep (t : Term S) :
    ∃ (c : Term S) (ρ : Subst S),
      IsRenaming ρ ∧ Canonical c ∧ apply ρ c = t

/-- **Enumeration completeness for `I_can`**: every canonical,
R_can-irreducible term of size ≤ n is stored in `I_can S n`. -/
axiom canonical_irreducible_in_I_can {n : Nat} {c : Term S}
    (hsize : Term.size c ≤ n)
    (hcan : Canonical c)
    (hirr : ∀ u, ¬ Step (R_can S n) c u) : c ∈ I_can S n

/-- **Algorithm completeness theorem**: every R_can-irreducible term `t`
of size ≤ n has both
* a *substitution pre-image* in `I_can` — some `m ∈ I_can` with
  `apply σ m = t` — meaning `t` is structurally an instance of a
  stored canonical, *and*
* a *canonical class representative* in `I_can` — some `c ∈ I_can`
  with `c ≈ₜ t`.

Proof sketch: by `exists_canonical_alpha_rep`, `t` has a canonical
α-rep `c` with `apply ρ c = t` for renaming ρ. Renaming preserves
size (`apply_renaming_size`) and irreducibility transfers backwards
along ρ via `IsRenaming.flip` + `preserves_step_irreducible`, so `c`
is canonical, R_can-irreducible, and of size ≤ n — hence
`c ∈ I_can S n` by `canonical_irreducible_in_I_can`. The source
anchor takes `m = c, σ = ρ`; the destination takes the same `c`,
with `c ≈ₜ t` from `equiv_rename`. -/
theorem I_can_complete_subst {n : Nat} {t : Term S}
    (hsize : Term.size t ≤ n)
    (hirr : ∀ u, ¬ Step (R_can S n) t u) :
    (∃ m σ, m ∈ I_can S n ∧ apply σ m = t) ∧
    (∃ c, c ∈ I_can S n ∧ c ≈ₜ t) := by
  rcases exists_canonical_alpha_rep t with ⟨c, ρ, hρ, hcan, hρc⟩
  -- Size transfer: t and c have the same size.
  have hc_size : Term.size c ≤ n := by
    rw [← hρc, apply_renaming_size hρ] at hsize; exact hsize
  -- Irreducibility transfer: c = apply τ t where τ is the inverse renaming.
  rcases hρ.flip with ⟨τ, hτ, _, hLρτ⟩
  have hc_irr : ∀ u, ¬ Step (R_can S n) c u := by
    have hτt : apply τ t = c := by rw [← hρc]; exact hLρτ c
    rw [← hτt]
    exact hτ.preserves_step_irreducible hirr
  -- Enumeration: c ∈ I_can S n.
  have hc_mem : c ∈ I_can S n :=
    canonical_irreducible_in_I_can hc_size hcan hc_irr
  -- Equivalence: c ≈ₜ apply ρ c = t (by equiv_rename).
  have hc_equiv : c ≈ₜ t := by rw [← hρc]; exact equiv_rename hρ c
  exact ⟨⟨c, ρ, hc_mem, hρc⟩, ⟨c, hc_mem, hc_equiv⟩⟩

inductive ExtStep (n : Nat) : Term S → Term S → Prop where
  /-- Standard rule rewriting (Phase 1). -/
  | rule {s t : Term S} (h : Step (R_can S n) s t) : ExtStep n s t
  /-- Equivalence-class step: from `t` to a stored `I_can` member
  `c ≈ₜ t`, where `t` itself is a substitution-instance of some
  `m ∈ I_can` (i.e., the source `t` lies in `I_can` *modulo substitution*).
  Both source-side (`apply σ m = t`) and destination-side (`c ∈ I_can`)
  are anchored in the algorithm's stored canonical irreducibles. -/
  | class_lookup {t c : Term S} {m : Term S} {σ : Subst S}
      (hm : m ∈ I_can S n) (h_inst : apply σ m = t)
      (hc : c ∈ I_can S n) (h_eq : t ≈ₜ c) :
      ExtStep n t c
  /-- `≈ₜ`-preserving renaming. -/
  | rename_eq {s : Term S} {ρ : Subst S} (hρ : IsRenaming ρ)
      (h_eq : s ≈ₜ apply ρ s) : ExtStep n s (apply ρ s)

abbrev ExtStepStar (n : Nat) : Term S → Term S → Prop :=
  Relation.ReflTransGen (ExtStep (S := S) n)

namespace ExtStep

theorem equiv_of {n : Nat} {s t : Term S} (hst : ExtStep n s t) : s ≈ₜ t := by
  cases hst with
  | rule h => exact Step.equiv_of (fun hlr => rule_equiv_can hlr) h
  | class_lookup _ _ _ h_eq => exact h_eq
  | rename_eq _ h_eq => exact h_eq

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

/-- **Common normal form theorem**: for any `≈ₜ`-equivalent terms of
size ≤ n, both reach **the same** term `c ∈ I_can S n` — the unique
canonical representative of the shared `≈ₜ`-class — via the
algorithm's three operational steps.

Proof: Phase 1 reaches `R_can`-irreducibles `s', t'` with `s' ≈ₜ t'`.
By `I_can_complete`, there is `c ∈ I_can S n` with `c ≈ₜ s'`. By
`I_can_unique_per_class`, this `c` is the unique `I_can` member in
the class — so it equals the `I_can` member for `t'`'s class
(same class). Both `s' →` `c` and `t' → c` via `class_lookup`. -/
theorem complete_common_normal_form (n : Nat) {s t : Term S}
    (hs_size : Term.size s ≤ n) (ht_size : Term.size t ≤ n) (hst : s ≈ₜ t) :
    ∃ c, c ∈ I_can S n ∧
         ExtStepStar (S := S) n s c ∧ ExtStepStar (S := S) n t c := by
  rcases reaches_normal_form_can n s with ⟨s', hss', hs_irr⟩
  rcases reaches_normal_form_can n t with ⟨t', htt', ht_irr⟩
  -- Sizes are non-increasing under R_can-rewriting.
  have hs'_size : Term.size s' ≤ n := le_trans (StepStar.size_le hss') hs_size
  have ht'_size : Term.size t' ≤ n := le_trans (StepStar.size_le htt') ht_size
  -- Soundness: s ≈ₜ s', t ≈ₜ t', so s' ≈ₜ t'.
  have hs_eq : s ≈ₜ s' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) hss'
  have ht_eq : t ≈ₜ t' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) htt'
  have hst' : s' ≈ₜ t' :=
    equiv_trans (equiv_symm hs_eq) (equiv_trans hst ht_eq)
  -- I_can_complete_subst gives both substitution-pre-image and canonical rep.
  rcases I_can_complete_subst hs'_size hs_irr with
    ⟨⟨m_s, σ_s, hm_s, h_inst_s⟩, ⟨c_s, hc_s, h_cs⟩⟩
  rcases I_can_complete_subst ht'_size ht_irr with
    ⟨⟨m_t, σ_t, hm_t, h_inst_t⟩, ⟨c_t, hc_t, h_ct⟩⟩
  -- Uniqueness: c_s = c_t since both are I_can reps of the same class.
  have h_cs_ct : c_s ≈ₜ c_t :=
    equiv_trans h_cs (equiv_trans hst' (equiv_symm h_ct))
  have hc_eq : c_s = c_t := I_can_unique_per_class hc_s hc_t h_cs_ct
  -- Both paths: rewrite to s'/t', then class_lookup (anchored on both sides).
  refine ⟨c_s, hc_s, ?_, ?_⟩
  · refine Relation.ReflTransGen.tail hss'.toExtStepStar ?_
    exact ExtStep.class_lookup hm_s h_inst_s hc_s (equiv_symm h_cs)
  · rw [hc_eq]
    refine Relation.ReflTransGen.tail htt'.toExtStepStar ?_
    exact ExtStep.class_lookup hm_t h_inst_t hc_t (equiv_symm h_ct)

end EnumRules
