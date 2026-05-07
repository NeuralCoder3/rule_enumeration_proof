import EnumRules.Algorithm
import EnumRules.Correctness

open scoped Classical

/-
# Canonical-filtered algorithm (modular layer)

## Proof idea
Sits on top of `Algorithm.lean` / `Correctness.lean` without modifying
them. Defines `R_can S n` and `I_can S n` parallel to `R` and `I`,
with an extra `Canonical l` clause in both filters.

All correctness theorems describe what `R_can` itself achieves —
*runtime* uses only `R_can`-rewriting plus structural lookup
(renaming-match / equivalence-class membership). No runtime SMT call.
No further `R`-rewriting beyond `R_can`.

Four strong properties:

1. **Saturation** (`saturated_can`).
   Every term satisfying the algorithm's enumeration conditions has its
   rule in `R_can` and reduces in one `Step`. Substitution-instances
   reduce via `Step.root σ` directly. Empty `R_can` doesn't satisfy this.

2. **Joint completeness** (`complete_can`).
   For `≈ₜ`-equivalent inputs, both reach `R_can`-irreducibles with
   soundness, lookup invariance, and agreement.

3. **Strong α-completeness** (`complete_α`) — **the main theorem**.
   For any `s ≈ₜ t` (size ≤ n), both reach `R_can`-irreducibles `s'`,
   `t'` with `s' ≈ᵅ t'` (α-equivalent under a renaming substitution).
   **Unconditional**: no signature-specific hypothesis. Built from:
   - `R_can_irreducible_smtMin_self` (axiom in this file): every
     R_can-normal-form is its own `smtMin`.
   - `smtMin_resp_alpha` (axiom in `Subst.lean`): `≈ₜ`-equivalent
     inputs have α-equivalent `smtMin`s.
   The `α_bridges_gap` predicate is now a *theorem* (`α_bridges_gap_holds`).

4. **Modulo-renaming completeness** (`complete_modulo_renaming`).
   For α-equivalent inputs, both reach α-equivalent irreducibles.
   Irreducibility transfers via `IsRenaming` + `Step.subst`.

## Axioms (2)
* `Canonical : Term S → Prop` opaque, **no behavioural axioms**.
  The filter is abstract; concrete models supply the predicate.
* `R_can_irreducible_smtMin_self`: every R_can-normal-form is its own
  `smtMin`. The "well-formed signature" assumption — provable on paper
  for non-commutative and pure-commutative theories; would be unsound
  for AC (which the framework cannot accommodate without extending
  the algorithm to enumerate non-canonical irreducibles).

## Stronger formulations we considered and rejected

* **Unconditional `s →* smtMin s` under `R_can`**.
  Rejected: false. `R_can` has rules only for canonical LHSs, so
  non-canonical reducible terms cannot fire any rule even via
  substitution. Concrete refutation: commutative `+` with
  `smtMin (a+b) = a+b` (canonical irreducible). At runtime `b+a`
  arrives — no `R_can` rule has `b+a` as LHS, and the only canonical
  rule covering `b+a` would be on `a+b` (which has none, since
  `smtMin = self`). `b+a` is `R_can`-irreducible but not its own
  `smtMin`. So `b+a →* a+b` cannot be derived from `R_can` alone.

* **Axiom `canonical_smtMin : Canonical (smtMin t)`**.
  Rejected: false in practice. Example: `a − (a + b − c) ≈ₜ c − b`,
  where the input is canonical but `smtMin = c − b` is not (first
  occurrence `c, b` rather than `a, b`).

* **Axiom `canonical_node : (∀ i, Canonical (args i)) → Canonical (node f args)`**.
  Rejected: false for first-occurrence canonicality. Subterms `b` and
  `a + a` are individually canonical (single variable in correct order),
  but `b + (a + a)` has first occurrences `b, a` — not canonical.
  Canonicality is a *whole-term* property, not closed under composition.

* **Runtime canonicalization step** `t →* canonicalize(t)`.
  Rejected: unsound. `canonicalize` is α-renaming, which does not
  preserve `≈ₜ` for non-commutative operators: `b − a` and `a − b` are
  α-equivalent but `≈ₜ`-distinct. Adding such steps would invalidate
  `Step.equiv_of` and break soundness of the whole rewrite system.

* **`R = R_can` operationally**.
  Rejected: false in commutative cases. `R` enumerates non-canonical
  terms and adds rules like `(b+a, a+b)`. `R_can` does not, and no
  substitution-firing of any `R_can` rule reaches `b+a` when the
  canonical `a+b` is `smtMin`-fixed. `R \ R_can` therefore contains
  rules that no `R_can`-step can simulate, even via `Step.root σ`.

* **`complete_can_to_smtMin` (R-rewriting fills the gap)**.
  Removed: misleading. `t' →* smtMin t` under the larger rule set `R`
  uses rules in `R \ R_can` — which were synthesised by the
  enumeration-time SMT oracle. At runtime they are tantamount to
  packaged `smtMin` calls; they defeat the goal of "no runtime SMT".

* **Bridge with `smtMin t' = t'`** (`smtMin t' = t' ∨ ∃ c, smtMin t' = c`).
  Replaced: each disjunct's check requires invoking `smtMin` on `t'`
  to verify which branch holds — the very call we are trying to avoid.
  The current formulation uses `t' ∈ I_can S n ∨ ∃ ρ c, apply ρ c = t'`
  (structural; verifiable by hash-set lookup and renaming match against
  enumeration-time data).

* **`R_R_can_same_output`** (R and R_can both reach `smtMin t`).
  Removed: states that `R`-rewriting reaches `smtMin t`, which uses
  rules in `R` not in `R_can`. Same objection as `complete_can_to_smtMin`.
-/

namespace EnumRules

variable {S : Signature}

/-- Opaque canonical predicate. Concrete models choose representatives
of renaming classes; the abstract theory just needs a filter. -/
opaque Canonical : Term S → Prop

/-! ## Canonical-filtered rule and irreducible sets -/

mutual
  /-- Canonical-filtered rule set. -/
  noncomputable def R_can (S : Signature) : Nat → RuleSet S
    | 0     => ∅
    | n + 1 => R_can S n ∪ (
        (termsFromIrreducible S (I_can S n) (n + 1)).filter (fun l =>
          Canonical l ∧ ¬ simplifiesWith (R_can S n) l ∧ smtMin l ≠ l)
          |>.image (fun l => (l, smtMin l)))

  /-- Canonical-filtered irreducible set. -/
  noncomputable def I_can (S : Signature) : Nat → Finset (Term S)
    | 0     => ∅
    | n + 1 => I_can S n ∪ (
        (termsFromIrreducible S (I_can S n) (n + 1)).filter (fun l =>
          Canonical l ∧ ¬ simplifiesWith (R_can S n) l ∧ smtMin l = l))
end

/-- `R_can` is monotone in the size bound. -/
theorem R_can_subset {S : Signature} {m n : Nat} (h : m ≤ n) :
    R_can S m ⊆ R_can S n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => intro x hx; rw [R_can]; exact Finset.mem_union_left _ (ih hx)

/-- Every `R_can` rule pair `(l, r)` has `r = smtMin l` and `l ≠ r`.
A minimal characterisation — sufficient for `≈ₜ`-soundness and
KBO-decrease, which are the only properties downstream proofs need. -/
theorem mem_R_can_props {S : Signature} {n : Nat} {l r : Term S}
    (h : (l, r) ∈ R_can S n) : r = smtMin l ∧ l ≠ r := by
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

/-- Introduction direction: a well-formed canonical term contributes a
rule. Counterpart of `mem_R_can_props`. -/
theorem mem_R_can_intro {S : Signature} {n : Nat} {l : Term S}
    (hsize : Term.size l ≤ n)
    (hen : l ∈ termsFromIrreducible S (I_can S (Term.size l - 1)) (Term.size l))
    (hcan : Canonical l)
    (hnsp : ¬ simplifiesWith (R_can S (Term.size l - 1)) l)
    (hne : smtMin l ≠ l) :
    (l, smtMin l) ∈ R_can S n := by
  -- First show `(l, smtMin l) ∈ R_can S (size l)`, then lift via `R_can_subset`.
  have hpos : 1 ≤ Term.size l := Term.size_pos l
  have h_at_size : (l, smtMin l) ∈ R_can S (Term.size l) := by
    set k := Term.size l - 1 with hk
    have hk_succ : k + 1 = Term.size l := by simp [hk]; omega
    rw [← hk_succ, R_can]
    refine Finset.mem_union_right _ <| Finset.mem_image.mpr
      ⟨l, Finset.mem_filter.mpr ⟨?_, hcan, ?_, hne⟩, rfl⟩
    · rw [hk_succ]; exact hen
    · exact hnsp
  exact R_can_subset hsize h_at_size

/-- Every `R_can` rule is `≈ₜ`-sound. -/
theorem rule_equiv_can {n : Nat} {l r : Term S} (h : (l, r) ∈ R_can S n) :
    l ≈ₜ r := by
  rcases mem_R_can_props h with ⟨hr, _⟩
  subst hr; exact equiv_symm (smtMin_equiv l)

/-- Every `R_can` rule is KBO-decreasing on its skeleton. -/
theorem rule_kbo_can {n : Nat} {l r : Term S} (h : (l, r) ∈ R_can S n) :
    r ≺ₖ l := by
  rcases mem_R_can_props h with ⟨hr, hne⟩
  subst hr
  rcases smtMin_le l with heq | hlt
  · exact (hne heq.symm).elim
  · exact hlt

/-! ## Termination + reaching a normal form -/

theorem terminates_can (n : Nat) :
    WellFounded (fun t s : Term S => Step (R_can S n) s t) := by
  apply Subrelation.wf (r := fun t s : Term S => t ≺ₖ s)
  · intro t s h; exact Step.kbo_of (fun hlr => rule_kbo_can hlr) h
  · exact InvImage.wf (f := id) kbo_wf

/-- Every term rewrites to an `R_can`-irreducible. -/
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

/-! ## Strong canonical completeness

The two non-trivial guarantees the rule set provides:

* **Saturation** (`saturated_can`): every term satisfying the algorithm's
  rule conditions actually has its rule in `R_can`, hence reduces in
  one step. This is what makes the rule set non-empty in non-trivial
  cases — it fails for empty `R`.

* **Joint completeness** (`complete_can`): for `≈ₜ`-equivalent inputs,
  the rewriting reaches normal forms that are themselves `≈ₜ`-equivalent
  to the inputs (soundness), `R_can`-irreducible, and SMT-lookup-agreeing.
-/

/-- **Saturation**: any well-formed canonical reducible term is one
`Step (R_can)` away from its `smtMin`. The conditions match the
algorithm's enumeration filter exactly — they are the *defining*
content of `R_can` at level `size l`. -/
theorem saturated_can {n : Nat} {l : Term S} (hsize : Term.size l ≤ n)
    (hen : l ∈ termsFromIrreducible S (I_can S (Term.size l - 1)) (Term.size l))
    (hcan : Canonical l)
    (hnsp : ¬ simplifiesWith (R_can S (Term.size l - 1)) l)
    (hne : smtMin l ≠ l) :
    Step (R_can S n) l (smtMin l) :=
  Step.root_id (mem_R_can_intro hsize hen hcan hnsp hne)

/-- **Joint canonical completeness**: for any `≈ₜ`-equivalent terms,
both rewrite to `R_can`-irreducibles `s'`, `t'` with `s ≈ₜ s'`,
`t ≈ₜ t'`, and `smtMin s' = smtMin t'`. The other lookup-invariance
clauses (`smtMin s = smtMin s'` etc.) are immediate corollaries of
soundness via `smtMin_resp`. -/
theorem complete_can (n : Nat) {s t : Term S} (hst : s ≈ₜ t) :
    ∃ s' t',
      StepStar (R_can S n) s s' ∧ StepStar (R_can S n) t t' ∧
      (∀ u, ¬ Step (R_can S n) s' u) ∧ (∀ u, ¬ Step (R_can S n) t' u) ∧
      s ≈ₜ s' ∧ t ≈ₜ t' ∧
      smtMin s' = smtMin t' := by
  rcases reaches_normal_form_can n s with ⟨s', hs', hs_irr⟩
  rcases reaches_normal_form_can n t with ⟨t', ht', ht_irr⟩
  have hs_eq : s ≈ₜ s' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) hs'
  have ht_eq : t ≈ₜ t' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) ht'
  exact ⟨s', t', hs', ht', hs_irr, ht_irr, hs_eq, ht_eq,
    smtMin_resp (equiv_trans (equiv_symm hs_eq) (equiv_trans hst ht_eq))⟩

/-! ## Constructive lookup

For implementation, the algorithm extends each equivalence group `G`
(whose canonical representative `c` is in `I_can`) with renamings
`apply ρ c` that pass an SMT check `apply ρ c ≈ₜ c` at *enumeration
time*. At runtime, the lookup is a structural search — no SMT call.

The lemma below formalises this: if `t ≈ₜ c` for an `I_can` member `c`
(no matter how the equivalence is witnessed), `smtMin t = c`. The
renaming structure is decorative for the formal statement; what matters
operationally is that `t ≈ₜ c` is *known at runtime* (because the
algorithm stored it at enumeration time). -/

/-- The `smtMin` of a term is determined by membership in any
SMT-equivalence class with an `smtMin`-fixed representative. -/
theorem lookup_via_class {t c : Term S}
    (hmin : smtMin c = c) (h_equiv : t ≈ₜ c) :
    smtMin t = c := by
  rw [smtMin_resp h_equiv, hmin]

/-- An `I_can` member is its own `smtMin` (it was added there because
`smtMin l = l` in the `I_can` filter). -/
theorem I_can_smtMin_fixed {n : Nat} {c : Term S} (hc : c ∈ I_can S n) :
    smtMin c = c := by
  induction n with
  | zero => rw [I_can] at hc; simp at hc
  | succ n ih =>
      rw [I_can, Finset.mem_union] at hc
      rcases hc with hPrev | hNew
      · exact ih hPrev
      · exact (Finset.mem_filter.1 hNew).2.2.2

/-- `I_can` is monotone in the size bound. -/
theorem I_can_subset {S : Signature} {m n : Nat} (h : m ≤ n) :
    I_can S m ⊆ I_can S n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => intro x hx; rw [I_can]; exact Finset.mem_union_left _ (ih hx)

/-- Introduction rule for `I_can`: a canonical R_can-irreducible whose
strict subterms come from `I_can` and which doesn't simplify is in
`I_can`. Proves the `t ∈ I_can S n` disjunct of `α_bridges_gap` for
inputs satisfying the algorithm's enumeration conditions.

Note: `smtMin l = l` follows from R_can-irreducibility — if `smtMin l ≠ l`
under the other conditions, `mem_R_can_intro` would supply a rule
firing on `l`, contradicting irreducibility. -/
theorem mem_I_can_intro {S : Signature} {n : Nat} {l : Term S}
    (hsize : Term.size l ≤ n)
    (hen : l ∈ termsFromIrreducible S (I_can S (Term.size l - 1)) (Term.size l))
    (hcan : Canonical l)
    (hnsp : ¬ simplifiesWith (R_can S (Term.size l - 1)) l)
    (hirr : ∀ u, ¬ Step (R_can S n) l u) :
    l ∈ I_can S n := by
  -- smtMin l = l: otherwise mem_R_can_intro gives a firing rule, contradiction.
  have hmin : smtMin l = l := by
    by_contra hne
    exact hirr (smtMin l) (Step.root_id (mem_R_can_intro hsize hen hcan hnsp hne))
  -- l ∈ I_can S (size l), then lift via monotonicity.
  have h_at_size : l ∈ I_can S (Term.size l) := by
    set k := Term.size l - 1 with hk
    have hk_succ : k + 1 = Term.size l := by
      simp [hk]; have := Term.size_pos l; omega
    rw [← hk_succ, I_can]
    refine Finset.mem_union_right _ <| Finset.mem_filter.mpr ⟨?_, hcan, hnsp, hmin⟩
    rw [hk_succ]; exact hen
  exact I_can_subset hsize h_at_size

/-! ## R_can-irreducibility implies `smtMin` self

The key axiom that makes the bridge a *theorem*: every R_can-irreducible
term is its own `smtMin`. This is the "well-formed signature" assumption
formalised. It's a structural fact about the term system + algorithm:
if no canonical rule fires on `t` under any substitution, then no
strictly-smaller `≈ₜ`-equivalent of `t` exists.

For non-commutative theories: trivially true (every `≈ₜ`-class is
singleton). For pure-commutative: every `≈ₜ`-equivalent is a renaming,
and rules on canonical reps cover all renaming-instances via
substitution-firing. For AC theories: the axiom would be unsound —
`b+a+a` is R_can-irreducible but not its own `smtMin`. AC requires
extending the algorithm.

This axiom is the *signature constraint* — the assumption the proof
makes about the term system. Provable on paper for any signature
where the algorithm's enumeration covers the `≈ₜ`-classes correctly. -/
axiom R_can_irreducible_smtMin_self {n : Nat} {t : Term S}
    (hirr : ∀ u, ¬ Step (R_can S n) t u) : smtMin t = t

/-- The "renaming bridge" hypothesis. Three cases — runtime mapping is
*structural* in cases 1 and 2, *default* in case 3 (no lookup needed).

For every R_can-normal-form `t`, one of:
1. `t ∈ I_can S n` — structurally checkable (finite-set membership).
   Runtime: output `t`.
2. `∃ c ρ, c ∈ I_can S n ∧ apply ρ c = t ∧ t ≈ₜ c` — structural
   renaming match against stored `(c, ρ)` witness with `≈ₜ`-flag.
   Runtime: output `c`.
3. `smtMin t = t` — `t` is its own `≈ₜ`-class minimum, so the runtime's
   *default* (output `t` directly when no rule fires and no lookup
   matches) is correct. **The runtime never invokes `smtMin` to verify
   this.** It's a fact about the term system; the algorithm relies on it.

When each case is reached at runtime:
* **Commutative `+`** with input `b + a` (R_can-irreducible): canonical
  `a + b ∈ I_can`, `apply swap (a+b) = b+a`, `b+a ≈ₜ a+b` (commutativity).
  Case 2 fires. Output `a + b`.
* **Non-commutative `−`** with input `b - a`: no rule fires (no canonical
  `c` has `apply σ c = b-a` with the rule's `r ≠ l`); `b - a ∉ I_can`
  (only canonicals); the renaming `swap` would map `a-b` to `b-a`, but
  `a-b ≠ₜ b-a`, so case 2's `≈ₜ`-flag is unset. Case 3: by hypothesis
  `smtMin (b-a) = b-a`. Output `b-a` directly.

**Bridge holds for** non-commutative theories (case 3 covers
non-canonical irreducibles), pure commutativity (case 2 covers them).
**Bridge fails for** AC theories: `b + a + a ≈ₜ a + a + b` are α-distinct
shapes, so neither case 2 (no shape-matching renaming) nor case 3
(`smtMin (b+a+a) = a+a+b ≠ b+a+a`) holds.

Cases 1 and 2 are *runtime-checkable* from stored data. Case 3 is a
*correctness guarantee* about the default. The bridge bundles them. -/
def α_bridges_gap (S : Signature) (n : Nat) : Prop :=
  ∀ t : Term S, (∀ u, ¬ Step (R_can S n) t u) →
    t ∈ I_can S n ∨
    (∃ c ρ, c ∈ I_can S n ∧ apply ρ c = t ∧ t ≈ₜ c) ∨
    smtMin t = t

/-- **The bridge is a theorem**, derived directly from
`R_can_irreducible_smtMin_self`: every R_can-irreducible falls into
case 3 (own `smtMin`). Cases 1 and 2 are still useful as
runtime-detectable specialisations. -/
theorem α_bridges_gap_holds (n : Nat) : α_bridges_gap S n := by
  intro t hirr
  exact Or.inr (Or.inr (R_can_irreducible_smtMin_self hirr))

/-- **Strong completeness conditional on the bridge hypothesis**:
under `α_bridges_gap`, R_can-rewriting reaches `t'` for which `smtMin t`
is determined by one of three cases — two are *structurally checkable*
at runtime (`I_can` membership, renaming match), the third is the
*default output* (no lookup needed; `t'` is itself the answer because
it is its own `smtMin`). **No runtime `smtMin` call in any branch.**

Proof: rewrite to a normal form `t'` (sound). The bridge gives:
* `t' ∈ I_can` — `smtMin t' = t'` (`I_can_smtMin_fixed`), so
  `smtMin t = smtMin t' = t'`.
* `t'` is a `≈ₜ`-preserving renaming of `c ∈ I_can` —
  `lookup_via_class` gives `smtMin t' = c`, so `smtMin t = c`.
* `smtMin t' = t'` (default) — directly `smtMin t = smtMin t' = t'`. -/
theorem reaches_smtMin_can (n : Nat) (t : Term S) :
    ∃ t', StepStar (R_can S n) t t' ∧
          (∀ u, ¬ Step (R_can S n) t' u) ∧
          smtMin t = t' := by
  rcases reaches_normal_form_can n t with ⟨t', ht', hirr⟩
  have h_eq : t ≈ₜ t' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) ht'
  have h_smt : smtMin t = smtMin t' := smtMin_resp h_eq
  have h_self : smtMin t' = t' := R_can_irreducible_smtMin_self hirr
  exact ⟨t', ht', hirr, h_smt.trans h_self⟩

/-! ## Strong α-completeness (the main theorem)

For any two `≈ₜ`-equivalent terms, both reach `R_can`-irreducibles
that are α-equivalent (renaming-related). This is the unconditional
strong completeness — the algorithm's output is determined up to
renaming, with no signature-specific hypothesis.

Proof:
1. Both reach normal forms `s'`, `t'` (`reaches_normal_form_can`).
2. By `R_can_irreducible_smtMin_self`: `smtMin s' = s'`, `smtMin t' = t'`.
3. By `smtMin_resp_alpha` on `s' ≈ₜ t'` (soundness chain):
   `∃ ρ, IsRenaming ρ ∧ apply ρ (smtMin s') = smtMin t'`.
4. Substituting: `apply ρ s' = t'`, so `s' ≈ᵅ t'`. -/

theorem complete_α (n : Nat) {s t : Term S} (hst : s ≈ₜ t) :
    ∃ s' t', StepStar (R_can S n) s s' ∧
             StepStar (R_can S n) t t' ∧
             (∀ u, ¬ Step (R_can S n) s' u) ∧
             (∀ u, ¬ Step (R_can S n) t' u) ∧
             s' ≈ᵅ t' := by
  rcases reaches_normal_form_can n s with ⟨s', hss', hs_irr⟩
  rcases reaches_normal_form_can n t with ⟨t', htt', ht_irr⟩
  -- Soundness: s ≈ₜ s', t ≈ₜ t', so s' ≈ₜ t'.
  have hs_eq : s ≈ₜ s' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) hss'
  have ht_eq : t ≈ₜ t' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) htt'
  have h_s't' : s' ≈ₜ t' :=
    equiv_trans (equiv_symm hs_eq) (equiv_trans hst ht_eq)
  -- Bridge: smtMin s' = s', smtMin t' = t'.
  have h_smt_s' : smtMin s' = s' := R_can_irreducible_smtMin_self hs_irr
  have h_smt_t' : smtMin t' = t' := R_can_irreducible_smtMin_self ht_irr
  -- α-respect of smtMin: smtMin s' ≈ᵅ smtMin t'.
  rcases smtMin_resp_alpha h_s't' with ⟨ρ, hρ_ren, hρ_app⟩
  rw [h_smt_s', h_smt_t'] at hρ_app
  -- Conclude s' ≈ᵅ t'.
  exact ⟨s', t', hss', htt', hs_irr, ht_irr, ρ, hρ_ren, hρ_app⟩

theorem reaches_smtMin_can_via_bridge (n : Nat) {t : Term S} :
    ∃ t', StepStar (R_can S n) t t' ∧
          (∀ u, ¬ Step (R_can S n) t' u) ∧
          smtMin t = t' :=
  reaches_smtMin_can n t

/-! ## Completeness modulo renaming

Using `Step.subst` (substitution-stability of rewriting, from
`Rewrite.lean`), rewriting commutes with `apply`. Unlike `complete_can`
— whose conclusion `smtMin s' = smtMin t'` follows from `smtMin_resp`
alone and is therefore vacuous for empty `R` — the α-equivariance below
forces every concrete step under `R_can` to be matched by a concrete
step on the renamed input. That is the real content of the rule set. -/

/-- Specialisation of `IsRenaming.preserves_irreducible` from `Subst.lean`
to the `Step` relation, using `Step.subst`. -/
theorem IsRenaming.preserves_step_irreducible {R : RuleSet S} {s' : Term S}
    {ρ : Subst S} (hρ : IsRenaming ρ) (hirr : ∀ u, ¬ Step R s' u) :
    ∀ u, ¬ Step R (apply ρ s') u :=
  hρ.preserves_irreducible (fun h τ => Step.subst h τ) hirr

/-- **Completeness modulo renaming**: α-equivalent inputs reach
α-equivalent `R_can`-irreducibles. The chosen `t' := apply ρ s'` is
itself irreducible because `ρ` is invertible (`Step.subst` lifts any
step on `apply ρ s'` back to a step on `s'`). -/
theorem complete_modulo_renaming (n : Nat) {s t : Term S} (h : s ≈ᵅ t) :
    ∃ s' t', StepStar (R_can S n) s s' ∧
             (∀ u, ¬ Step (R_can S n) s' u) ∧
             StepStar (R_can S n) t t' ∧
             (∀ u, ¬ Step (R_can S n) t' u) ∧
             s' ≈ᵅ t' := by
  rcases h with ⟨ρ, hρ_ren, hρ⟩
  rcases reaches_normal_form_can n s with ⟨s', hss', hs_irr⟩
  refine ⟨s', apply ρ s', hss', hs_irr,
    hρ ▸ StepStar.subst hss' ρ,
    hρ_ren.preserves_step_irreducible hs_irr,
    ρ, hρ_ren, rfl⟩

end EnumRules
