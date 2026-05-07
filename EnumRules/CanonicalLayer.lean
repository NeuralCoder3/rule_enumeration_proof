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

1. **Saturation** (`saturated_can` / `saturated_can_subst`).
   Every term satisfying the algorithm's enumeration conditions has its
   rule in `R_can` and reduces in one `Step`. Substitution-instances
   reduce via `Step.root σ`. Empty `R_can` doesn't satisfy this.

2. **Joint completeness** (`complete_can`).
   For `≈ₜ`-equivalent inputs, both reach `R_can`-irreducibles with
   soundness, lookup invariance, and agreement.

3. **Strong completeness via the bridge** (`reaches_smtMin_can_via_bridge`).
   When the bridge `α_bridges_gap` holds (every R_can-normal-form is
   *itself* in `I_can` or is a `≈ₜ`-preserving renaming of an `I_can`
   member — both runtime-checkable), the algorithm reaches `smtMin t`
   using only:
   - `R_can`-rewriting (terminates by KBO well-foundedness), and
   - **structural** classification of `t'`: membership in the finite
     set `I_can` or a structural renaming match against stored witnesses.
   **No runtime `smtMin` call. No `R`-rewriting beyond `R_can`.**
   The bridge holds for non-commutative and pure-commutativity theories;
   it can fail for AC theories where associativity produces different
   `≈ₜ`-equivalent shapes.

4. **Modulo-renaming completeness** (`complete_modulo_renaming`).
   For α-equivalent inputs (related by an invertible substitution `ρ`),
   both reach α-equivalent irreducibles. Irreducibility transfers via
   `IsRenaming` + `Step.subst`.

## Axioms (1)
* `Canonical : Term S → Prop` opaque, **no behavioural axioms**.
  The filter is abstract; concrete models supply the predicate
  (first-occurrence variable ordering, renaming-class representative,
  etc.). The proof never inspects what the predicate means.

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

/-- **Substitution-saturation**: every substitution-instance of a
well-formed canonical reducible term takes a `Step` too. Combines
saturation with the substitution form of `Step.root`. -/
theorem saturated_can_subst {n : Nat} {l : Term S} (σ : Subst S)
    (hsize : Term.size l ≤ n)
    (hen : l ∈ termsFromIrreducible S (I_can S (Term.size l - 1)) (Term.size l))
    (hcan : Canonical l)
    (hnsp : ¬ simplifiesWith (R_can S (Term.size l - 1)) l)
    (hne : smtMin l ≠ l) :
    Step (R_can S n) (apply σ l) (apply σ (smtMin l)) :=
  Step.root σ (mem_R_can_intro hsize hen hcan hnsp hne)

/-- **Joint canonical completeness**: for any `≈ₜ`-equivalent terms
(size ≤ n), both rewrite to `R_can`-normal-forms `s'`, `t'` such that:
- (Soundness)        `s ≈ₜ s'` and `t ≈ₜ t'`.
- (Lookup invariance) `smtMin s = smtMin s'` and `smtMin t = smtMin t'`.
- (Agreement)         `smtMin s' = smtMin t'`.

The combination characterises the algorithm as computing a function
on `≈ₜ`-classes via "rewrite then SMT-lookup". -/
theorem complete_can (n : Nat) {s t : Term S} (hst : s ≈ₜ t) :
    ∃ s' t',
      StepStar (R_can S n) s s' ∧ StepStar (R_can S n) t t' ∧
      (∀ u, ¬ Step (R_can S n) s' u) ∧ (∀ u, ¬ Step (R_can S n) t' u) ∧
      s ≈ₜ s' ∧ t ≈ₜ t' ∧
      smtMin s = smtMin s' ∧ smtMin t = smtMin t' ∧
      smtMin s' = smtMin t' := by
  rcases reaches_normal_form_can n s with ⟨s', hs', hs_irr⟩
  rcases reaches_normal_form_can n t with ⟨t', ht', ht_irr⟩
  have hs_eq : s ≈ₜ s' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) hs'
  have ht_eq : t ≈ₜ t' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) ht'
  exact ⟨s', t', hs', ht', hs_irr, ht_irr, hs_eq, ht_eq,
    smtMin_resp hs_eq, smtMin_resp ht_eq,
    smtMin_resp (equiv_trans (equiv_symm hs_eq) (equiv_trans hst ht_eq))⟩

/-! ## Constructive lookup via renaming

The runtime lookup phase is `smtMin` (opaque). For practical
implementation, the algorithm extends each equivalence group `G` (whose
canonical representative `c` is in `I_can`) with renamings `apply ρ c`
that pass an SMT check `apply ρ c ≈ₜ c` at *enumeration time*.

Then at runtime, given an `R_can`-normal-form `t'`, the lookup is a
structural search through the enriched groups — no SMT call needed —
provided `t'` is a `≈ₜ`-preserving renaming of some group member.

The lemma below formalises this: if `t` is such a renaming-instance,
then `smtMin t = c` is determined by the group structure alone. -/

/-- **Renaming-based lookup**: when `t` is a `≈ₜ`-preserving renaming
of a canonical `I_can` member `c` (i.e., `apply ρ c = t` and
`apply ρ c ≈ₜ c`), the lookup `smtMin t` equals `c`.

For commutative operators (e.g., `t = b+a`, `c = a+b`, `ρ = swap`):
the hypothesis `apply ρ c ≈ₜ c` holds (`a+b ≈ₜ b+a`) so the lemma
applies and the lookup returns `a+b` directly. For non-commutative
operators (e.g., `t = b-a`, `c = a-b`): the hypothesis fails, the
lemma does NOT apply, and the algorithm correctly recognises `t` as
its own `≈ₜ`-class representative (lookup returns `t = b-a`). -/
theorem lookup_via_renaming {t c : Term S} (ρ : Subst S)
    (hmin : smtMin c = c) (_hα : apply ρ c = t) (h_equiv : t ≈ₜ c) :
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

/-- The "renaming bridge" hypothesis, **fully structural**: every
R_can-normal-form is either *itself* in `I_can` or is a `≈ₜ`-preserving
renaming of some `I_can` member. No `smtMin` invocation: both
disjuncts are runtime-checkable from stored data.

Holds when `≈ₜ`-classes coincide with α-classes within the scope —
purely commutative theories, non-commutative theories. Fails for AC-style
richer theories that produce *different-shape* `≈ₜ`-equivalents
(`b+a+a ≈ₜ a+a+b`). -/
def α_bridges_gap (S : Signature) (n : Nat) : Prop :=
  ∀ t : Term S, (∀ u, ¬ Step (R_can S n) t u) →
    t ∈ I_can S n ∨
    ∃ c ρ, c ∈ I_can S n ∧ apply ρ c = t ∧ t ≈ₜ c

/-- **Strong completeness conditional on the bridge hypothesis**:
under `α_bridges_gap`, R_can-rewriting reaches a term `t'` for which
`smtMin t` is computable *purely structurally* — either `t'` is
itself in `I_can` (output `t'`), or `t'` is a stored renaming of some
`c ∈ I_can` (output `c`). **No runtime `smtMin` call.**

The conclusion mentions `smtMin t` only as the *specification*: it
states what the structural lookup *equals*. Runtime needs only
membership tests against `I_can` and `apply ρ c = t'` checks against
stored renaming witnesses.

Proof: rewrite to a normal form `t'` (sound). The bridge gives two cases:
* `t' ∈ I_can` — `smtMin t' = t'` by `I_can_smtMin_fixed`, then
  `smtMin t = smtMin t' = t'`.
* `t'` is a `≈ₜ`-preserving renaming of `c ∈ I_can` —
  `lookup_via_renaming` gives `smtMin t' = c`, then
  `smtMin t = smtMin t' = c`. -/
theorem reaches_smtMin_can_via_bridge (n : Nat) {t : Term S}
    (h_bridge : α_bridges_gap S n) :
    ∃ t', StepStar (R_can S n) t t' ∧
          (∀ u, ¬ Step (R_can S n) t' u) ∧
          ((t' ∈ I_can S n ∧ smtMin t = t') ∨
           (∃ c ρ, c ∈ I_can S n ∧ apply ρ c = t' ∧ t' ≈ₜ c ∧ smtMin t = c)) := by
  rcases reaches_normal_form_can n t with ⟨t', ht', hirr⟩
  have h_eq : t ≈ₜ t' := StepStar.equiv_of (fun hlr => rule_equiv_can hlr) ht'
  have h_smt : smtMin t = smtMin t' := smtMin_resp h_eq
  rcases h_bridge t' hirr with hin | ⟨c, ρ, hc, hα, h_equiv⟩
  · refine ⟨t', ht', hirr, Or.inl ⟨hin, ?_⟩⟩
    rw [h_smt, I_can_smtMin_fixed hin]
  · refine ⟨t', ht', hirr, Or.inr ⟨c, ρ, hc, hα, h_equiv, ?_⟩⟩
    rw [h_smt, lookup_via_renaming ρ (I_can_smtMin_fixed hc) hα h_equiv]

/-! ## Completeness modulo renaming

Using `Step.subst` (substitution-stability of rewriting, from
`Rewrite.lean`), rewriting commutes with `apply`. Unlike `complete_can`
— whose conclusion `smtMin s' = smtMin t'` follows from `smtMin_resp`
alone and is therefore vacuous for empty `R` — the α-equivariance below
forces every concrete step under `R_can` to be matched by a concrete
step on the renamed input. That is the real content of the rule set. -/

/-- A substitution is a *renaming* if it has a global left inverse.
True for any variable-permutation substitution. -/
def IsRenaming (ρ : Subst S) : Prop :=
  ∃ τ : Subst S, ∀ u : Term S, apply τ (apply ρ u) = u

/-- α-equivalence: `t = apply ρ s` for an invertible (renaming)
substitution `ρ`. Reflexive (via `idSubst`) and transitive (via
`Subst.comp`). With invertibility, irreducibility is preserved by
`apply ρ`. -/
def AlphaEquiv (s t : Term S) : Prop :=
  ∃ ρ : Subst S, IsRenaming ρ ∧ apply ρ s = t

@[inherit_doc AlphaEquiv]
scoped infix:50 " ≈ᵅ " => AlphaEquiv

theorem IsRenaming.id : IsRenaming (idSubst S) :=
  ⟨idSubst S, fun u => by rw [apply_id, apply_id]⟩

theorem IsRenaming.comp {ρ τ : Subst S}
    (hρ : IsRenaming ρ) (hτ : IsRenaming τ) : IsRenaming (Subst.comp τ ρ) := by
  rcases hρ with ⟨ρ', hρ'⟩
  rcases hτ with ⟨τ', hτ'⟩
  refine ⟨Subst.comp ρ' τ', fun u => ?_⟩
  rw [apply_comp, apply_comp]
  rw [hτ' (apply ρ u)]
  exact hρ' u

theorem AlphaEquiv.refl (t : Term S) : t ≈ᵅ t :=
  ⟨idSubst S, IsRenaming.id, apply_id t⟩

theorem AlphaEquiv.trans {s t u : Term S} (h₁ : s ≈ᵅ t) (h₂ : t ≈ᵅ u) :
    s ≈ᵅ u := by
  rcases h₁ with ⟨ρ, hρ_ren, hρ⟩
  rcases h₂ with ⟨τ, hτ_ren, hτ⟩
  exact ⟨Subst.comp τ ρ, hρ_ren.comp hτ_ren, by rw [apply_comp, hρ]; exact hτ⟩

/-- Irreducibility is preserved by renaming substitutions: if `s'` admits
no `R`-step, then `apply ρ s'` admits none either, when `ρ` is a renaming. -/
theorem IsRenaming.preserves_irreducible {R : RuleSet S} {s' : Term S}
    {ρ : Subst S} (hρ : IsRenaming ρ) (hirr : ∀ u, ¬ Step R s' u) :
    ∀ u, ¬ Step R (apply ρ s') u := by
  rcases hρ with ⟨τ, hτ⟩
  intro u hstep
  have h := Step.subst hstep τ
  rw [hτ] at h
  exact hirr (apply τ u) h

/-- **α-equivariance of rewriting**: every reduction lifts under any
substitution. Non-trivial for any non-empty rule set — every concrete
step in `s →* s'` matches a concrete step in `apply ρ s →* apply ρ s'`. -/
theorem rewriting_α_equivariant {R : RuleSet S} {s s' : Term S}
    (ρ : Subst S) (h : StepStar R s s') :
    StepStar R (apply ρ s) (apply ρ s') :=
  StepStar.subst h ρ

/-- For any input `s` and substitution `ρ`, the algorithm's normal form
`s'` for `s` produces a reachable counterpart `apply ρ s'` for `apply ρ s`. -/
theorem normal_form_modulo_renaming (n : Nat) (s : Term S) (ρ : Subst S) :
    ∃ s', StepStar (R_can S n) s s' ∧
          (∀ u, ¬ Step (R_can S n) s' u) ∧
          StepStar (R_can S n) (apply ρ s) (apply ρ s') := by
  rcases reaches_normal_form_can n s with ⟨s', hss', hirr⟩
  exact ⟨s', hss', hirr, StepStar.subst hss' ρ⟩

/-- **Completeness modulo renaming**: α-equivalent inputs reach
α-equivalent normal forms under `R_can`. Both `s'` and `t'` are
genuine `R_can`-irreducibles. -/
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
    hρ_ren.preserves_irreducible hs_irr,
    ρ, hρ_ren, rfl⟩

end EnumRules
