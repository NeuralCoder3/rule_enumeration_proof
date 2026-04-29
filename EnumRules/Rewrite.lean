import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import EnumRules.Equiv
import EnumRules.Kbo
import EnumRules.Oracle

/-
# Rewrite relation

A rule set is a finite set of term pairs. One-step rewriting is the
standard contextual closure: rewrite at the root or in exactly one
argument position.
-/

namespace EnumRules

variable {S : Signature}

/-- A rule set is a finite set of pairs `(l, r)`. -/
abbrev RuleSet (S : Signature) := Finset (Term S × Term S)

/-- One-step rewriting. -/
inductive Step (R : RuleSet S) : Term S → Term S → Prop where
  /-- Root rewrite: apply a rule at the top of the term. -/
  | root {l r : Term S} : (l, r) ∈ R → Step R l r
  /-- Contextual rewrite: rewrite the `i`-th argument of a node. -/
  | ctx {f : S.σ} {as bs : Fin (S.arity f) → Term S} {i : Fin (S.arity f)}
        (hstep : Step R (as i) (bs i))
        (hrest : ∀ j, j ≠ i → as j = bs j) :
      Step R (Term.node f as) (Term.node f bs)

/-- Reflexive-transitive closure of one-step rewriting. -/
abbrev StepStar (R : RuleSet S) : Term S → Term S → Prop :=
  Relation.ReflTransGen (Step R)

namespace Step

/-- Every one-step rewrite under a ∼-sound rule set preserves ∼. -/
theorem equiv_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S}, (l, r) ∈ R → l ≈ₜ r)
    {s t : Term S} (hst : Step R s t) : s ≈ₜ t := by
  induction hst with
  | root hlr => exact hR hlr
  | @ctx f as bs i _ hrest ih =>
    -- Build arg-wise equivalence: at i we have ih, elsewhere as j = bs j.
    have harg : ∀ j, as j ≈ₜ bs j := by
      intro j
      by_cases hj : j = i
      · cases hj; exact ih
      · have h := hrest j hj
        -- `as j = bs j` gives reflexive equivalence after rewriting.
        have : as j ≈ₜ as j := equiv_refl _
        exact h ▸ this
    exact equiv_congr harg

/-- Every one-step rewrite under an "oracle"-compatible rule set is
KBO-decreasing, given that every rule `(l, r)` satisfies `r ≺ₖ l`. -/
theorem kbo_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S}, (l, r) ∈ R → r ≺ₖ l)
    {s t : Term S} (hst : Step R s t) : t ≺ₖ s := by
  induction hst with
  | root hlr => exact hR hlr
  | @ctx f as bs i _ hrest ih =>
    -- `bs i ≺ as i` and `as j = bs j` for `j ≠ i`.
    -- We want `node f bs ≺ node f as`, which is `kbo_mono_ctx` with `as` as the
    -- "larger" family and `bs` as the "smaller" family.
    refine kbo_mono_ctx (as := as) (bs := bs) (i := i) ?_ ih
    intro j hj
    exact hrest j hj

/-- One-step rewriting under a size-non-increasing rule set does not grow
the term size. -/
theorem size_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S}, (l, r) ∈ R → Term.size r ≤ Term.size l)
    {s t : Term S} (hst : Step R s t) : Term.size t ≤ Term.size s := by
  induction hst with
  | root hlr => exact hR hlr
  | @ctx f as bs i _ hrest ih =>
    -- size (node f as) = 1 + ∑ size (as j); similarly for bs.
    -- Only `i` changes; at `i` we have `size (bs i) ≤ size (as i)` by IH;
    -- everywhere else they are equal.
    simp [Term.size]
    have hsum : (∑ i : Fin (S.arity f), Term.size (bs i)) ≤ (∑ i : Fin (S.arity f), Term.size (as i)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = i
      · cases hj; exact ih
      · have h := hrest j hj
        rw [h]
    omega

end Step

namespace StepStar

/-- Reflexive-transitive version of `Step.equiv_of`. -/
theorem equiv_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S}, (l, r) ∈ R → l ≈ₜ r)
    {s t : Term S} (hst : StepStar R s t) : s ≈ₜ t := by
  induction hst with
  | refl => exact equiv_refl _
  | tail _ hlast ih => exact equiv_trans ih (Step.equiv_of hR hlast)

/-- Reflexive-transitive version of `Step.size_of`. -/
theorem size_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S}, (l, r) ∈ R → Term.size r ≤ Term.size l)
    {s t : Term S} (hst : StepStar R s t) : Term.size t ≤ Term.size s := by
  induction hst with
  | refl => exact le_refl _
  | tail _ hlast ih => exact le_trans (Step.size_of hR hlast) ih

end StepStar

end EnumRules
