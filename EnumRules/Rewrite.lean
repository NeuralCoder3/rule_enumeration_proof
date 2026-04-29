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

/-- Reflexive-transitive version of `Step.kbo_of`. -/
theorem kbo_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S}, (l, r) ∈ R → r ≺ₖ l)
    {s t : Term S} (hst : StepStar R s t) : s = t ∨ kbo t s := by
  induction hst with
  | refl => exact Or.inl rfl
  | tail hprefix hstep ih =>
    rcases ih with (heq | hlt)
    · subst heq; exact Or.inr (Step.kbo_of hR hstep)
    · exact Or.inr (kbo_trans (Step.kbo_of hR hstep) hlt)

end StepStar

/-- Lift a single step to a larger rule set. -/
theorem Step.lift {R₁ R₂ : RuleSet S} (hR : R₁ ⊆ R₂) {s t : Term S}
    (h : Step R₁ s t) : Step R₂ s t := by
  induction h with
  | root hmem => exact Step.root (hR hmem)
  | ctx hstep hrest ih => exact Step.ctx ih hrest

/-- Lift a rewrite sequence to a larger rule set. -/
theorem StepStar.lift {R₁ R₂ : RuleSet S} (hR : R₁ ⊆ R₂) {s t : Term S}
    (h : StepStar R₁ s t) : StepStar R₂ s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprefix hstep ih =>
    exact Relation.ReflTransGen.tail ih (Step.lift hR hstep)

/-- `simplifiesWith R t` holds when `t` can be rewritten by `R` to a term
of strictly smaller size. This is used to skip SMT calls for terms already
covered by rules from previous iterations. -/
def simplifiesWith (R : RuleSet S) (t : Term S) : Prop :=
  ∃ u, StepStar R t u ∧ Term.size u < Term.size t

/-- If a term simplifies with a smaller rule set, it also simplifies with a larger one. -/
theorem simplifiesWith.mono {R₁ R₂ : RuleSet S} (hR : R₁ ⊆ R₂) {t : Term S}
    (h : simplifiesWith R₁ t) : simplifiesWith R₂ t := by
  rcases h with ⟨u, hu, hsize⟩
  exact ⟨u, StepStar.lift hR hu, hsize⟩

/-- Lift a `StepStar` reduction to a context position: if a subterm rewrites,
the whole node rewrites at that position. -/
theorem StepStar.ctx {R : RuleSet S} {f : S.σ}
    {args : Fin (S.arity f) → Term S} {i : Fin (S.arity f)} {v : Term S}
    (h : StepStar R (args i) v) :
    StepStar R (Term.node f args)
      (Term.node f (fun j => if j = i then v else args j)) := by
  match h with
  | Relation.ReflTransGen.refl =>
    have h_eq : (fun j : Fin (S.arity f) => if j = i then args i else args j) = args := by
      funext j; dsimp; split_ifs with h
      · subst h; rfl
      · rfl
    simpa [h_eq] using (Relation.ReflTransGen.refl : StepStar R (Term.node f args) (Term.node f args))
  | Relation.ReflTransGen.tail hprefix hstep =>
    rename_i b
    have ih := StepStar.ctx hprefix
    have hlast : Step R
        (Term.node f (fun j => if j = i then b else args j))
        (Term.node f (fun j => if j = i then v else args j)) := by
      have hstep' : Step R ((fun j => if j = i then b else args j) i)
                           ((fun j => if j = i then v else args j) i) := by
        simpa using hstep
      exact Step.ctx (as := fun j => if j = i then b else args j)
                     (bs := fun j => if j = i then v else args j)
                     (i := i) hstep' (by intro j hj; simp [hj])
    exact Relation.ReflTransGen.tail ih hlast

/-- If a term simplifies, the reduced term is strictly KBO-smaller. -/
theorem simplifiesWith.kbo_lt {R : RuleSet S}
    (hR : ∀ {l r : Term S}, (l, r) ∈ R → r ≺ₖ l)
    {t : Term S} (h : simplifiesWith R t) :
    ∃ u, StepStar R t u ∧ Term.size u < Term.size t ∧ u ≺ₖ t := by
  rcases h with ⟨u, htu, hsize_u⟩
  rcases StepStar.kbo_of hR htu with (heq | hlt)
  · rw [heq] at hsize_u
    exact absurd hsize_u (Nat.lt_irrefl _)
  · exact ⟨u, htu, hsize_u, hlt⟩

end EnumRules
