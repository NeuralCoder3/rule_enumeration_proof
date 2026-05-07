import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import EnumRules.Equiv
import EnumRules.Kbo
import EnumRules.Oracle
import EnumRules.Subst

/-
# Substitution-based rewriting

## Role
Defines `Step R` (one-step rewrite) and its reflexive-transitive
closure `StepStar R`. `Step.root σ` fires a rule `(l, r) ∈ R` under
substitution `σ`; `Step.ctx` closes under one-hole contexts.

Three properties of `Step` carry the proof:
* `equiv_of` — rewriting preserves `≈ₜ` (uses `equiv_subst`,
  `equiv_congr`, `equiv_refl`).
* `kbo_of` — rewriting strictly decreases `≺ₖ` (uses `kbo_subst`,
  `kbo_mono_ctx`).
* `subst` — rewriting commutes with `apply ρ` (uses `apply_comp`,
  `apply_node`). Foundation for α-equivariance in CanonicalLayer.

`Step.root_id` is the ground-rule firing form, used wherever a rule
fires "as written" (no further substitution) — concretely,
`Correctness.lean`'s `reaches_smtMin` final step. Built from
`Step.root (idSubst S)` plus `apply_id`.

## Axioms
None. Everything in this file is a theorem from the axioms in
`Equiv.lean`, `Kbo.lean`, `Subst.lean`.
-/

namespace EnumRules

variable {S : Signature}

/-- A rule set is a finite set of pairs `(l, r)`. -/
abbrev RuleSet (S : Signature) := Finset (Term S × Term S)

/-- One-step substitution-based rewriting. -/
inductive Step (R : RuleSet S) : Term S → Term S → Prop where
  /-- Root rewrite: fire a rule under a substitution. -/
  | root {l r : Term S} (σ : Subst S) :
      (l, r) ∈ R → Step R (apply σ l) (apply σ r)
  /-- Contextual rewrite: rewrite the `i`-th argument of a node. -/
  | ctx {f : S.σ} {as bs : Fin (S.arity f) → Term S} {i : Fin (S.arity f)}
        (hstep : Step R (as i) (bs i))
        (hrest : ∀ j, j ≠ i → as j = bs j) :
      Step R (Term.node f as) (Term.node f bs)

/-- Reflexive-transitive closure of one-step rewriting. -/
abbrev StepStar (R : RuleSet S) : Term S → Term S → Prop :=
  Relation.ReflTransGen (Step R)

namespace Step

/-- Fire a rule at the root via the identity substitution. -/
theorem root_id {R : RuleSet S} {l r : Term S}
    (h : (l, r) ∈ R) : Step R l r := by
  have := Step.root (R := R) (idSubst S) h
  simpa [apply_id] using this

/-- Soundness: a step under a `≈ₜ`-sound rule set preserves `≈ₜ`. -/
theorem equiv_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S}, (l, r) ∈ R → l ≈ₜ r)
    {s t : Term S} (hst : Step R s t) : s ≈ₜ t := by
  induction hst with
  | root σ hlr => exact equiv_subst (hR hlr) σ
  | @ctx f as bs i _ hrest ih =>
      have harg : ∀ j, as j ≈ₜ bs j := by
        intro j
        by_cases hj : j = i
        · cases hj; exact ih
        · exact (hrest j hj) ▸ equiv_refl _
      exact equiv_congr harg

/-- KBO-decrease: a step under a KBO-decreasing rule set is itself
KBO-decreasing — pointwise on rule skeletons (`r ≺ₖ l`) lifts to every
substitution instance via `kbo_subst`. -/
theorem kbo_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S}, (l, r) ∈ R → r ≺ₖ l)
    {s t : Term S} (hst : Step R s t) : t ≺ₖ s := by
  induction hst with
  | root σ hlr => exact kbo_subst (hR hlr) σ
  | @ctx f as bs i _ hrest ih =>
      exact kbo_mono_ctx (as := as) (bs := bs) (i := i)
        (fun j hj => hrest j hj) ih

/-- Lift a step to a larger rule set. -/
theorem lift {R₁ R₂ : RuleSet S} (hR : R₁ ⊆ R₂) {s t : Term S}
    (h : Step R₁ s t) : Step R₂ s t := by
  induction h with
  | root σ hmem => exact Step.root σ (hR hmem)
  | ctx _ hrest ih => exact Step.ctx ih hrest

/-- Substitution-stability: rewriting commutes with `apply`. A step
under substitution `σ` lifts under `ρ` to a step under `Subst.comp ρ σ`,
and contextual closure follows by `apply_node`. -/
theorem subst {R : RuleSet S} {s t : Term S} (h : Step R s t) (ρ : Subst S) :
    Step R (apply ρ s) (apply ρ t) := by
  induction h with
  | @root l r σ hmem =>
      have h₁ : Step R (apply (Subst.comp ρ σ) l) (apply (Subst.comp ρ σ) r) :=
        Step.root (Subst.comp ρ σ) hmem
      rw [apply_comp, apply_comp] at h₁
      exact h₁
  | @ctx f as bs i _ hrest ih =>
      rw [apply_node, apply_node]
      refine Step.ctx (i := i) ih ?_
      intro j hj; rw [hrest j hj]

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

/-- Reflexive-transitive version of `Step.kbo_of`. -/
theorem kbo_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S}, (l, r) ∈ R → r ≺ₖ l)
    {s t : Term S} (hst : StepStar R s t) : s = t ∨ t ≺ₖ s := by
  induction hst with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
    rcases ih with (heq | hlt)
    · subst heq; exact Or.inr (Step.kbo_of hR hstep)
    · exact Or.inr (kbo_trans (Step.kbo_of hR hstep) hlt)

/-- Lift a rewrite sequence to a larger rule set. -/
theorem lift {R₁ R₂ : RuleSet S} (hR : R₁ ⊆ R₂) {s t : Term S}
    (h : StepStar R₁ s t) : StepStar R₂ s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.tail ih (Step.lift hR hstep)

/-- Substitution-stability of multi-step rewriting. -/
theorem subst {R : RuleSet S} {s t : Term S}
    (h : StepStar R s t) (ρ : Subst S) :
    StepStar R (apply ρ s) (apply ρ t) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (Step.subst hstep ρ)

end StepStar

/-- `simplifiesWith R t` holds when `t` can be rewritten by `R` to a term
of strictly smaller size. -/
def simplifiesWith (R : RuleSet S) (t : Term S) : Prop :=
  ∃ u, StepStar R t u ∧ Term.size u < Term.size t

/-- Lift a `StepStar` reduction to a context position. -/
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
