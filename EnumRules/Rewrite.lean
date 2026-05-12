import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import EnumRules.Equiv
import EnumRules.Kbo
import EnumRules.Oracle
import EnumRules.Subst

/-
# Substitution-based rewriting (parameterised by extension)

## Role
Rules are stored as pairs of *rule-construction terms*
`(l, r) : Term S Empty × Term S Empty`. At runtime, `Step R` is a
relation on `Term S Ext` — firing rule `(l, r)` under a substitution
`σ : Subst S Ext` rewrites `apply σ l → apply σ r` (now in
`Term S Ext`). Contextual closure descends into `node` subterms
(`var`/`constP` can't appear at runtime; `ext` is a 0-ary leaf, atomic).

Properties of `Step` plumbed into the algorithm correctness proof:
* `equiv_of` — rewriting preserves `≈ₜ` (via `equiv_subst`,
  `equiv_congr`, `equiv_refl`).
* `kbo_of` — rewriting strictly decreases `≺ₖ` (via `kbo_subst`,
  `kbo_mono_ctx`).
* `irreducible_arg` — irreducibility passes to subterms (contrapositive
  of `Step.ctx`).
* `root_id` — fire a rule "as written" (no further substitution).
  Built from `Step.root Subst.id` plus `apply_id`. Only available at
  `Ext = Empty` (rule-construction time).

`not_simplifiesWith_of_irreducible` — irreducibility implies no
size-shrinking `StepStar` path.

## Axioms
None. Everything in this file is a theorem from the axioms in
`Equiv.lean`, `Kbo.lean`, `Subst.lean`.
-/

namespace EnumRules

variable {S : Signature} {Ext : Type}

/-- A rule set: pairs of rule-construction terms (no extension symbols). -/
abbrev RuleSet (S : Signature) := Finset (Term S Empty × Term S Empty)

/-- One-step substitution-based rewriting at extension `Ext`. -/
inductive Step (R : RuleSet S) : Term S Ext → Term S Ext → Prop where
  /-- Root rewrite: fire a rule (in `Term S Empty`) under a substitution
  (into `Term S Ext`). -/
  | root {l r : Term S Empty} (σ : Subst S Ext) :
      (l, r) ∈ R → Step R (apply σ l) (apply σ r)
  /-- Contextual rewrite: rewrite the `i`-th argument of a node. -/
  | ctx {f : S.σ} {as bs : Fin (S.arity f) → Term S Ext} {i : Fin (S.arity f)}
        (hstep : Step R (as i) (bs i))
        (hrest : ∀ j, j ≠ i → as j = bs j) :
      Step R (Term.node f as) (Term.node f bs)

/-- Reflexive-transitive closure of one-step rewriting. -/
abbrev StepStar (R : RuleSet S) : Term S Ext → Term S Ext → Prop :=
  Relation.ReflTransGen (Step R (Ext := Ext))

namespace Step

/-- Fire a rule at the root via the identity substitution. Only
available at `Ext = Empty` (the only level where `Subst.id` exists). -/
theorem root_id {R : RuleSet S} {l r : Term S Empty}
    (h : (l, r) ∈ R) : Step (Ext := Empty) R l r := by
  have := Step.root (R := R) (Ext := Empty) Subst.id h
  simpa [apply_id] using this

/-- Soundness: a step under a `≈ₜ`-sound rule set preserves `≈ₜ`. -/
theorem equiv_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S Empty}, (l, r) ∈ R → l ≈ₜ r)
    {s t : Term S Ext} (hst : Step R s t) : s ≈ₜ t := by
  induction hst with
  | root σ hlr => exact equiv_subst (hR hlr) σ
  | @ctx f as bs i _ hrest ih =>
      refine equiv_congr fun j => ?_
      by_cases hj : j = i <;> [exact hj ▸ ih; exact hrest j hj ▸ equiv_refl _]

/-- KBO-decrease: a step under a KBO-decreasing rule set is itself
KBO-decreasing. -/
theorem kbo_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S Empty}, (l, r) ∈ R → r ≺ₖ l)
    {s t : Term S Ext} (hst : Step R s t) : t ≺ₖ s := by
  induction hst with
  | root σ hlr => exact kbo_subst (hR hlr) σ
  | ctx _ hrest ih => exact kbo_mono_ctx hrest ih

/-- Lift a step to a larger rule set. -/
theorem lift {R₁ R₂ : RuleSet S} (hR : R₁ ⊆ R₂) {s t : Term S Ext}
    (h : Step R₁ s t) : Step R₂ s t := by
  induction h with
  | root σ hmem => exact Step.root σ (hR hmem)
  | ctx _ hrest ih => exact Step.ctx ih hrest

/-- Contrapositive of `Step.ctx`: subterms of an irreducible node are
themselves irreducible. -/
theorem irreducible_arg {R : RuleSet S} {f : S.σ}
    {args : Fin (S.arity f) → Term S Ext} {i : Fin (S.arity f)}
    (h : ∀ u, ¬ Step R (Term.node f args) u) :
    ∀ v, ¬ Step R (args i) v := by
  intro v hstep
  apply h (Term.node f (fun j => if j = i then v else args j))
  refine Step.ctx (as := args) (bs := fun j => if j = i then v else args j) (i := i) ?_ ?_
  · simpa using hstep
  · intro j hj; simp [hj]

/-- Substitution-stability of `Step`: a construction-time step
`Step R s t` (at `Ext = Empty`) lifts under any `σ : Subst S Ext` to
a runtime step `Step R (apply σ s) (apply σ t)` (at `Ext`). The key
mechanism: composing the construction-time rule's substitution `σ'`
with `σ` gives a single `σ.comp σ'` that fires the rule directly at
`Ext`. -/
theorem subst {R : RuleSet S} {s t : Term S Empty}
    (h : Step (Ext := Empty) R s t) (σ : Subst S Ext) :
    Step R (apply σ s) (apply σ t) := by
  induction h with
  | @root l r σ' hmem =>
      have hcomp : Step R (apply (σ.comp σ') l) (apply (σ.comp σ') r) :=
        Step.root (σ.comp σ') hmem
      rw [apply_comp, apply_comp] at hcomp
      exact hcomp
  | @ctx f as bs i _ hrest ih =>
      rw [apply_node, apply_node]
      refine Step.ctx (i := i) ih ?_
      intro j hj
      rw [hrest j hj]

end Step

namespace StepStar

/-- Reflexive-transitive version of `Step.equiv_of`. -/
theorem equiv_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S Empty}, (l, r) ∈ R → l ≈ₜ r)
    {s t : Term S Ext} (hst : StepStar R s t) : s ≈ₜ t := by
  induction hst with
  | refl => exact equiv_refl _
  | tail _ hlast ih => exact equiv_trans ih (Step.equiv_of hR hlast)

/-- Reflexive-transitive version of `Step.kbo_of`. -/
theorem kbo_of
    {R : RuleSet S}
    (hR : ∀ {l r : Term S Empty}, (l, r) ∈ R → r ≺ₖ l)
    {s t : Term S Ext} (hst : StepStar R s t) : s = t ∨ t ≺ₖ s := by
  induction hst with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
    rcases ih with (heq | hlt)
    · subst heq; exact Or.inr (Step.kbo_of hR hstep)
    · exact Or.inr (kbo_trans (Step.kbo_of hR hstep) hlt)

/-- Lift a rewrite sequence to a larger rule set. -/
theorem lift {R₁ R₂ : RuleSet S} (hR : R₁ ⊆ R₂) {s t : Term S Ext}
    (h : StepStar R₁ s t) : StepStar R₂ s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.tail ih (Step.lift hR hstep)

end StepStar

/-- `simplifiesWith R t` holds when `t` can be rewritten by `R` to a term
of strictly smaller size. -/
def simplifiesWith (R : RuleSet S) (t : Term S Ext) : Prop :=
  ∃ u, StepStar R t u ∧ Term.size u < Term.size t

/-- If a term simplifies, the reduced term is strictly KBO-smaller. -/
theorem simplifiesWith.kbo_lt {R : RuleSet S}
    (hR : ∀ {l r : Term S Empty}, (l, r) ∈ R → r ≺ₖ l)
    {t : Term S Ext} (h : simplifiesWith R t) :
    ∃ u, StepStar R t u ∧ Term.size u < Term.size t ∧ u ≺ₖ t := by
  obtain ⟨u, htu, hsize⟩ := h
  rcases StepStar.kbo_of hR htu with rfl | hlt
  · omega
  · exact ⟨u, htu, hsize, hlt⟩

/-- An irreducible term doesn't simplify. -/
theorem not_simplifiesWith_of_irreducible {R : RuleSet S} {t : Term S Ext}
    (h : ∀ u, ¬ Step R t u) : ¬ simplifiesWith R t := by
  rintro ⟨u, htu, hsize⟩
  have heq : t = u := by
    clear hsize
    induction htu with
    | refl => rfl
    | tail _ hstep ih => exact absurd (ih ▸ hstep) (h _)
  subst heq
  omega

end EnumRules
