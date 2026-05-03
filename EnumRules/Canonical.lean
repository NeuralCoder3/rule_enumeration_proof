import EnumRules.Rewrite

/-
# Canonical terms (Algorithm 3)

To avoid enumerating many terms that differ only by renaming of variable
(nullary) symbols, we restrict the enumeration to *canonical* terms — one
representative from each `≈ᵣ`-equivalence class.

Renaming `≈ᵣ` is an equivalence relation.  `Canonical t` holds when `t`
is the designated representative of its `≈ᵣ`-class.

Key axioms:
- Every term has a canonical renaming.
- Renaming preserves size, `smtMin` (up to renaming), and term structure.
-/

namespace EnumRules

variable {S : Signature}

/-- Two ground terms are equivalent under renaming (`≈ᵣ`) if they differ
only by a consistent renaming of variable symbols. -/
opaque Rename : Term S → Term S → Prop

@[inherit_doc Rename]
scoped infix:50 " ≈ᵣ " => Rename

axiom rename_refl (t : Term S) : t ≈ᵣ t

axiom rename_symm {s t : Term S} : s ≈ᵣ t → t ≈ᵣ s

axiom rename_trans {s t u : Term S} : s ≈ᵣ t → t ≈ᵣ u → s ≈ᵣ u

/-- A term is *canonical* if it is the designated representative of its
`≈ᵣ`-equivalence class. -/
opaque Canonical : Term S → Prop

/-- Every term has a canonical renaming. -/
axiom exists_canonical (t : Term S) : ∃ t', t ≈ᵣ t' ∧ Canonical t'

/-- Renaming does not change the size of a term. -/
axiom rename_size {s t : Term S} (h : s ≈ᵣ t) : Term.size s = Term.size t

/-- The SMT oracle commutes with renaming up to renaming. -/
axiom rename_smtMin {s t : Term S} (h : s ≈ᵣ t) : smtMin s ≈ᵣ smtMin t

theorem rename_smtMin_symm {s t : Term S} (h : s ≈ᵣ t) : smtMin t ≈ᵣ smtMin s :=
  rename_symm (rename_smtMin h)

/-- Renaming is a congruence: renaming subterms yields a renamed node. -/
axiom rename_congr {f : S.σ} {as bs : Fin (S.arity f) → Term S}
    (h : ∀ i, as i ≈ᵣ bs i) : (Term.node f as) ≈ᵣ (Term.node f bs)

/-- If all arguments are canonical, the node is canonical. -/
axiom canonical_node {f : S.σ} {args : Fin (S.arity f) → Term S}
    (h : ∀ i, Canonical (args i)) : Canonical (Term.node f args)

/-- The canonical version of a minimal term is minimal:
if `t` is canonical and `smtMin t ≈ᵣ t`, then `smtMin t = t`. -/
axiom canonical_minimal {t : Term S} (hcan : Canonical t)
    (h : smtMin t ≈ᵣ t) : smtMin t = t

/-- A canonical renaming is `≈ₜ`-equivalent to the original term. -/
axiom canonical_equiv {t t' : Term S} (hcan : Canonical t') (hren : t ≈ᵣ t') : t ≈ₜ t'

/-! ## Abstract interface for renaming models

The class `Renaming` bundles all renaming‑related axioms so that concrete
models (like `EnumRules.Concrete`) can be instances. -/

/-- A `Renaming` model for terms of type `α` over function symbols `σ`
with arities `arity`. -/
class Renaming (α σ : Type) (arity : σ → ℕ) where
  /-- Renaming equivalence. -/
  Rename : α → α → Prop
  /-- Renaming is reflexive. -/
  rename_refl (t : α) : Rename t t
  /-- Renaming is symmetric. -/
  rename_symm {s t : α} : Rename s t → Rename t s
  /-- Renaming is transitive. -/
  rename_trans {s t u : α} : Rename s t → Rename t u → Rename s u
  /-- A term is canonical if it is the designated representative of its
  renaming class. -/
  Canonical : α → Prop
  /-- Every term has a canonical renaming. -/
  exists_canonical (t : α) : ∃ t', Rename t t' ∧ Canonical t'
  /-- Size of a term. -/
  size : α → ℕ
  /-- Renaming preserves size. -/
  rename_size {s t : α} (h : Rename s t) : size s = size t
  /-- Construct a node from a function symbol and arguments. -/
  node (f : σ) (args : Fin (arity f) → α) : α
  /-- A type of renaming witnesses (e.g. `Equiv.Perm V` in a concrete
  model, `Unit` in the abstract theory). -/
  rename_witness : Type
  /-- Apply a witness to a term. -/
  rename_apply (r : rename_witness) (t : α) : α
  /-- A witness relates a term to its renaming. -/
  rename_of_witness (r : rename_witness) (t : α) : Rename t (rename_apply r t)
  /-- Renaming is a congruence under nodes (same witness). -/
  rename_congr (r : rename_witness) {f : σ} {as bs : Fin (arity f) → α}
    (h : ∀ i, rename_apply r (as i) = bs i) : Rename (node f as) (node f bs)
  /-- A node of canonical subterms is canonical. -/
  canonical_node {f : σ} {args : Fin (arity f) → α}
    (h : ∀ i, Canonical (args i)) : Canonical (node f args)

/-- The abstract `Term S` over the ambient `Signature` satisfies `Renaming`
via the opaque declarations above.  (This is a restatement, not a proof —
the axioms are assumed.) -/
instance (S : Signature) : Renaming (Term S) S.σ S.arity where
  Rename := Rename
  rename_refl := rename_refl
  rename_symm := rename_symm
  rename_trans := rename_trans
  Canonical := Canonical
  exists_canonical := exists_canonical
  size := Term.size
  rename_size := rename_size
  node := Term.node
  rename_witness := Unit
  rename_apply _ t := t
  rename_of_witness _ t := rename_refl t
  rename_congr r {f as bs} h := by
    -- h : ∀ i, rename_apply r (as i) = bs i, i.e., as i = bs i
    -- So rename_congr follows from the original axiom
    have h' : ∀ i, (as i) ≈ᵣ (bs i) := by
      intro i; rw [h i]; exact rename_refl _
    exact rename_congr h'
  canonical_node := canonical_node

/-- Extended one-step rewriting that also allows renaming steps.
Rules can be applied on non‑canonical terms by matching modulo `≈ᵣ`. -/
inductive StepR (R : RuleSet S) : Term S → Term S → Prop where
  | step {s t : Term S} : Step R s t → StepR R s t
  | rename {s t : Term S} : s ≈ᵣ t → StepR R s t

/-- Reflexive-transitive closure of `StepR`. -/
abbrev StepStarR (R : RuleSet S) : Term S → Term S → Prop :=
  Relation.ReflTransGen (StepR R)

namespace StepR

/-- Lifting a `StepR` to a larger rule set. -/
theorem lift {R₁ R₂ : RuleSet S} (hR : R₁ ⊆ R₂) {s t : Term S}
    (h : StepR R₁ s t) : StepR R₂ s t := by
  induction h with
  | step hstep => exact StepR.step (Step.lift hR hstep)
  | rename hren => exact StepR.rename hren

end StepR

namespace StepStarR

/-- Lifting a `StepStarR` to a larger rule set. -/
theorem lift {R₁ R₂ : RuleSet S} (hR : R₁ ⊆ R₂) {s t : Term S}
    (h : StepStarR R₁ s t) : StepStarR R₂ s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (StepR.lift hR hstep)

/-- Contextual closure of `StepStarR`: reducing a subterm via `StepStarR`
reduces the whole node. -/
theorem ctx {R : RuleSet S} {f : S.σ}
    {args : Fin (S.arity f) → Term S} {i : Fin (S.arity f)} {v : Term S}
    (h : StepStarR R (args i) v) :
    StepStarR R (Term.node f args)
      (Term.node f (fun j => if j = i then v else args j)) := by
  match h with
  | Relation.ReflTransGen.refl =>
    have h_eq : (fun j : Fin (S.arity f) => if j = i then args i else args j) = args := by
      funext j; dsimp; split_ifs with h
      · subst h; rfl
      · rfl
    simpa [h_eq] using (Relation.ReflTransGen.refl : StepStarR R (Term.node f args) (Term.node f args))
  | Relation.ReflTransGen.tail hprefix hstep =>
    rename_i b
    have ih := ctx hprefix
    have hlast : StepR R
        (Term.node f (fun j => if j = i then b else args j))
        (Term.node f (fun j => if j = i then v else args j)) := by
      let as' := fun j => if j = i then b else args j
      let bs' := fun j => if j = i then v else args j
      rcases hstep with (hstep' | hren)
      · -- inner step: Step R b v
        have hrest' : ∀ j, j ≠ i → as' j = bs' j := by
          intro j hj; simp [as', bs', hj]
        have hstep_at_i : Step R (as' i) (bs' i) := by
          simpa [as', bs'] using hstep'
        exact StepR.step (Step.ctx (as := as') (bs := bs') (i := i) hstep_at_i hrest')
      · -- inner renaming: b ≈ᵣ v
        have h_all : ∀ j, as' j ≈ᵣ bs' j := by
          intro j
          dsimp [as', bs']
          split_ifs with h
          · subst h; exact hren
          · exact rename_refl _
        exact StepR.rename (rename_congr h_all)
    exact Relation.ReflTransGen.tail ih hlast

end StepStarR

end EnumRules
