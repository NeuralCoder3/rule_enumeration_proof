import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import EnumRules.Rewrite

open scoped Classical

/-
# The enumeration algorithm

## Role
Defines the algorithm's data structures:
* `termsFromIrreducible` — enumeration of terms of a given size with
  subterms in a given set. Concrete `Finset` (no axiom).
* `Canonical` — opaque per-class representative-picking predicate.
* `R_can S n` — synthesised rule set after processing all sizes ≤ n.
* `I_can S n` — stored canonical irreducibles after processing all
  sizes ≤ n. `R_can` and `I_can` are mutually recursive on size.
* `ExtStep n` / `ExtStepStar n` — runtime operational steps:
  rule rewriting (`Step (R_can S n)`) and class lookup
  (`I_can S n`-anchored).

`CanonicalLayer.lean` proves the algorithm's properties on top of
these definitions (termination, soundness, ground-input
common-normal-form completeness).

## Axioms
None in this file. `mem_termsFromIrreducible` is now a theorem
derived from the concrete definition (which uses `Fintype S.σ` /
`Fintype S.V`).

## Opaque (1)
* `Canonical : Term S → Prop` — no behavioural axioms here. The proofs
  in `CanonicalLayer.lean` use one axiom about it (`canonical_of_ground`).
-/

namespace EnumRules

variable {S : Signature}

/-! ## Enumeration of terms by size -/

/-- Enumeration of terms of size `n` whose direct subterms (when the
term is a node) all belong to `subterms`. Variables — which carry no
node-decomposition — are included unconditionally and filtered by
size, which leaves them only at `n = 1`. -/
noncomputable def termsFromIrreducible (S : Signature)
    (subterms : Finset (Term S)) (n : Nat) : Finset (Term S) :=
  ((Finset.univ : Finset S.V).image Term.var ∪
    (Finset.univ : Finset S.σ).biUnion (fun f =>
      (Fintype.piFinset (fun _ : Fin (S.arity f) => subterms)).image (Term.node f))
  ).filter (fun t => Term.size t = n)

/-- Specification of `termsFromIrreducible`: a term `t` is in
`termsFromIrreducible S subterms n` iff its size is `n` and *every*
node-decomposition `t = Term.node f args` has `args i ∈ subterms`
(vacuous for variables). -/
theorem mem_termsFromIrreducible {subterms : Finset (Term S)} {n : Nat} {t : Term S} :
    t ∈ termsFromIrreducible S subterms n ↔
      Term.size t = n ∧
      ∀ (f : S.σ) (args : Fin (S.arity f) → Term S),
        Term.node f args = t → ∀ i, args i ∈ subterms := by
  simp only [termsFromIrreducible, Finset.mem_filter, Finset.mem_union,
             Finset.mem_image, Finset.mem_biUnion, Fintype.mem_piFinset,
             Finset.mem_univ, true_and]
  refine ⟨fun ⟨h, hsize⟩ => ⟨hsize, fun f' as' heq i => ?_⟩,
          fun ⟨hsize, h⟩ => ⟨?_, hsize⟩⟩
  · rcases h with ⟨v, hv⟩ | ⟨f, as, hin, hnode⟩
    · cases heq.trans hv.symm
    · injection heq.trans hnode.symm with hf has
      subst hf
      obtain rfl : as' = as := eq_of_heq has
      exact hin i
  · cases t with
    | var v => exact .inl ⟨v, rfl⟩
    | node f as => exact .inr ⟨f, as, fun i => h f as rfl i, rfl⟩

end EnumRules

namespace EnumRules

variable {S : Signature}

/-! ## Canonical filter and the synthesised rule / irreducible sets -/

/-- Canonicality predicate: a placeholder for any per-class
representative-picking filter. The proofs require only that ground
terms satisfy it (`canonical_of_ground` in `CanonicalLayer.lean`). -/
opaque Canonical : Term S → Prop

mutual
  /-- The synthesised rule set after processing all sizes `≤ n`. -/
  noncomputable def R_can (S : Signature) : Nat → RuleSet S
    | 0     => ∅
    | n + 1 => R_can S n ∪ (
        (termsFromIrreducible S (I_can S n) (n + 1)).filter (fun l =>
          Canonical l ∧ ¬ simplifiesWith (R_can S n) l ∧ smtMin l ≠ l)
          |>.image (fun l => (l, smtMin l)))

  /-- The stored canonical irreducible set after processing all sizes `≤ n`. -/
  noncomputable def I_can (S : Signature) : Nat → Finset (Term S)
    | 0     => ∅
    | n + 1 => I_can S n ∪ (
        (termsFromIrreducible S (I_can S n) (n + 1)).filter (fun l =>
          Canonical l ∧ ¬ simplifiesWith (R_can S n) l ∧ smtMin l = l))
end

/-! ## Runtime operational steps

The algorithm's two operational steps — neither invokes `smtMin` at
runtime; the SMT work is done at enumeration time when `R_can` and
`I_can` are constructed. -/

/-- Runtime operational step: either rule rewriting or class lookup. -/
inductive ExtStep (n : Nat) : Term S → Term S → Prop where
  /-- Standard rule rewriting (Phase 1). -/
  | rule {s t : Term S} (h : Step (R_can S n) s t) : ExtStep n s t
  /-- Equivalence-class step: from `t` to a stored `I_can` member
  `c ≈ₜ t`, where `t` itself is a substitution-instance of some
  `m ∈ I_can` (anchoring source and destination in the algorithm's
  stored irreducibles). -/
  | class_lookup {t c : Term S} {m : Term S} {σ : Subst S}
      (hm : m ∈ I_can S n) (h_inst : apply σ m = t)
      (hc : c ∈ I_can S n) (h_eq : t ≈ₜ c) :
      ExtStep n t c

/-- Reflexive-transitive closure of `ExtStep n`. -/
abbrev ExtStepStar (n : Nat) : Term S → Term S → Prop :=
  Relation.ReflTransGen (ExtStep (S := S) n)

end EnumRules
