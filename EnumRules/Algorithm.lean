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
node-decomposition — are included whenever `n = 1`. -/
noncomputable def termsFromIrreducible (S : Signature)
    (subterms : Finset (Term S)) : Nat → Finset (Term S)
  | 0     => ∅
  | n + 1 =>
      (if n = 0 then (Finset.univ : Finset S.V).image Term.var else ∅) ∪
      (Finset.univ : Finset S.σ).biUnion (fun f =>
        ((Fintype.piFinset (fun _ : Fin (S.arity f) => subterms)).filter
            (fun args => Term.size (Term.node f args) = n + 1)).image (Term.node f))

/-- Specification of `termsFromIrreducible`: a term `t` is in
`termsFromIrreducible S subterms n` iff its size is `n` and *every*
node-decomposition `t = Term.node f args` has `args i ∈ subterms`
(vacuous for variables). -/
theorem mem_termsFromIrreducible {subterms : Finset (Term S)} {n : Nat} {t : Term S} :
    t ∈ termsFromIrreducible S subterms n ↔
      Term.size t = n ∧
      ∀ (f : S.σ) (args : Fin (S.arity f) → Term S),
        Term.node f args = t → ∀ i, args i ∈ subterms := by
  match n with
  | 0 =>
      constructor
      · intro h
        simp [termsFromIrreducible] at h
      · intro hand
        exfalso
        have hsize : Term.size t = 0 := hand.1
        have hpos : 1 ≤ Term.size t := Term.size_pos t
        omega
  | n + 1 =>
      cases t with
      | var v =>
          unfold termsFromIrreducible
          rw [Finset.mem_union]
          constructor
          · rintro (hL | hR)
            · -- Var disjunct
              by_cases hn : n = 0
              · subst hn
                refine ⟨by simp [Term.size], fun f as heq => by cases heq⟩
              · rw [if_neg hn] at hL
                simp at hL
            · -- Node disjunct: impossible
              rw [Finset.mem_biUnion] at hR
              obtain ⟨f, _, hf⟩ := hR
              rw [Finset.mem_image] at hf
              obtain ⟨as, _, hnode⟩ := hf
              cases hnode
          · rintro ⟨hsize, _⟩
            left
            have hn : n = 0 := by simp [Term.size] at hsize; omega
            rw [if_pos hn]
            rw [Finset.mem_image]
            exact ⟨v, Finset.mem_univ _, rfl⟩
      | node f as =>
          unfold termsFromIrreducible
          rw [Finset.mem_union]
          constructor
          · rintro (hL | hR)
            · -- Var disjunct: contradiction
              by_cases hn : n = 0
              · rw [if_pos hn] at hL
                rw [Finset.mem_image] at hL
                obtain ⟨v, _, hcontra⟩ := hL
                cases hcontra
              · rw [if_neg hn] at hL
                simp at hL
            · -- Node disjunct
              rw [Finset.mem_biUnion] at hR
              obtain ⟨f', _, hf'⟩ := hR
              rw [Finset.mem_image] at hf'
              obtain ⟨bs, hargs', hnode⟩ := hf'
              rw [Finset.mem_filter, Fintype.mem_piFinset] at hargs'
              obtain ⟨hpi, hsize⟩ := hargs'
              injection hnode with hf heq
              subst hf
              have hbs_eq : bs = as := eq_of_heq heq
              rw [hbs_eq] at hpi hsize
              refine ⟨hsize, ?_⟩
              intro f₀ as₀ heq₀
              injection heq₀ with hf₀ heq₀'
              subst hf₀
              have has_eq : as₀ = as := eq_of_heq heq₀'
              rw [has_eq]
              exact hpi
          · rintro ⟨hsize, hsub⟩
            right
            rw [Finset.mem_biUnion]
            refine ⟨f, Finset.mem_univ _, ?_⟩
            rw [Finset.mem_image]
            refine ⟨as, ?_, rfl⟩
            rw [Finset.mem_filter, Fintype.mem_piFinset]
            exact ⟨fun i => hsub f as rfl i, hsize⟩

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
