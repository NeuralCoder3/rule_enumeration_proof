import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import EnumRules.Signature

/-
# Ground terms over a signature

## Role
Inductive `Term S` and a `size` function. Variables are modelled as
0-ary symbols (the algorithm's "var-constants"). `size_arg_lt` is the
key fact powering size-induction in `Algorithm.lean` / `Correctness.lean`.

## Axioms
None. Pure inductive type + structural recursion.
-/

inductive Term (S : Signature) : Type where
  | node (f : S.σ) (args : Fin (S.arity f) → Term S) : Term S

namespace Term

variable {S : Signature}

/-- Helper extensionality for argument-indexed term families. -/
theorem node_ext {f : S.σ} {as bs : Fin (S.arity f) → Term S}
    (h : ∀ i, as i = bs i) : Term.node f as = Term.node f bs := by
  have : as = bs := funext h
  simp [this]

/-- Decidable equality for ground terms using classical logic. -/
noncomputable instance : DecidableEq (Term S) := by
  classical
  exact inferInstance

/-- Size of a term: 1 plus the sum of the sizes of its arguments. -/
def size : Term S → Nat
  | .node _ args =>
    1 + Finset.sum (Finset.univ : Finset (Fin _)) (fun i => size (args i))
termination_by structural t => t

/-- Every term has size at least 1. -/
theorem size_pos (t : Term S) : 1 ≤ size t := by
  cases t with
  | node _ _ =>
    simp [size]

/-- A direct argument is strictly smaller than the enclosing node. -/
theorem size_arg_lt (f : S.σ) (args : Fin (S.arity f) → Term S) (i : Fin (S.arity f)) :
    size (args i) < size (Term.node f args) := by
  rw [size]
  have hsum : size (args i) ≤ Finset.sum (Finset.univ : Finset (Fin (S.arity f))) (fun j => size (args j)) :=
    Finset.single_le_sum (by
      intro j _
      exact Nat.zero_le (size (args j))) (Finset.mem_univ i)
  omega

end Term
