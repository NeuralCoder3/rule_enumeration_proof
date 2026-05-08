import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import EnumRules.Signature

/-
# Terms with explicit variables

Terms are built from:
* `var v` for `v : S.V` — a *variable* (algorithm-internal placeholder
  used in rule schemas; substituted by `apply σ`).
* `node f args` for `f : S.σ` — a *function application* with the
  right number of argument terms.

User-level variables in input formulas are 0-ary symbols of `S.σ`,
*not* `Term.var v`. So runtime inputs are S.V-ground (`IsGround`).
The `Term.var` constructor exists to write rule schemas that
generalise across substitutions.
-/

inductive Term (S : Signature) : Type where
  | var  (v : S.V) : Term S
  | node (f : S.σ) (args : Fin (S.arity f) → Term S) : Term S

namespace Term

variable {S : Signature}

/-- Helper extensionality for argument-indexed term families. -/
theorem node_ext {f : S.σ} {as bs : Fin (S.arity f) → Term S}
    (h : ∀ i, as i = bs i) : Term.node f as = Term.node f bs := by
  have : as = bs := funext h
  simp [this]

noncomputable instance : DecidableEq (Term S) := by
  classical
  exact inferInstance

/-- Size of a term: variables have size 1, function applications add 1
to the sum of subterm sizes. -/
def size : Term S → Nat
  | .var _      => 1
  | .node _ args => 1 + Finset.sum (Finset.univ : Finset (Fin _)) (fun i => size (args i))
termination_by structural t => t

theorem size_pos (t : Term S) : 1 ≤ size t := by
  cases t with
  | var _   => simp [size]
  | node _ _ => simp [size]

theorem size_arg_lt (f : S.σ) (args : Fin (S.arity f) → Term S) (i : Fin (S.arity f)) :
    size (args i) < size (Term.node f args) := by
  rw [size]
  have hsum : size (args i) ≤ Finset.sum (Finset.univ : Finset (Fin (S.arity f))) (fun j => size (args j)) :=
    Finset.single_le_sum (f := fun j => size (args j))
      (by intro j _; exact Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- A term is *ground* if it contains no variables. -/
def IsGround : Term S → Prop
  | .var _      => False
  | .node _ args => ∀ i, IsGround (args i)
termination_by structural t => t

end Term
