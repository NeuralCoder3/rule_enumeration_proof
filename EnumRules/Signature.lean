import Mathlib.Data.Fintype.Basic

/-
# Signatures with explicit variables

A `Signature` packages:
* `σ`: finite type of function symbols (with arities).
* `V`: finite type of variables (separate from `σ`).
* Decidable equality on both, so terms have decidable equality.

`Fintype` instances are required so the algorithm's enumeration
(`termsFromIrreducible`) can produce concrete `Finset`s. (Without
finiteness the enumeration spec would be unsatisfiable: every variable
appears among terms of size 1.)
-/

structure Signature where
  σ        : Type
  V        : Type
  decEqσ   : DecidableEq σ
  decEqV   : DecidableEq V
  fintypeσ : Fintype σ
  fintypeV : Fintype V
  arity    : σ → Nat

attribute [instance] Signature.decEqσ Signature.decEqV
                     Signature.fintypeσ Signature.fintypeV
