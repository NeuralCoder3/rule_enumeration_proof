/-
# Signatures with explicit variables

A `Signature` packages:
* `σ`: type of function symbols (with arities).
* `V`: type of variables (separate from `σ`).
* Decidable equality on both, so terms have decidable equality.
-/

structure Signature where
  σ      : Type
  V      : Type
  decEqσ : DecidableEq σ
  decEqV : DecidableEq V
  arity  : σ → Nat

attribute [instance] Signature.decEqσ Signature.decEqV
