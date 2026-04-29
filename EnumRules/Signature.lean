/-
# Signatures

A `Signature` packages the symbol type together with an arity function.
Decidable equality on symbols is assumed so that decidable equality on
terms can be derived.
-/

structure Signature where
  σ     : Type
  decEq : DecidableEq σ
  arity : σ → Nat

attribute [instance] Signature.decEq
