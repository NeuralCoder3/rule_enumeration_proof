/-
# Signatures

## Role
Bundle a symbol type `σ` with an arity function. The base of the term
language: every term is a function symbol applied to its arity-many
arguments.

## Axioms
None. Decidable equality on `σ` is a structure field, not an axiom.
-/

structure Signature where
  σ     : Type
  decEq : DecidableEq σ
  arity : σ → Nat

attribute [instance] Signature.decEq
