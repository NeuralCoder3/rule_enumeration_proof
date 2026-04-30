/-
# Signatures

A `Signature` packages the symbol type together with an arity function
and a predicate identifying which symbols are variables (0-ary stand-in
constants). Decidable equality on symbols is assumed so that decidable
equality on terms can be derived.
-/

structure Signature where
  σ     : Type
  decEq : DecidableEq σ
  arity : σ → Nat
  isVar : σ → Bool

attribute [instance] Signature.decEq

/-- All variable symbols have arity 0 (they are constants). -/
axiom isVar_arity_zero {S : Signature} {a : S.σ} (h : S.isVar a) : S.arity a = 0

attribute [instance] Signature.decEq
