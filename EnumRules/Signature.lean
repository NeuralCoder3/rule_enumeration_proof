import Mathlib.Data.Fintype.Basic

/-
# Signatures with explicit variables and ConstPlaceholders

A `Signature` packages:
* `σ`: finite type of function symbols (with arities).
* `V`: finite type of S.V variables (algorithm-internal placeholders;
  substituted by arbitrary terms at runtime).
* `C`: finite type of ConstPlaceholders (algorithm-internal stand-ins
  for new 0-ary symbols; substituted by extension symbols at runtime).
* Decidable equality on all three, so terms have decidable equality.

`Fintype` instances are required so the algorithm's enumeration
(`termsFromIrreducible`) can produce concrete `Finset`s.

At rule construction time, both `S.V` and `S.C` are used to write rule
schemas with two distinct kinds of placeholders. At runtime, signature
gets *extended* with new 0-ary symbols (modelled as an `Ext` parameter
to `Term`); rules' `S.V`-variables substitute with arbitrary runtime
terms, while rules' `S.C`-placeholders substitute only with extension
symbols.
-/

structure Signature where
  σ        : Type
  V        : Type
  C        : Type
  decEqσ   : DecidableEq σ
  decEqV   : DecidableEq V
  decEqC   : DecidableEq C
  fintypeσ : Fintype σ
  fintypeV : Fintype V
  fintypeC : Fintype C
  /-- A linear order on ConstPlaceholders. Used for renaming-orbit
  enumeration and for the canonical pullback of runtime extension
  symbols (`σ_of_embed`). -/
  linOrderC : LinearOrder C
  arity    : σ → Nat

attribute [instance] Signature.decEqσ Signature.decEqV Signature.decEqC
                     Signature.fintypeσ Signature.fintypeV Signature.fintypeC
                     Signature.linOrderC
