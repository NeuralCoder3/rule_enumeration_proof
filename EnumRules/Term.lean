import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import EnumRules.Signature

/-
# Terms with explicit variables, ConstPlaceholders, and extension symbols

Terms are built from four constructors:
* `var v` for `v : S.V` — an *S.V variable* (algorithm-internal
  placeholder; substituted at runtime with arbitrary terms).
* `constP c` for `c : S.C` — a *ConstPlaceholder* (algorithm-internal
  placeholder; substituted at runtime with new 0-ary extension symbols).
* `node f args` for `f : S.σ` — a *function application*.
* `ext e` for `e : Ext` — a *runtime extension symbol* (a "new" 0-ary
  symbol unknown at rule construction). Only appears at runtime
  (`Ext = Empty` during rule construction).

The `Ext` parameter discriminates rule-construction terms
(`Term S Empty`) from runtime terms (`Term S Ext` for some non-trivial
`Ext`). Runtime ground terms have no `var`/`constP` — the
`IsRuntime` predicate captures this.
-/

inductive Term (S : Signature) (Ext : Type) : Type where
  | var    (v : S.V) : Term S Ext
  | constP (c : S.C) : Term S Ext
  | node   (f : S.σ) (args : Fin (S.arity f) → Term S Ext) : Term S Ext
  | ext    (e : Ext) : Term S Ext

namespace Term

variable {S : Signature} {Ext : Type}

/-- Helper extensionality for argument-indexed term families. -/
theorem node_ext {f : S.σ} {as bs : Fin (S.arity f) → Term S Ext}
    (h : ∀ i, as i = bs i) : Term.node f as = Term.node f bs :=
  congrArg (Term.node f) (funext h)

noncomputable instance : DecidableEq (Term S Ext) := Classical.decEq _

/-- Size of a term: each leaf has size 1, function applications add 1
to the sum of subterm sizes. -/
def size : Term S Ext → Nat
  | .var _       => 1
  | .constP _    => 1
  | .node _ args => 1 + Finset.sum (Finset.univ : Finset (Fin _)) (fun i => size (args i))
  | .ext _       => 1
termination_by structural t => t

theorem size_pos (t : Term S Ext) : 1 ≤ size t := by
  cases t <;> simp [size]

theorem size_arg_lt (f : S.σ) (args : Fin (S.arity f) → Term S Ext) (i : Fin (S.arity f)) :
    size (args i) < size (Term.node f args) := by
  rw [size]
  have : size (args i) ≤ ∑ j, size (args j) :=
    Finset.single_le_sum (f := fun j => size (args j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- A term is *S.V/S.C-ground* (a *runtime term*) if it contains no
S.V variables and no ConstPlaceholders. May contain extension symbols
and function applications. -/
def IsRuntime : Term S Ext → Prop
  | .var _       => False
  | .constP _    => False
  | .node _ args => ∀ i, IsRuntime (args i)
  | .ext _       => True
termination_by structural t => t

/-- A term contains no S.V variables. ConstPlaceholders, function
applications, and extension symbols are all allowed.

This is the predicate on which `kbo_total` is sound: classical KBO is
total whenever there are no actual variables (constPs and exts behave
as 0-ary symbols with a precedence).

`IsRuntime → NoVar` (IsRuntime strictly stronger). At rule construction
time we have `NoVar`-but-not-`IsRuntime` terms (with constP-leaves);
at runtime, `IsRuntime` terms (with ext-leaves). KBO/smtMin reasoning
that works at both levels uses `NoVar`. -/
def NoVar : Term S Ext → Prop
  | .var _       => False
  | .constP _    => True
  | .node _ args => ∀ i, NoVar (args i)
  | .ext _       => True
termination_by structural t => t

/-- `IsRuntime → NoVar`. -/
theorem NoVar_of_IsRuntime {t : Term S Ext} : IsRuntime t → NoVar t := by
  induction t with
  | var v       => intro h; exact h.elim
  | constP c    => intro h; exact h.elim
  | node f args ih =>
      intro h j; exact ih j (h j)
  | ext e       => intro _; trivial

end Term
