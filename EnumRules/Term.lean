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

/-- The Finset of extension symbols appearing in a term. Used to
state cardinality constraints (e.g., `|usedExt s ∪ usedExt t| ≤ |S.C|`
to lift `Term S Ext` terms into `Term S Empty`). -/
def usedExt [DecidableEq Ext] : Term S Ext → Finset Ext
  | .var _       => ∅
  | .constP _    => ∅
  | .node _ args =>
      (Finset.univ : Finset (Fin _)).biUnion (fun i => usedExt (args i))
  | .ext e       => {e}
termination_by structural t => t

@[simp] theorem usedExt_var [DecidableEq Ext] (v : S.V) :
    usedExt (Term.var (Ext := Ext) v) = ∅ := rfl

@[simp] theorem usedExt_constP [DecidableEq Ext] (c : S.C) :
    usedExt (Term.constP (Ext := Ext) c) = ∅ := rfl

@[simp] theorem usedExt_node [DecidableEq Ext] {f : S.σ}
    (args : Fin (S.arity f) → Term S Ext) :
    usedExt (Term.node f args) =
      (Finset.univ : Finset (Fin _)).biUnion (fun i => usedExt (args i)) := rfl

@[simp] theorem usedExt_ext [DecidableEq Ext] (e : Ext) :
    usedExt (Term.ext (S := S) e) = {e} := rfl

theorem usedExt_arg_subset [DecidableEq Ext] {f : S.σ}
    (args : Fin (S.arity f) → Term S Ext) (i : Fin (S.arity f)) :
    usedExt (args i) ⊆ usedExt (Term.node f args) := by
  intro e he
  simp only [usedExt_node, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, he⟩

/-- Embed a `Term S Ext` into `Term S Empty` by replacing each `ext e`
leaf with `constP (f e)`. Variables and ConstPlaceholders are preserved.
For `IsRuntime` input, the result has constP-leaves drawn from `f`'s
image and no variables. -/
def embExt (f : Ext → S.C) : Term S Ext → Term S Empty
  | .var v       => .var v
  | .constP c    => .constP c
  | .node f' args => .node f' (fun i => embExt f (args i))
  | .ext e       => .constP (f e)
termination_by structural t => t

@[simp] theorem embExt_var (f : Ext → S.C) (v : S.V) :
    embExt f (Term.var (Ext := Ext) v) = Term.var v := rfl

@[simp] theorem embExt_constP (f : Ext → S.C) (c : S.C) :
    embExt f (Term.constP (Ext := Ext) c) = Term.constP c := rfl

@[simp] theorem embExt_node (f : Ext → S.C) {f' : S.σ}
    (args : Fin (S.arity f') → Term S Ext) :
    embExt f (Term.node f' args) = Term.node f' (fun i => embExt f (args i)) := rfl

@[simp] theorem embExt_ext (f : Ext → S.C) (e : Ext) :
    embExt f (Term.ext (S := S) e) = Term.constP (f e) := rfl

/-- `embExt` preserves term size. -/
theorem size_embExt (f : Ext → S.C) (t : Term S Ext) :
    size (embExt f t) = size t := by
  induction t with
  | var v       => rfl
  | constP c    => rfl
  | node f' args ih =>
      simp only [embExt_node, size]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => ih i)
  | ext e       => rfl

/-- `embExt` preserves `NoVar`. -/
theorem NoVar_embExt (f : Ext → S.C) {t : Term S Ext} (h : NoVar t) :
    NoVar (embExt f t) := by
  induction t with
  | var v       => exact h.elim
  | constP c    => trivial
  | node f' args ih => intro i; exact ih i (h i)
  | ext e       => trivial

end Term
