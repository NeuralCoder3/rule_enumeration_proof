import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import EnumRules.Canonical

/-
# Concrete model: consistent renaming via variable bijections

`Term' V F arity` is a simple term language with variables in `V` and
function symbols whose arities are given by `arity : F → ℕ`.
Renaming is a permutation of `V` applied homomorphically.

This module provides a `Renaming` instance for `Term'`, proving that
the usual consistent renaming satisfies the axioms of `Canonical.lean`.
-/

namespace EnumRules.Concrete

/-! ## Terms with explicit variables -/

inductive Term' (V : Type) (F : Type) (arity : F → ℕ) : Type
  | var (v : V)
  | node (f : F) (args : Fin (arity f) → Term' V F arity)

variable {V : Type}
variable {F : Type} {arity : F → ℕ}

namespace Term'

open Finset

/-- Size of a term. -/
def size : Term' V F arity → Nat
  | var _ => 1
  | node _ args => 1 + ∑ i : Fin _, size (args i)

theorem size_pos (t : Term' V F arity) : 1 ≤ size t := by
  induction t with
  | var v => simp [size]
  | node f args =>
    rw [size]
    omega

theorem size_arg_lt {f : F} {args : Fin (arity f) → Term' V F arity} {i : Fin (arity f)} :
    size (args i) < size (node f args) := by
  rw [size]
  have hpos : ∀ j, 0 ≤ size (args j) := fun j => by
    have := size_pos (args j); omega
  have h : size (args i) ≤ ∑ j : Fin (arity f), size (args j) :=
    single_le_sum (fun j _ => hpos j) (mem_univ i)
  omega

/-! ## Renaming = permutation of V applied everywhere -/

def rename (ρ : Equiv.Perm V) : Term' V F arity → Term' V F arity
  | var v   => var (ρ v)
  | node f args => node f (fun i => rename ρ (args i))

def RenameRel (s t : Term' V F arity) : Prop :=
  ∃ ρ : Equiv.Perm V, rename ρ s = t

theorem rename_id (t : Term' V F arity) : rename (Equiv.refl V) t = t := by
  induction t with
  | var v => simp [rename]
  | node f args ih => simp [rename, ih]

theorem rename_refl (t : Term' V F arity) : RenameRel t t :=
  ⟨Equiv.refl V, rename_id t⟩

theorem rename_comp (ρ₁ ρ₂ : Equiv.Perm V) (t : Term' V F arity) :
    rename ρ₂ (rename ρ₁ t) = rename (ρ₁.trans ρ₂) t := by
  induction t with
  | var v => simp [rename]
  | node f args ih => simp [rename, ih]

theorem rename_symm' {ρ : Equiv.Perm V} {s t : Term' V F arity}
    (h : rename ρ s = t) : rename ρ.symm t = s := by
  rw [← h, rename_comp, Equiv.self_trans_symm, rename_id]

theorem rename_symm {s t : Term' V F arity} (h : RenameRel s t) : RenameRel t s := by
  rcases h with ⟨ρ, h⟩; exact ⟨ρ.symm, rename_symm' h⟩

theorem rename_trans {s t u : Term' V F arity}
    (h₁ : RenameRel s t) (h₂ : RenameRel t u) : RenameRel s u := by
  rcases h₁ with ⟨ρ₁, h₁⟩; rcases h₂ with ⟨ρ₂, h₂⟩
  refine ⟨ρ₁.trans ρ₂, ?_⟩
  rw [← h₂, ← h₁, rename_comp]

theorem rename_size (ρ : Equiv.Perm V) (t : Term' V F arity) : size (rename ρ t) = size t := by
  induction t with
  | var v => rfl
  | node f args ih => simp [rename, size, ih]

theorem rename_rel_size {s t : Term' V F arity} (h : RenameRel s t) : size s = size t := by
  rcases h with ⟨ρ, h⟩; rw [← h, rename_size]

/-- RenameRel congruence under the SAME permutation. -/
theorem renamerel_congr_same_ρ (ρ : Equiv.Perm V) (f : F)
    {as bs : Fin (arity f) → Term' V F arity}
    (h : ∀ i, rename ρ (as i) = bs i) : RenameRel (node f as) (node f bs) := by
  refine ⟨ρ, ?_⟩
  simp [rename]; apply funext; exact h

/-- RenameRel congruence: if each subterm is rename‑equivalent to its
counterpart, and the same ρ witnesses all of them, then the nodes are
rename‑equivalent.  (This is the interpretation needed for the
`Renaming` class; we require a common ρ.) -/
theorem renamerel_congr {f : F} {as bs : Fin (arity f) → Term' V F arity}
    (ρ : Equiv.Perm V) (h : ∀ i, rename ρ (as i) = bs i) :
    RenameRel (node f as) (node f bs) :=
  renamerel_congr_same_ρ ρ _ h

/-! ## Canonical terms (all terms are canonical for simplicity) -/

def Canonical' (_t : Term' V F arity) : Prop := True

theorem exists_canonical (t : Term' V F arity) : ∃ t', RenameRel t t' ∧ Canonical' t' :=
  ⟨t, rename_refl t, trivial⟩

theorem canonical_node {f : F} {args : Fin (arity f) → Term' V F arity}
    (_h : ∀ i, Canonical' (args i)) : Canonical' (node f args) := trivial

/-! ## `Renaming` instance -/

/-- `Term' V F arity` with permutation‑renaming satisfies `Renaming`. -/
noncomputable instance : Renaming (Term' V F arity) F arity where
  Rename := RenameRel
  rename_refl := rename_refl
  rename_symm := rename_symm
  rename_trans := rename_trans
  Canonical := Canonical'
  exists_canonical := exists_canonical
  size := size
  rename_size := rename_rel_size
  node := node
  rename_witness := Equiv.Perm V
  rename_apply := rename
  rename_of_witness ρ _t := ⟨ρ, rfl⟩
  rename_congr := fun ρ {f _as _bs} h => renamerel_congr_same_ρ ρ f h
  canonical_node := canonical_node

end Term'

end EnumRules.Concrete
