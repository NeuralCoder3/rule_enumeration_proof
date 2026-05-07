import EnumRules.Equiv
import EnumRules.Kbo

/-
# Substitutions (concrete)

Substitutions are *functions* `S.V → Term S`. Substitution application,
identity, and composition are defined directly. The previously
"opaque" axioms `apply_id`, `apply_comp`, `apply_node` are now
**theorems** by structural induction.

The remaining axioms are about how `≈ₜ` and `≺ₖ` interact with
substitution — those are external to the substitution machinery itself.

## Axioms in this file (3)

* `kbo_subst : s ≺ₖ t → apply σ s ≺ₖ apply σ t` (substitution-monotonicity
  of the reduction order). KBO with positive weights satisfies this.
* `equiv_subst : s ≈ₜ t → apply σ s ≈ₜ apply σ t` (the SMT equivalence
  is closed under substitution).
* `equiv_rename : IsRenaming ρ → s ≈ₜ apply ρ s` (renaming variables
  preserves the SMT-equivalence class). Reflects that `Term.var v` is
  an algorithm-level placeholder; user-level "variables" are 0-ary
  nodes in `S.σ`. Note this is *not* derivable from `equiv_subst`,
  which only gives `apply ρ s ≈ₜ apply ρ s`.

These are not derivable from the structural definition of `apply`.
-/

namespace EnumRules

variable {S : Signature}

/-! ## Concrete substitutions -/

/-- A substitution is a function from variables to terms. -/
def Subst (S : Signature) : Type := S.V → Term S

/-- The identity substitution maps each variable to itself. -/
def Subst.id : Subst S := Term.var

/-- Apply a substitution to a term. -/
def apply (σ : Subst S) : Term S → Term S
  | .var v       => σ v
  | .node f args => .node f (fun i => apply σ (args i))
termination_by structural t => t

/-- Composition of substitutions: `(comp ρ σ) v = apply ρ (σ v)`. -/
def Subst.comp (ρ σ : Subst S) : Subst S := fun v => apply ρ (σ v)

instance : Inhabited (Subst S) := ⟨Subst.id⟩

@[simp]
theorem apply_var (σ : Subst S) (v : S.V) : apply σ (.var v) = σ v := rfl

@[simp]
theorem apply_node (σ : Subst S) {f : S.σ} (args : Fin (S.arity f) → Term S) :
    apply σ (.node f args) = .node f (fun i => apply σ (args i)) := rfl

/-! ### Identity acts trivially -/

theorem apply_id (t : Term S) : apply Subst.id t = t := by
  induction t with
  | var v => simp [Subst.id]
  | node f args ih =>
      show Term.node f (fun i => apply Subst.id (args i)) = Term.node f args
      congr 1; funext i; exact ih i

/-! ### Composition -/

theorem apply_comp (ρ σ : Subst S) (t : Term S) :
    apply (Subst.comp ρ σ) t = apply ρ (apply σ t) := by
  induction t with
  | var v => simp [Subst.comp]
  | node f args ih => simp [ih]

/-! ## Behavioural axioms -/

/-- Substitution-monotonicity of `≺ₖ`. KBO satisfies this. -/
axiom kbo_subst {s t : Term S} (h : s ≺ₖ t) (σ : Subst S) :
    apply σ s ≺ₖ apply σ t

/-- `≈ₜ` is closed under substitution. -/
axiom equiv_subst {s t : Term S} (h : s ≈ₜ t) (σ : Subst S) :
    apply σ s ≈ₜ apply σ t

/-! ## α-equivalence (renaming-equivalence)

A *renaming* is a substitution that maps each variable to a variable
and is bijective on `S.V`. We package this as: `ρ` is a renaming if
there exists a left and right inverse on every term. -/

def IsRenaming (ρ : Subst S) : Prop :=
  ∃ τ : Subst S, (∀ u : Term S, apply τ (apply ρ u) = u) ∧
                 (∀ u : Term S, apply ρ (apply τ u) = u)

/-- α-equivalence: terms differ only by a renaming. -/
def AlphaEquiv (s t : Term S) : Prop :=
  ∃ ρ : Subst S, IsRenaming ρ ∧ apply ρ s = t

@[inherit_doc AlphaEquiv]
scoped infix:50 " ≈ᵅ " => AlphaEquiv

theorem IsRenaming.id : IsRenaming (S := S) Subst.id :=
  ⟨Subst.id, fun u => by rw [apply_id, apply_id], fun u => by rw [apply_id, apply_id]⟩

theorem AlphaEquiv.refl (t : Term S) : t ≈ᵅ t :=
  ⟨Subst.id, IsRenaming.id, apply_id t⟩

/-! ## Irreducibility transfer (renaming preserves it) -/

theorem IsRenaming.preserves_irreducible {R : Term S → Term S → Prop} {s' : Term S}
    {ρ : Subst S} (hρ : IsRenaming ρ)
    (hstep_subst : ∀ {a b : Term S}, R a b → ∀ τ, R (apply τ a) (apply τ b))
    (hirr : ∀ u, ¬ R s' u) : ∀ u, ¬ R (apply ρ s') u := by
  rcases hρ with ⟨τ, hτL, _⟩
  intro u hstep
  have h := hstep_subst hstep τ
  rw [hτL] at h
  exact hirr (apply τ u) h

/-! ## Structural facts about renamings

A renaming maps each variable to a variable, preserves term size, and
its inverse is itself a renaming. These follow from the two-sided
inverse condition without further axioms. -/

/-- A renaming maps each variable to a variable. -/
theorem IsRenaming.var_to_var {ρ : Subst S} (hρ : IsRenaming ρ) (v : S.V) :
    ∃ v' : S.V, ρ v = Term.var v' := by
  rcases hρ with ⟨τ, hL, _⟩
  have h : apply τ (ρ v) = Term.var v := by
    have := hL (Term.var v); simpa using this
  generalize hρv : ρ v = w at h
  cases w with
  | var v'      => exact ⟨v', rfl⟩
  | node f args => simp [apply_node] at h

/-- The inverse of a renaming is itself a renaming. -/
theorem IsRenaming.flip {ρ : Subst S} (hρ : IsRenaming ρ) :
    ∃ τ : Subst S, IsRenaming τ ∧
      (∀ u, apply ρ (apply τ u) = u) ∧ (∀ u, apply τ (apply ρ u) = u) := by
  rcases hρ with ⟨τ, hL, hR⟩
  exact ⟨τ, ⟨ρ, hR, hL⟩, hR, hL⟩

/-- Renaming preserves term size: each variable maps to a variable
(size 1), and structural induction lifts this to all terms. -/
theorem apply_renaming_size {ρ : Subst S} (hρ : IsRenaming ρ) (t : Term S) :
    Term.size (apply ρ t) = Term.size t := by
  induction t with
  | var v =>
      rcases hρ.var_to_var v with ⟨v', hv'⟩
      simp [apply_var, hv', Term.size]
  | node f args ih =>
      simp only [apply_node, Term.size]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => ih i)

/-! ## α-equivariance of `≈ₜ`

`Term.var v` is an algorithm-level placeholder; relabelling variables
doesn't change the SMT-equivalence class. (User-level "variables" in
input formulas are 0-ary symbols of `S.σ`, not `Term.var`.) -/

/-- α-renaming preserves the `≈ₜ`-class. Distinct from `equiv_subst`,
which says `apply ρ s ≈ₜ apply ρ t` when `s ≈ₜ t`: this says every
term is `≈ₜ`-related to its renamings, even when the renaming is not
the identity. -/
axiom equiv_rename {ρ : Subst S} (hρ : IsRenaming ρ) (s : Term S) :
    s ≈ₜ apply ρ s

end EnumRules
