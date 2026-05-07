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

## Axioms in this file (2)

* `kbo_subst : s ≺ₖ t → apply σ s ≺ₖ apply σ t` (substitution-monotonicity
  of the reduction order). KBO with positive weights satisfies this.
* `equiv_subst : s ≈ₜ t → apply σ s ≈ₜ apply σ t` (the SMT equivalence
  is closed under substitution).

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

/-! ## Ground terms are fixed by substitution

User-level "variables" in input formulas are 0-ary symbols of `S.σ`,
*not* `Term.var v`. Runtime inputs are therefore S.V-ground, and
substitution is the identity on them. -/

/-- Substitution is the identity on ground terms. -/
theorem apply_ground {σ : Subst S} {t : Term S} (h : Term.IsGround t) :
    apply σ t = t := by
  induction t with
  | var v       => exact h.elim
  | node f args ih =>
      rw [apply_node]
      congr 1
      funext i
      exact ih i (h i)

end EnumRules
