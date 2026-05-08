import EnumRules.Equiv
import EnumRules.Kbo

/-
# Substitutions (concrete)

Substitutions are *functions* `S.V → Term S`. Substitution application
and identity are defined directly. The previously "opaque" axioms
`apply_id`, `apply_node` are now **theorems**.

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

instance : Inhabited (Subst S) := ⟨Subst.id⟩

@[simp]
theorem apply_var (σ : Subst S) (v : S.V) : apply σ (.var v) = σ v := rfl

@[simp]
theorem apply_node (σ : Subst S) {f : S.σ} (args : Fin (S.arity f) → Term S) :
    apply σ (.node f args) = .node f (fun i => apply σ (args i)) := rfl

/-! ### Identity acts trivially -/

theorem apply_id (t : Term S) : apply Subst.id t = t := by
  induction t with
  | var v => rfl
  | node f args ih => simp [apply_node, ih]

/-! ## Behavioural axioms -/

/-- Substitution-monotonicity of `≺ₖ`. KBO satisfies this. -/
axiom kbo_subst {s t : Term S} (h : s ≺ₖ t) (σ : Subst S) :
    apply σ s ≺ₖ apply σ t

/-- `≈ₜ` is closed under substitution. -/
axiom equiv_subst {s t : Term S} (h : s ≈ₜ t) (σ : Subst S) :
    apply σ s ≈ₜ apply σ t

end EnumRules
