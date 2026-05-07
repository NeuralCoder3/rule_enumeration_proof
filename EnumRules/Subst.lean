import EnumRules.Equiv
import EnumRules.Kbo
import EnumRules.Oracle

/-
# Substitutions and α-equivalence

## Role
Abstract type `Subst S` with action `apply σ t`. Substitutions enter the
proof in two roles: rules fire under any substitution (`Step.root σ` in
Rewrite.lean), and α-equivalence is built from invertible substitutions.

## Axioms (8 total)

Type-level (3 opaques):
* `Subst : Type`, `idSubst : Subst S`, `apply : Subst S → Term S → Term S`,
  `Subst.comp : Subst S → Subst S → Subst S`.

Behavioural (8):
* `Subst.nonempty` — `Subst S` inhabited.
* `apply_id : apply (idSubst S) t = t` — identity acts trivially.
* `kbo_subst : s ≺ₖ t → apply σ s ≺ₖ apply σ t` — order is substitution-monotone.
* `equiv_subst : s ≈ₜ t → apply σ s ≈ₜ apply σ t` — `≈ₜ` is closed under substitution.
* `apply_comp : apply (Subst.comp ρ σ) t = apply ρ (apply σ t)`.
* `apply_node : apply σ (Term.node f args) = Term.node f (apply σ ∘ args)`.
* `smtMin_subst : smtMin (apply σ t) = apply σ (smtMin t)` — smtMin commutes
  with substitution. The crucial new axiom: it makes the bridge a *theorem*
  rather than a hypothesis.
* `smtMin_resp_alpha : s ≈ₜ t → ∃ ρ, IsRenaming ρ ∧ apply ρ (smtMin s) = smtMin t`
  — `≈ₜ`-equivalent inputs have α-equivalent (renaming-related) `smtMin`s.
  Stronger than `≈ₜ`-equivalence (which is automatic), weaker than equality.

Holds for every signature whose `≈ₜ`-classes are renaming-mediated
(non-commutative, pure-commutativity). For richer theories (AC) the
axiom would be unsound — it's the natural strength point.
-/

namespace EnumRules

variable {S : Signature}

/-! ## Substitutions -/

opaque Subst (S : Signature) : Type

axiom Subst.nonempty (S : Signature) : Nonempty (Subst S)

instance (S : Signature) : Nonempty (Subst S) := Subst.nonempty S

instance : Nonempty (Subst S → Term S → Term S) := ⟨fun _ t => t⟩

noncomputable opaque apply : Subst S → Term S → Term S

noncomputable opaque idSubst (S : Signature) : Subst S

axiom apply_id (t : Term S) : apply (idSubst S) t = t

axiom kbo_subst {s t : Term S} (h : s ≺ₖ t) (σ : Subst S) :
    apply σ s ≺ₖ apply σ t

axiom equiv_subst {s t : Term S} (h : s ≈ₜ t) (σ : Subst S) :
    apply σ s ≈ₜ apply σ t

noncomputable opaque Subst.comp : Subst S → Subst S → Subst S

axiom apply_comp (ρ σ : Subst S) (t : Term S) :
    apply (Subst.comp ρ σ) t = apply ρ (apply σ t)

axiom apply_node {f : S.σ} (args : Fin (S.arity f) → Term S) (σ : Subst S) :
    apply σ (Term.node f args) = Term.node f (fun i => apply σ (args i))

/-- `smtMin` commutes with substitution. The key new axiom that promotes
the bridge from a hypothesis to a theorem. -/
axiom smtMin_subst (σ : Subst S) (t : Term S) :
    smtMin (apply σ t) = apply σ (smtMin t)

/-! ## α-equivalence (renaming-equivalence)

A *renaming* substitution is one with a global left inverse — invertible
on every term, not just on a single one. The α-equivalence relation
asks for a renaming witness. -/

/-- A substitution is a *renaming* if it has a global left inverse. -/
def IsRenaming (ρ : Subst S) : Prop :=
  ∃ τ : Subst S, ∀ u : Term S, apply τ (apply ρ u) = u

/-- α-equivalence: `t = apply ρ s` for some invertible (renaming) `ρ`. -/
def AlphaEquiv (s t : Term S) : Prop :=
  ∃ ρ : Subst S, IsRenaming ρ ∧ apply ρ s = t

@[inherit_doc AlphaEquiv]
scoped infix:50 " ≈ᵅ " => AlphaEquiv

theorem IsRenaming.id : IsRenaming (idSubst S) :=
  ⟨idSubst S, fun u => by rw [apply_id, apply_id]⟩

theorem AlphaEquiv.refl (t : Term S) : t ≈ᵅ t :=
  ⟨idSubst S, IsRenaming.id, apply_id t⟩

/-- `≈ₜ`-equivalent terms have α-equivalent `smtMin`s. The output is
determined up to renaming (variable-permutation), not arbitrary `≈ₜ`. -/
axiom smtMin_resp_alpha {s t : Term S} (h : s ≈ₜ t) :
    ∃ ρ : Subst S, IsRenaming ρ ∧ apply ρ (smtMin s) = smtMin t

/-! ## Irreducibility transfer (renaming preserves it) -/

theorem IsRenaming.preserves_irreducible {R : Term S → Term S → Prop} {s' : Term S}
    {ρ : Subst S} (hρ : IsRenaming ρ)
    (hstep_subst : ∀ {a b : Term S}, R a b → ∀ τ, R (apply τ a) (apply τ b))
    (hirr : ∀ u, ¬ R s' u) : ∀ u, ¬ R (apply ρ s') u := by
  rcases hρ with ⟨τ, hτ⟩
  intro u hstep
  have h := hstep_subst hstep τ
  rw [hτ] at h
  exact hirr (apply τ u) h

end EnumRules
