import EnumRules.Term

/-
# Knuth-Bendix ordering (axiomatized)

## Role
The reduction order `≺ₖ`. Rewrite rules `(l, r)` satisfy `r ≺ₖ l`,
making one-step rewriting `≺ₖ`-decreasing — hence terminating by
well-foundedness.

## Axioms (5)

* `kbo_wf` — well-founded.
* `kbo_trans` — transitive.
* `kbo_total` — totality on **ground** terms (`IsGround` hypothesis).
  Classical KBO is partial on terms with variables (distinct
  `Term.var` are KBO-incomparable); restricting the axiom to ground
  inputs keeps it sound. Used in `smtMin_resp` for uniqueness of
  `smtMin` per `≈ₜ`-class on ground inputs.
* `kbo_mono_ctx` — monotone under one-hole contexts.
* `kbo_size_le` — `≺ₖ` doesn't grow size (with positive weights).
-/

namespace EnumRules

variable {S : Signature}

/-- Knuth-Bendix ordering (≺ₖ) on terms.
  This relation is provided axiomatically (opaque) and is used as the
  reduction order for rewrite rules.
-/
opaque kbo : Term S → Term S → Prop

@[inherit_doc kbo]
scoped infix:50 " ≺ₖ " => kbo

axiom kbo_wf : WellFounded (kbo : Term S → Term S → Prop)

axiom kbo_trans {a b c : Term S} : a ≺ₖ b → b ≺ₖ c → a ≺ₖ c

axiom kbo_total {s t : Term S}
    (hs : Term.IsGround s) (ht : Term.IsGround t) :
    s = t ∨ s ≺ₖ t ∨ t ≺ₖ s

axiom kbo_mono_ctx
    {f : S.σ} {as bs : Fin (S.arity f) → Term S} {i : Fin (S.arity f)}
    (hrest : ∀ j, j ≠ i → as j = bs j)
    (hlt : bs i ≺ₖ as i) :
    (Term.node f bs) ≺ₖ (Term.node f as)

axiom kbo_size_le {s t : Term S} (h : s ≺ₖ t) : Term.size s ≤ Term.size t

end EnumRules
