import EnumRules.Term

/-
# Knuth-Bendix ordering (axiomatized)

## Role
The reduction order `≺ₖ`. Rewrite rules `(l, r)` satisfy `r ≺ₖ l`,
making one-step rewriting `≺ₖ`-decreasing — hence terminating by
well-foundedness.

## Axioms (5)

All hold for KBO over any signature.

* `kbo_wf` — well-founded.
* `kbo_trans` — transitive.
* `kbo_total` — total on ground terms (every two ground terms are
  comparable or equal). Sound for ground terms; we use it via
  `smtMin_resp` to derive uniqueness of `smtMin` per `≈ₜ`-class.
* `kbo_mono_ctx` — monotone under one-hole contexts.
* `kbo_size_le` — `≺ₖ` doesn't grow size (with positive weights).
-/

namespace EnumRules

variable {S : Signature}

opaque kbo : Term S → Term S → Prop

@[inherit_doc kbo]
scoped infix:50 " ≺ₖ " => kbo

axiom kbo_wf : WellFounded (kbo : Term S → Term S → Prop)

axiom kbo_trans {a b c : Term S} : a ≺ₖ b → b ≺ₖ c → a ≺ₖ c

axiom kbo_total (s t : Term S) : s = t ∨ s ≺ₖ t ∨ t ≺ₖ s

axiom kbo_mono_ctx
    {f : S.σ} {as bs : Fin (S.arity f) → Term S} {i : Fin (S.arity f)}
    (hrest : ∀ j, j ≠ i → as j = bs j)
    (hlt : bs i ≺ₖ as i) :
    (Term.node f bs) ≺ₖ (Term.node f as)

axiom kbo_size_le {s t : Term S} (h : s ≺ₖ t) : Term.size s ≤ Term.size t

end EnumRules
