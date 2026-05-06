import EnumRules.Term

/-
# Knuth-Bendix ordering (axiomatized)

We axiomatize the properties of KBO used by the correctness proof:
`kbo` is well-founded, transitive, total on ground terms, monotone under
one-hole contexts, and (with weight 1) never grows term size.
-/

namespace EnumRules

variable {S : Signature}

/-- Opaque KBO strict order on ground terms. -/
opaque kbo : Term S → Term S → Prop

@[inherit_doc kbo]
scoped infix:50 " ≺ₖ " => kbo

axiom kbo_wf : WellFounded (kbo : Term S → Term S → Prop)

axiom kbo_trans {a b c : Term S} : a ≺ₖ b → b ≺ₖ c → a ≺ₖ c

/-- KBO is total on ground terms. -/
axiom kbo_total (s t : Term S) : s = t ∨ s ≺ₖ t ∨ t ≺ₖ s

/-- KBO is monotone under one-hole contexts: rewriting a single argument
to a KBO-smaller term decreases the whole node. -/
axiom kbo_mono_ctx
    {f : S.σ} {as bs : Fin (S.arity f) → Term S} {i : Fin (S.arity f)}
    (hrest : ∀ j, j ≠ i → as j = bs j)
    (hlt : bs i ≺ₖ as i) :
    (Term.node f bs) ≺ₖ (Term.node f as)

/-- With all function symbols having weight 1, a KBO-smaller term
never exceeds the size of the larger term. -/
axiom kbo_size_le {s t : Term S} (h : s ≺ₖ t) : Term.size s ≤ Term.size t

end EnumRules
