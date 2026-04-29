import EnumRules.Term

/-
# Knuth-Bendix ordering (axiomatized)

We axiomatize the properties of KBO that the algorithm's correctness
proof relies on. Concretely: `kbo` is a well-founded, irreflexive,
transitive, context-monotone strict order that is total on ground terms.

All function symbols have weight 1, so KBO-smaller terms are never
larger in size.
-/

namespace EnumRules

variable {S : Signature}

/-- Opaque KBO strict order on ground terms. -/
opaque kbo : Term S → Term S → Prop

@[inherit_doc kbo]
scoped infix:50 " ≺ₖ " => kbo

axiom kbo_wf : WellFounded (kbo : Term S → Term S → Prop)

axiom kbo_irrefl (t : Term S) : ¬ (t ≺ₖ t)

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

/-- A proper subterm is strictly KBO-smaller than the enclosing node. -/
axiom kbo_subterm {f : S.σ} {args : Fin (S.arity f) → Term S} {i : Fin (S.arity f)} :
    (args i) ≺ₖ (Term.node f args)

end EnumRules
