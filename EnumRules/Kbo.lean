import EnumRules.Term

/-
# Knuth-Bendix ordering (parameterised by extension)

## Role
The reduction order `≺ₖ`, indexed by the runtime extension type
`Ext`. Rewrite rules `(l, r) ∈ Term S Empty × Term S Empty` satisfy
`r ≺ₖ l` at construction time; substitution-monotonicity (Subst.lean)
lifts this to runtime instances in `Term S Ext`.

## Axioms (5) — each is a family indexed by `Ext`

* `kbo_wf` — well-founded.
* `kbo_trans` — transitive.
* `kbo_total` — total on `NoVar` terms (terms without S.V variables;
  constPs, nodes, and extension symbols are all allowed and treated
  as 0-ary or function-application symbols with a fixed precedence).
* `kbo_mono_ctx` — monotone under one-hole contexts.
* `kbo_size_le` — `≺ₖ` doesn't grow size.
-/

namespace EnumRules

variable {S : Signature} {Ext : Type}

opaque kbo : Term S Ext → Term S Ext → Prop

@[inherit_doc kbo]
scoped infix:50 " ≺ₖ " => kbo

axiom kbo_wf : WellFounded (kbo : Term S Ext → Term S Ext → Prop)

axiom kbo_trans {a b c : Term S Ext} : a ≺ₖ b → b ≺ₖ c → a ≺ₖ c

axiom kbo_total {s t : Term S Ext}
    (hs : Term.NoVar s) (ht : Term.NoVar t) :
    s = t ∨ s ≺ₖ t ∨ t ≺ₖ s

axiom kbo_mono_ctx
    {f : S.σ} {as bs : Fin (S.arity f) → Term S Ext} {i : Fin (S.arity f)}
    (hrest : ∀ j, j ≠ i → as j = bs j)
    (hlt : bs i ≺ₖ as i) :
    (Term.node f bs) ≺ₖ (Term.node f as)

axiom kbo_size_le {s t : Term S Ext} (h : s ≺ₖ t) : Term.size s ≤ Term.size t

end EnumRules
