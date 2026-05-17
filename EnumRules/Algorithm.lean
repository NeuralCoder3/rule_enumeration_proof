import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import EnumRules.Rewrite

open scoped Classical

/-
# The enumeration algorithm

## Role
Defines the algorithm's data structures (all over rule-construction
terms `Term S Empty`):
* `termsFromIrreducible` — enumerate terms of given size whose
  subterms come from a given set. Includes variables, ConstPlaceholders,
  and nodes.
* `renamingOrbit` — close a Finset under variable and ConstPlaceholder
  renamings, ensuring canonical representatives are present.
* `Canonical` — opaque per-orbit representative-picking predicate.
* `R_can S n` — synthesised rule set after processing all sizes ≤ n.
* `I_can S n` — stored canonical irreducibles after processing all
  sizes ≤ n.

Runtime substitution (substituting ConstPlaceholders with extension
symbols, variables with arbitrary runtime terms) is in `Subst.lean`.

## Axioms
None in this file. `mem_termsFromIrreducible` is a theorem.

## Opaque (1)
* `Canonical : Term S Empty → Prop` — no behavioural axioms here.
  Used in `CanonicalLayer.lean` with `canonical_of_ground` to handle
  the runtime-ground case (terms whose ConstPlaceholders correspond
  to extension symbols).
-/

namespace EnumRules

variable {S : Signature}

/-! ## Enumeration of terms by size + distinct-VC bound -/

/-- Enumeration of `Term S Empty` of size `n` whose direct subterms
(when the term is a node) all belong to `subterms`, AND whose total
number of distinct variables + ConstPlaceholders is at most `k`.
Variables and ConstPlaceholders are included unconditionally (at size
1) but the `≤ k` filter still applies. -/
noncomputable def termsFromIrreducible (S : Signature)
    (subterms : Finset (Term S Empty)) (k n : Nat) : Finset (Term S Empty) :=
  ((Finset.univ : Finset S.V).image Term.var ∪
   (Finset.univ : Finset S.C).image Term.constP ∪
    (Finset.univ : Finset S.σ).biUnion (fun f =>
      (Fintype.piFinset (fun _ : Fin (S.arity f) => subterms)).image (Term.node f))
  ).filter (fun t => Term.size t = n ∧ Term.numDistinctVCs t ≤ k)

/-- Specification of `termsFromIrreducible`: a term `t` is in
`termsFromIrreducible S subterms k n` iff its size is `n`, its
distinct-VC count is at most `k`, and every node-decomposition has
`args i ∈ subterms`. -/
@[simp] theorem mem_termsFromIrreducible
    {subterms : Finset (Term S Empty)} {k n : Nat} {t : Term S Empty} :
    t ∈ termsFromIrreducible S subterms k n ↔
      Term.size t = n ∧ Term.numDistinctVCs t ≤ k ∧
      ∀ (f : S.σ) (args : Fin (S.arity f) → Term S Empty),
        Term.node f args = t → ∀ i, args i ∈ subterms := by
  simp only [termsFromIrreducible, Finset.mem_filter, Finset.mem_union,
             Finset.mem_image, Finset.mem_biUnion, Fintype.mem_piFinset,
             Finset.mem_univ, true_and]
  cases t <;> aesop

/-! ## Renamings: maps on S.V and S.C

A renaming is a pair `(σV : S.V → S.V, σC : S.C → S.C)` that acts on
a rule-construction term by renaming each `var` and `constP` leaf.
We close the enumerated `termsFromIrreducible` under all such renamings
so the `Canonical` filter sees the canonical representative of each
renaming-orbit. (Bijectivity isn't enforced — extra non-bijective
renamings over-generate harmlessly; `Canonical` filters them out.) -/

/-- Apply a renaming pair `(σV, σC)` to a rule-construction term. -/
def renameTerm (σV : S.V → S.V) (σC : S.C → S.C) : Term S Empty → Term S Empty
  | .var v       => .var (σV v)
  | .constP c    => .constP (σC c)
  | .node f args => .node f (fun i => renameTerm σV σC (args i))
  | .ext e       => Empty.elim e
termination_by structural t => t

/-- Close a Finset of terms under all renamings (variable and
ConstPlaceholder maps). -/
noncomputable def renamingOrbit
    (s : Finset (Term S Empty)) : Finset (Term S Empty) :=
  s.biUnion fun t =>
    ((Finset.univ : Finset (S.V → S.V)) ×ˢ (Finset.univ : Finset (S.C → S.C))).image
      (fun p => renameTerm p.1 p.2 t)

/-! ## Canonical filter and the synthesised rule / irreducible sets -/

/-- Canonicality predicate over rule-construction terms (`Term S Empty`):
a per-renaming-orbit representative-picking filter. -/
opaque Canonical : Term S Empty → Prop

mutual
  /-- The synthesised rule set after processing all sizes `≤ n`, with
  the distinct-VC bound `k`. -/
  noncomputable def R_can (S : Signature) (k : Nat) : Nat → RuleSet S
    | 0     => ∅
    | n + 1 => R_can S k n ∪ (
        (renamingOrbit (termsFromIrreducible S (I_can S k n) k (n + 1))).filter (fun l =>
          Canonical l ∧ ¬ simplifiesWith (R_can S k n) l ∧ smtMin l ≠ l)
          |>.image (fun l => (l, smtMin l)))

  /-- The stored canonical irreducible set after processing all sizes
  `≤ n`, with the distinct-VC bound `k`. -/
  noncomputable def I_can (S : Signature) (k : Nat) : Nat → Finset (Term S Empty)
    | 0     => ∅
    | n + 1 => I_can S k n ∪ (
        (renamingOrbit (termsFromIrreducible S (I_can S k n) k (n + 1))).filter (fun l =>
          Canonical l ∧ ¬ simplifiesWith (R_can S k n) l ∧ smtMin l = l))
end

end EnumRules
