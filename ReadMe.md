Alg 0:

For n:
enum all terms of size n
for each term l:
synthesize kbo minimal term r, add rule l -> r


Alg 1:
Simplify with R n, if smaller size, discard
otherwise: smt


Alg 2:
Enumerate terms only from the irreducable set of previous iterations.


Alg 3:
Only enumerate canonical terms.


apply rules mod renaming on enumerated terms?




We have a signature with function symbols, and var-constants as placeholder for variables.
Iteration of algorithm:
- Enumerate canonical terms from irreducibles of previous iteration (arguments are previous irreducibles such that the size is correct)
  For each term we enumerate a subset of renaming such that we keep one term that is the same under renaming.
- We then simplify the terms with the current rule set, and if the term is smaller than the original term, we skip it.
- Otherwise, we get a set of terms on which we call our SMT oracle.
- The SMT oracle returns a term that is minimal among our order and equivalent to the original term. If the term is smaller according to the order, we add a rule.
- For the remaining irreducibile terms, we check equivalences with the current and smaller irreducible terms, and group them into equivalence classes.

For the correctness lemma, we apply the rules as long as possible. Then we get a term that is irreducible, and we check the equivalence class of that term and all their instantiations and select the minimal one (our order is total on ground terms).


Our order is a reduction order that is stable under substitution.












# Algorithm description

## Setting

* `S` is a signature with function symbols and arities. Variables `V` are
  a separate type from `S` — they are NOT modelled as 0-ary symbols.
* Terms are built from variables and from function symbols applied to
  the right number of arguments.
* A *substitution* `σ : V → Term` is a total mapping of variables to
  terms. `t·σ` denotes simultaneous instantiation.
* `≈ₜ` is the equivalence relation decided by SMT (a congruence,
  closed under substitution: `s ≈ₜ t → s·σ ≈ₜ t·σ`).
* `≺ₖ` is a *reduction order* (well-founded, transitive, total on ground
  terms, monotone under one-hole contexts) that **respects every
  substitution**: `s ≺ₖ t → s·σ ≺ₖ t·σ`. KBO with all weights 1 is one
  such order.
* SMT oracle `smtMin t`: returns a `≺ₖ`-minimum element of the
  `≈ₜ`-class of `t`.

## Key invariant for rules

A rule `(l, r)` is added to the rule set only when `r ≺ₖ l` *as terms*
(not just as ground instances). Because `≺ₖ` respects substitutions,
this immediately gives `r·σ ≺ₖ l·σ` for every `σ`. If SMT cannot
synthesize an `r` with this property, `l` is declared **irreducible**
and the rule is skipped.

## Algorithm 4 (substitution + equivalence groups)

Maintain two structures, grown by ascending size:
* a rule set `R`,
* a set of irreducibles partitioned into **equivalence groups**
  `G = { G_1, G_2, … }`, each group a `≈ₜ`-class of pairwise
  non-rewritable terms.

```
for n = 1, 2, …, N:
  enumerate canonical terms l of size n whose strict subterms come from
  ⋃ G ∪ V (irreducibles + variables);
  for each l:
    if l simplifies via R (some R-rewrite makes it strictly smaller):
      skip
    else:
      r ← smtMin l                                  -- SMT call
      if r ≺ₖ l (always-ordered ⇒ r·σ ≺ₖ l·σ for all σ):
        add (l, r) to R
      else:
        -- l is irreducible; place it in its ≈ₜ-group
        if ∃ G_i with some m ∈ G_i and l ≈ₜ m (SMT check):
          add l to G_i
        else:
          create a new group {l}
```

## Normalization

```
normalize(t):
  apply R-rewrites with arbitrary substitutions until no rule matches;
  let t' be the result;
  find the group G_i and instance m ∈ G_i and substitution σ
    with m·σ ≈ₜ t' (SMT check);
  return the smallest such m·σ (under ≺ₖ).
```

The first phase rewrites *arbitrary* terms (not only canonical ones):
matching is `l·σ` against a subterm. Termination follows from
`≺ₖ`-decrease (each step decreases the term in the substitution-stable
reduction order).

## Completeness statement

For any two terms `s` and `t` with `s ≈ₜ t` (and small enough to be
covered by the bound `N`), `normalize(s) = normalize(t)`.

Sketch:
1. Both `normalize(s)` and `normalize(t)` are `≈ₜ`-equivalent to their
   inputs (rules preserve `≈ₜ`; the final group lookup is by `≈ₜ`).
2. Hence `normalize(s) ≈ₜ normalize(t)`.
3. Both lie in the same equivalence group `G_i` (groups are full
   `≈ₜ`-classes among irreducibles, by construction).
4. Both phases pick the **smallest** element `m·σ` of that group with
   `m·σ ≈ₜ` the input. Smallness under `≺ₖ` is preserved by
   substitution, so the smallest is unique up to `=`.

The current Lean development establishes this for the *renaming*
specialization of the above (variables identified with 0-ary symbols,
substitutions restricted to bijective renamings of variable symbols,
groups singletons of canonical representatives). Lifting from the
renaming proof to the full substitution proof reuses every lemma of
`Rewrite.lean` unchanged: the only new ingredient is the
substitution-monotonicity axioms `kbo_subst` and `equiv_subst`.
