# EnumRules

A Lean development of correctness for an enumeration-based normalization
algorithm modulo a semantic equivalence `≈ₜ` decided by an SMT oracle,
with explicit variable handling.

## Setting

### Signature with explicit variables

```
Signature = (σ, V, arity)
  σ      : Type of function symbols
  V      : Type of variables (separate from σ)
  arity  : σ → ℕ (only function symbols have arities; variables are
                  treated uniformly as 0-ary "placeholders")
```

Both `σ` and `V` have decidable equality.

### Terms

```
Term S ::=
  | var (v : S.V)                                  -- a variable
  | node (f : S.σ) (args : Fin (arity f) → Term S) -- a function application
```

A *ground term* contains no `var` constructors.

### Substitutions (concrete, not opaque)

```
Subst S := S.V → Term S

apply (σ : Subst) : Term S → Term S
  | var v        ↦ σ v
  | node f args  ↦ node f (apply σ ∘ args)

Subst.id : Subst         -- σ.id v = var v
Subst.comp : Subst → Subst → Subst
  (Subst.comp σ τ) v ↦ apply σ (τ v)
```

Substitution is defined directly. The "axioms" `apply_id`, `apply_comp`,
`apply_node` are now **theorems** by structural induction.

### Equivalence and order

* `≈ₜ` (semantic equivalence): SMT-decided. Equivalence relation,
  congruence, closed under substitution: `s ≈ₜ t → s·σ ≈ₜ t·σ`.
* `≺ₖ` (reduction order, e.g. KBO): well-founded, transitive,
  monotone under one-hole contexts, **substitution-monotone**:
  `s ≺ₖ t → s·σ ≺ₖ t·σ`. KBO is **partial** in general — distinct
  variables are KBO-incomparable, so e.g. `var a` and `var b` are
  incomparable; `var a + var b` and `var b + var a` are incomparable.
  KBO is **total on ground terms** (no variables).

### SMT oracle

`smtMin t` returns a `≺ₖ`-minimal element of `t`'s `≈ₜ`-class.
* `smtMin t ≈ₜ t`.
* `smtMin_min`: no `≈ₜ`-equivalent of `t` is `≺ₖ`-strictly-smaller than
  `smtMin t`.
* When `t` is its own minimum (no comparable smaller class member),
  `smtMin t = t` (the oracle returns the input).

### Why variables matter for rules

A rule `(l, r)` is added to `R` only when `r ≺ₖ l` *as terms with
variables*. By substitution-monotonicity, this gives `r·σ ≺ₖ l·σ` for
**every** `σ` — so the rule is sound under any instantiation.

When `≺ₖ` is **incomparable** between `l` and a candidate `r` (variables
prevent ordering), no rule can be added. Example: for commutative `+`,
`l = var a + var b` and `r = var b + var a` are KBO-incomparable
(distinct variables), so even though `l ≈ₜ r`, no rule with this LHS/RHS
gets added. `l` is declared **irreducible** and placed in its `≈ₜ`-group.

This is the key reason variables must be modelled explicitly: the
incomparability of variable-terms is what protects rule soundness from
α-renaming pitfalls.

## Algorithm

Maintain by ascending size `n = 1, 2, …, N`:
* a **rule set** `R`,
* irreducibles partitioned into **`≈ₜ`-groups** `G = { G_1, G_2, … }`.

```
for n = 1, 2, …, N:
  enumerate canonical terms l of size n whose strict subterms come from
    ⋃ G ∪ V (canonical irreducibles + variables);

  for each enumerated l:
    if l simplifies via R (rewrite reaches a strictly smaller term):
      skip                     -- already covered

    else:
      r ← smtMin l              -- SMT call at enumeration time
      if r ≺ₖ l (KBO-comparable, strictly smaller):
        add (l, r) to R         -- substitution-monotone rule
      else:                     -- r = l (incomparable case)
        if ∃ G_i and m ∈ G_i with l ≈ₜ m  (SMT check):
          add l to G_i
        else:
          create a new group {l} in G
```

### Normalization (runtime)

```
normalize(t):
  -- Phase 1: rewrite
  apply R-rewrites (rule l→r fires on subterm u when u = l·σ for some σ)
  until no rule matches; let t' be the result.

  -- Phase 2: lookup
  find the group G_i and m ∈ G_i and substitution σ
    with m·σ ≈ₜ t'              (lookup against stored ≈ₜ-data)
  return the smallest such m·σ under ≺ₖ.
```

Phase 1 terminates by `≺ₖ`-decrease (each step reduces under
substitution-monotone KBO).

Phase 2 picks the `≺ₖ`-minimum among `{m·σ : m ∈ G_i, m·σ ≈ₜ t'}`.
For **ground** `t'` this set's minimum is unique (KBO total on ground).
For non-ground `t'`, multiple minima may be incomparable; the algorithm
returns one — concretely, the smallest after instantiating variables.

## Strong completeness theorem

```
∀ s t, s ≈ₜ t →
  ∃ output,
    normalize(s) ≡ output ∧ normalize(t) ≡ output    (modulo renaming)
```

Where `≡ output` means `normalize` reaches `output` exactly when
ground, or up to a renaming on the variables when non-ground.

### Why this is achievable

* Phase 1 (rewriting) preserves `≈ₜ`. So `s →* s'` and `t →* t'` with
  `s' ≈ₜ s ≈ₜ t ≈ₜ t'`, hence `s' ≈ₜ t'`.
* Phase 2 picks the `≺ₖ`-minimum in the `≈ₜ`-class. By
  `smtMin_min`, this minimum is **unique up to KBO-incomparability**.
  KBO-incomparable terms are exactly those that differ only by variable
  renaming (under standard KBO without variable precedence). So the
  minimum is unique up to renaming.

### Why variables are essential

If we modeled variables as 0-ary constants (pre-refactor): `a + b` and
`b + a` for two distinct constants `a, b` would be **KBO-comparable**
(`a < b` in symbol precedence), so `smtMin` would pick one strictly,
forcing a rule `(b + a, a + b)`. This is wrong — these are constants,
not variables, and they have distinct semantic interpretations.

With **variables**: `var a + var b` and `var b + var a` are
KBO-incomparable (no precedence between distinct variables). No rule
is created. Both are stored as irreducibles, possibly in the same
`≈ₜ`-group (if `+` is commutative, by SMT check).

This is exactly the right behaviour: rules over variable-terms must be
substitution-stable, and the only way to guarantee that for partial KBO
is to require strict comparability.

## Assumptions / axioms

| Axiom | Sound for |
|---|---|
| `equiv_refl/symm/trans/congr/subst` | Any signature |
| `kbo_wf, kbo_trans, kbo_mono_ctx` | Any signature |
| `kbo_total_ground` (only on ground terms) | Any signature with KBO |
| `kbo_subst` (substitution-monotone) | Any signature with substitution-monotone reduction order |
| `kbo_size_le` (with weight 1) | KBO with positive weights |
| `smtMin_equiv, smtMin_min` | Any signature with SMT oracle |
| `smtMin_resp_ground` (for ground terms) | Any signature; `s ≈ₜ t (ground) → smtMin s = smtMin t` |
| `mem_termsFromIrreducible` | Specifies enumeration |
| `Canonical : Term S → Prop` (opaque) | Any predicate |

Substitutions are now **concrete** — `apply_id`, `apply_comp`,
`apply_node` are theorems.

`kbo_total_ground` is the appropriate weakening of the previous
`kbo_total`: KBO is total on **ground** terms but partial on terms with
variables. This is the standard KBO behaviour.

## Invariants

* **Rules are KBO-decreasing on the term level** (with variables):
  every `(l, r) ∈ R` satisfies `r ≺ₖ l`. By `kbo_subst`,
  `r·σ ≺ₖ l·σ` for every `σ` — substitution-stable rule decrease.
* **Rules preserve `≈ₜ`**: every rule `(l, r)` has `l ≈ₜ r`.
* **`I_can` consists of canonical irreducibles**: elements `c ∈ I_can`
  satisfy `Canonical c` and `smtMin c = c`.
* **Groups are `≈ₜ`-classes**: members of a group are pairwise `≈ₜ`.

## Proof outline

### Universal lemmas

1. **Termination**: `kbo_wf` + `rule_kbo` + classical induction
   gives `reaches_normal_form`.
2. **Soundness**: `rule_equiv` + congruence gives `Step.equiv_of`.
3. **`≺ₖ`-decrease**: `rule_kbo` + monotonicity gives `Step.kbo_of`.
4. **Substitution-stability of rewriting**: `Step.subst` (via
   `kbo_subst`, `equiv_subst`, definitional `apply` properties).

### Strong completeness

For ground inputs `s, t` with `s ≈ₜ t`:

5. Phase 1: `s →* s'` and `t →* t'` via `R`; `s' ≈ₜ s ≈ₜ t ≈ₜ t'`.
6. By `smtMin_resp_ground` (KBO total on ground): `smtMin s' = smtMin t'`.
7. Phase 2 lookup yields this `smtMin`. Algorithm output is the
   *unique* minimum of the `≈ₜ`-class.

For inputs with variables:

8. Same Phase 1.
9. Phase 2 picks a `≺ₖ`-minimum; for KBO-incomparable minima, the
   choice is up to renaming. The algorithm outputs a representative;
   different runs may pick different α-equivalent representatives.

### What's universal vs. signature-dependent

**Universal**: Phase 1 termination + soundness; Phase 2 correctness on
ground inputs (`smtMin` agreement).

**Signature-dependent** (non-AC): Phase 2's α-equivalent normal forms
for non-ground inputs.

For AC signatures, Phase 2's "smallest" is still a minimum, but it's
not α-equivalent across `≈ₜ`-equivalent inputs (different shapes).
For AC, the algorithm still produces a correct ground result, but
non-ground answers up-to-renaming don't exist.

## File layout

```
Signature.lean      -- σ, V, arities, decidable equalities
Term.lean           -- var/node, size, decidable equality
Subst.lean          -- concrete Subst, apply, Subst.comp;
                       all substitution lemmas as theorems
Equiv.lean          -- ≈ₜ axioms (refl/symm/trans/congr/subst)
Kbo.lean            -- ≺ₖ axioms (wf/trans/mono_ctx/size_le/subst);
                       kbo_total_ground for ground terms only
Oracle.lean         -- smtMin oracle (equiv, min);
                       smtMin_resp_ground derived; smtMin_strict, smtMin_idem
Rewrite.lean        -- Step / StepStar with substitution-based root;
                       Step.subst, Step.equiv_of, Step.kbo_of (as theorems)
Algorithm.lean      -- R, I, mem_R, rule_kbo, rule_equiv,
                       subterm_of_minimal_is_minimal
CanonicalLayer.lean -- R_can, I_can with Canonical filter;
                       complete_can (universal); complete_modulo_renaming
                       (non-AC, via Step.subst).
```
