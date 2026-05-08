# EnumRules

A Lean development of correctness for an enumeration-based normalisation
algorithm modulo a semantic equivalence `≈ₜ` decided by an SMT oracle.

## Setting

### Signature

```
Signature = (σ, V, arity)
  σ      : Type of function symbols
  V      : Type of S.V variables (algorithm-internal placeholders)
  arity  : σ → ℕ
```

Both `σ` and `V` have decidable equality.

**Two roles for "variables".** User-level variables in input formulas
are modelled as 0-ary symbols of `S.σ` (constants). The separate type
`S.V`, with its `Term.var` constructor, exists only for the algorithm's
*internal rule schemas*: when the algorithm synthesises a rule like
`f(v₀, v₀) → v₀`, the `v₀` is a `Term.var` and gets instantiated at
runtime against actual subterms via substitution.

### Terms

```
Term S ::=
  | var (v : S.V)                                  -- schema placeholder
  | node (f : S.σ) (args : Fin (arity f) → Term S) -- function application
```

A *ground* term (`Term.IsGround`) contains no `var` constructors.
**Runtime inputs are ground**: they live in the `Term.node`-only
sublanguage of `Term S`.

### Substitutions

```
Subst S := S.V → Term S

apply (σ : Subst) : Term S → Term S
  | var v        ↦ σ v
  | node f args  ↦ node f (apply σ ∘ args)

Subst.id (v) ↦ var v
Subst.comp ρ σ (v) ↦ apply ρ (σ v)
```

`apply_id`, `apply_comp`, `apply_node`, and `apply_ground` are
**theorems** by structural induction. The only behavioural axioms about
substitution are how it interacts with `≈ₜ` and `≺ₖ` (`equiv_subst`,
`kbo_subst`).

### Equivalence and order

* `≈ₜ` (semantic equivalence): SMT-decided. Equivalence relation,
  congruence, closed under substitution.
* `≺ₖ` (reduction order, e.g. KBO): well-founded, transitive,
  monotone under one-hole contexts, **substitution-monotone**
  (`s ≺ₖ t → apply σ s ≺ₖ apply σ t`), and **total on ground terms**
  (`kbo_total` requires `IsGround`).

Classical KBO is partial on terms with variables — distinct
`Term.var` are KBO-incomparable — so totality is sound only on
ground terms. The framework restricts `kbo_total` to ground inputs
explicitly. Where the algorithm needs a property of `smtMin` that
would have followed from uniform totality (specifically
`smtMin t = t ∨ smtMin t ≺ₖ t`), this is axiomatised separately as
`smtMin_le`, sound for any well-behaved oracle (return either the
input or a strictly KBO-smaller equivalent).

### SMT oracle

`smtMin t` returns a `≺ₖ`-minimum element of `t`'s `≈ₜ`-class.
* `smtMin t ≈ₜ t` (axiom `smtMin_equiv`).
* `smtMin_min`: no `≈ₜ`-equivalent of `t` is `≺ₖ`-strictly-smaller
  than `smtMin t`.
* `smtMin_le` (axiom): `smtMin t = t ∨ smtMin t ≺ₖ t`. Sound for any
  oracle that returns either the input or a strictly smaller
  KBO-comparable equivalent.
* `smtMin_resp` (theorem, from `smtMin_min` + ground `kbo_total`):
  for ground `s ≈ₜ t`, `smtMin s = smtMin t`. Used by
  `I_can_unique_per_class` for the common-normal-form theorem.

## Algorithm

Mutually recursive on size `n = 1, 2, …`:

* **rule set** `R_can S n`,
* **irreducible set** `I_can S n`.

```
for n = 1, 2, …:
  enumerate canonical terms l of size n whose strict subterms
    come from I_can S (n-1);

  for each enumerated l with Canonical l:
    if l simplifies via R_can S (n-1):
      skip                     -- already covered

    else if smtMin l ≠ l:
      add (l, smtMin l) to R_can S n   -- rule, l reducible

    else:
      add l to I_can S n               -- irreducible representative
```

`smtMin` is queried at *enumeration time*. Rules synthesised this way
are KBO-decreasing on the schema level (`r ≺ₖ l`); by `kbo_subst`,
every instance `apply σ r ≺ₖ apply σ l` — substitution-stable rule
decrease, hence one-step rewriting is `≺ₖ`-decreasing under any
substitution.

### Normalisation (runtime)

Inputs are S.V-ground. Two operational steps (`ExtStep`):

1. **Rule rewriting** (`Step (R_can S n)`) — fire a synthesised rule
   `(l, r) ∈ R_can` under any substitution σ matching `l` against a
   subterm. Phase 1; reaches an `R_can`-irreducible normal form.
2. **Class lookup** (`ExtStep.class_lookup`) — replace the irreducible
   normal form `t'` with its stored class representative `c ∈ I_can`
   (decided at enumeration time). For ground inputs this is *trivial*:
   `t' ∈ I_can` directly (see `complete_common_normal_form`).

No `smtMin` call happens at runtime — the SMT work is all paid at
enumeration time.

## Completeness theorem

### `complete_common_normal_form` (in `CanonicalLayer.lean`)

```
IsGround s ∧ IsGround t ∧ size s ≤ n ∧ size t ≤ n ∧ s ≈ₜ t →
  ∃ c, c ∈ I_can S n ∧ ExtStepStar n s c ∧ ExtStepStar n t c
```

For ground `≈ₜ`-equivalent inputs of bounded size, the algorithm
reaches the **same** stored representative `c ∈ I_can S n` from both —
no quotient or up-to-renaming.

Proof: rewriting preserves groundness (`Step.preserves_ground`), so
`s'` and `t'` (the irreducible normal forms) are both ground;
`ground_irreducible_in_I_can` puts them in `I_can S n`; and
`I_can_unique_per_class` (which uses `smtMin_resp` on ground inputs)
forces `s' = t'`.

## Axioms

```
Equiv.lean       (4)  equiv_refl, equiv_symm, equiv_trans, equiv_congr
Kbo.lean         (5)  kbo_wf, kbo_trans, kbo_total (ground only),
                      kbo_mono_ctx, kbo_size_le
Subst.lean       (2)  kbo_subst, equiv_subst
Oracle.lean      (3)  smtMin_equiv, smtMin_min, smtMin_le
Algorithm.lean   (0)  Canonical (opaque); termsFromIrreducible is a
                      concrete `noncomputable def` and
                      `mem_termsFromIrreducible` is a theorem
CanonicalLayer   (2)  canonical_of_ground, smtMin_apply_ground
```

`kbo_total` carries an `IsGround` hypothesis so it stays sound on
variable-bearing terms (where classical KBO is partial). `smtMin_le`
is now an axiom (was a theorem from uniform `kbo_total`); it holds
for any well-behaved oracle.

`canonical_of_ground` and `smtMin_apply_ground` exist purely to
support the ground-restricted completeness theorem and
`Step.preserves_ground`.

### What's a theorem (was previously an axiom)

* `apply_id`, `apply_node` — structural facts about `apply`.
* `mem_termsFromIrreducible` — derived from the concrete definition
  of `termsFromIrreducible` (uses `Fintype` on `S.σ` / `S.V`).
* `smtMin_resp` — uniqueness of class minimum on **ground** inputs
  (from `smtMin_min` + ground `kbo_total`).
* `ground_irreducible_in_I_can` — by structural induction on `t`.
* `Step.preserves_ground` / `StepStar.preserves_ground` — induction on
  `Step` using `smtMin_apply_ground` for the root case.

## Invariants

* **Rules are KBO-decreasing on the schema level**: every
  `(l, r) ∈ R_can S n` satisfies `r ≺ₖ l`, hence `apply σ r ≺ₖ apply σ l`
  for any σ.
* **Rules preserve `≈ₜ`**: `(l, r) ∈ R_can S n` implies `l ≈ₜ r`.
* **`I_can` members are smtMin-fixed**: `c ∈ I_can S n` implies
  `smtMin c = c` (built into the I_can filter).
* **`I_can` has at most one rep per `≈ₜ`-class**
  (`I_can_unique_per_class`).
* **`Step (R_can S n)` preserves `IsGround`**.

## File layout

```
Signature.lean      σ, V, arities, decidable equalities
Term.lean           var/node, size, IsGround, decidable equality
Equiv.lean          ≈ₜ axioms (refl/symm/trans/congr)
Kbo.lean            ≺ₖ axioms (wf/trans/total/mono_ctx/size_le)
Subst.lean          concrete Subst, Subst.id, apply;
                    apply_id and apply_node are theorems;
                    kbo_subst, equiv_subst are axioms
Oracle.lean         smtMin (opaque) + smtMin_equiv/min/le (axioms);
                    smtMin_resp (ground), smtMin_strict, smtMin_size derived
Rewrite.lean        Step / StepStar with substitution-based root;
                    Step.equiv_of/kbo_of/lift/irreducible_arg as theorems;
                    not_simplifiesWith_of_irreducible
Algorithm.lean      termsFromIrreducible (concrete noncomputable def),
                    mem_termsFromIrreducible (theorem);
                    Canonical (opaque); R_can, I_can (mutual);
                    ExtStep, ExtStepStar
CanonicalLayer.lean canonical_of_ground, smtMin_apply_ground (axioms);
                    R_can/I_can structural lemmas (subset, mem_R_can_*);
                    rule_equiv_can, rule_kbo_can, terminates_can;
                    ground_irreducible_in_I_can (theorem);
                    complete_common_normal_form
```
