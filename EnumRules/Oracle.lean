import EnumRules.Equiv
import EnumRules.Kbo

/-
# SMT oracle: KBO-minimal representative of the ≈ₜ-class

## Role
`smtMin t` is the SMT oracle's choice of `≺ₖ`-minimum element in
`t`'s `≈ₜ`-class. With `kbo_total` (ground-only), the minimum is
unique per class on ground inputs, giving `smtMin_resp` for ground
terms — Phase 2 lookup correctness.

## Axioms (3)
* `smtMin_equiv` — `smtMin t ≈ₜ t`.
* `smtMin_min` — no `≈ₜ`-equivalent term is `≺ₖ`-smaller than `smtMin t`.
* `smtMin_le` — `smtMin t = t ∨ smtMin t ≺ₖ t`. Holds for any
  well-behaved SMT oracle (returns either input or a strictly
  KBO-smaller equivalent). Previously derived from a uniform
  `kbo_total`; now an axiom because `kbo_total` is restricted to
  ground terms (KBO is partial on terms with variables).

## Derived theorems
* `smtMin_resp` — for ground `s ≈ₜ t`, `smtMin s = smtMin t`.
* `smtMin_strict` — if `smtMin t ≠ t`, then `smtMin t ≺ₖ t`.
* `smtMin_size` — `size (smtMin t) ≤ size t`.
-/

namespace EnumRules

variable {S : Signature}

instance : Nonempty (Term S → Term S) := ⟨fun x => x⟩

noncomputable opaque smtMin : Term S → Term S

axiom smtMin_equiv (t : Term S) : (smtMin t) ≈ₜ t

axiom smtMin_min {t : Term S} (u : Term S) (h : u ≈ₜ t) : ¬ (u ≺ₖ (smtMin t))

theorem smtMin_equiv_symm (t : Term S) : t ≈ₜ smtMin t :=
  equiv_symm (smtMin_equiv t)

/-- `smtMin t` is either `t` itself or strictly KBO-smaller. Sound for
any well-behaved oracle: when no comparable smaller equivalent exists
(e.g., for non-ground `t` with KBO-incomparable equivalents), the
oracle returns `t` itself. -/
axiom smtMin_le (t : Term S) : smtMin t = t ∨ (smtMin t) ≺ₖ t

/-- The oracle respects `≈ₜ`-equivalence on ground inputs. Two minima
of the same class are KBO-comparable (by ground `kbo_total`), but
neither is KBO-smaller than the other (by `smtMin_min`), so they are
equal. The hypotheses are placed on `smtMin s` / `smtMin t` so that
callers can supply them directly (e.g., from `I_can_smtMin_fixed`
combined with groundness of an `I_can` member). -/
theorem smtMin_resp {s t : Term S}
    (hs : Term.IsGround (smtMin s)) (ht : Term.IsGround (smtMin t))
    (h : s ≈ₜ t) : smtMin s = smtMin t := by
  have h1 : (smtMin s) ≈ₜ t := equiv_trans (smtMin_equiv s) h
  have h2 : ¬ ((smtMin s) ≺ₖ (smtMin t)) := smtMin_min (smtMin s) h1
  have h3 : (smtMin t) ≈ₜ s := equiv_trans (smtMin_equiv t) (equiv_symm h)
  have h4 : ¬ ((smtMin t) ≺ₖ (smtMin s)) := smtMin_min (smtMin t) h3
  rcases kbo_total hs ht with heq | hlt | hlt
  · exact heq
  · exact (h2 hlt).elim
  · exact (h4 hlt).elim

theorem smtMin_strict {t : Term S} (h : smtMin t ≠ t) : smtMin t ≺ₖ t := by
  rcases smtMin_le t with heq | hlt
  · exact (h heq).elim
  · exact hlt

theorem smtMin_size (t : Term S) : Term.size (smtMin t) ≤ Term.size t := by
  rcases smtMin_le t with heq | hlt
  · rw [heq]
  · exact kbo_size_le hlt

end EnumRules
