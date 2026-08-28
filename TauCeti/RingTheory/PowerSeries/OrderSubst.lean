/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The order of a power-series substitution

For univariate power series `f g : R⟦X⟧` with `constantCoeff f = 0`, over a commutative ring with
no zero divisors, the order of `PowerSeries.subst f g` is *determined* by the orders of `f` and
`g`:

`order (subst f g) = order g * order f`.

Mathlib provides only the inequality. `PowerSeries.le_order_subst` and its five companions
(`le_weightedOrder_subst`, `le_order_subst_left`, `le_order_subst_right` and the two primed forms)
all bound the order of a substitution from below; none determines it. The bound is what a caller
can prove without hypotheses on the coefficient ring, and the equality is what a caller usually
needs — additivity of the height of a composite formal-group homomorphism, for instance, is the
equality read at `order`.

`NoZeroDivisors R` is exactly what upgrades the bound to an equality: it is what makes
`order_mul` additive, and without it the leading terms of `f ^ order g` and of the substituted
tail can cancel. No hypothesis on `g` is needed — the proof splits on `g = 0` and on whether `g`
has vanishing constant coefficient, and the subsingleton case is handled uniformly.

## Main results

* `PowerSeries.order_subst` : the order of a substitution, as an equality.

## Provenance

Adapted from Chris Birkbeck's `AINTLIB` (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch
`dev/hasse-weil` at commit `513e83879e2f`, file
`projects/HasseWeil/HasseWeil/FormalGroup/OrderSubst.lean` — declarations `order_subst` and its
private constant-coefficient helper. The source module imports only
`Mathlib.RingTheory.PowerSeries.Substitution` and `Mathlib.RingTheory.PowerSeries.Order`, and is
ported here unchanged in mathematical content.

The helper is kept private and is not a re-derivation of Mathlib API: Mathlib's
`PowerSeries.constantCoeff_subst` states the constant coefficient as a `finsum`, and
`PowerSeries.constantCoeff_subst_eq_zero` covers only the case where it vanishes. Neither gives
`constantCoeff (subst f g) = constantCoeff g`, which is that `finsum` evaluated using
`constantCoeff f = 0`, and which both branches of the main proof consume.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The constant coefficient of `PowerSeries.subst f g` is that of `g`, when `constantCoeff f = 0`.
This is Mathlib's `constantCoeff_subst` finsum with every term but the `d = 0` one killed by
`constantCoeff f = 0`. -/
private lemma constantCoeff_subst_of_constantCoeff_eq_zero {f : PowerSeries R}
    (hf : constantCoeff f = 0) (g : PowerSeries R) :
    constantCoeff (subst f g) = constantCoeff g := by
  have hsub : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  rw [← coeff_zero_eq_constantCoeff, coeff_subst' hsub g 0, finsum_eq_single _ 0]
  · simp
  · intro d hd
    have hc : coeff 0 (f ^ d) = (0 : R) := by
      rw [coeff_zero_eq_constantCoeff, map_pow, hf, zero_pow hd]
    rw [hc, smul_zero]

/-- **The order of a substitution, as an equality**: for `f g : R⟦X⟧` with `constantCoeff f = 0`
over a commutative ring with no zero divisors,
`order (subst f g) = order g * order f`.

Mathlib's `le_order_subst` gives only `order g * order f ≤ order (subst f g)`. The hypothesis
`constantCoeff f = 0` is what makes the substitution well defined (`HasSubst f`); `NoZeroDivisors`
is what prevents the leading terms from cancelling and so upgrades the bound to an equality. -/
theorem order_subst [NoZeroDivisors R] {f g : PowerSeries R} (hf : constantCoeff f = 0) :
    order (subst f g : PowerSeries R) = g.order * f.order := by
  have hsub : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  by_cases hRtriv : Subsingleton R
  · -- Over the zero ring every series is `0`, so both sides are `⊤`.
    have h0 : ∀ h : PowerSeries R, h = 0 := fun h ↦ by ext n; exact Subsingleton.elim _ _
    have hlhs : order (subst f g : PowerSeries R) = ⊤ := by
      rw [h0 (subst f g : PowerSeries R)]; exact order_zero
    have hg : order g = ⊤ := by rw [h0 g]; exact order_zero
    have hfo : order f = ⊤ := by rw [h0 f]; exact order_zero
    rw [hlhs, hg, hfo]
    simp
  have : Nontrivial R := not_subsingleton_iff_nontrivial.mp hRtriv
  by_cases hg0 : g = 0
  · subst hg0
    have hz : subst f (0 : PowerSeries R) = 0 := by
      rw [← coe_substAlgHom hsub]; exact map_zero _
    have hf_ord_ne_zero : order f ≠ 0 := by
      rw [order_ne_zero_iff_constCoeff_eq_zero]; exact hf
    rw [show (subst f (0 : PowerSeries R) : PowerSeries R) = 0 from hz, order_zero]
    exact (ENat.top_mul hf_ord_ne_zero).symm
  by_cases hcg : constantCoeff g = 0
  · -- `g ≠ 0` with vanishing constant coefficient: split off `X ^ order g`.
    set n : ℕ := g.order.toNat with hn_def
    have hn_cast : (n : ℕ∞) = g.order := coe_toNat_order hg0
    have h_decomp : (subst f g : PowerSeries R) =
        f ^ n * (subst f (divXPowOrder g) : PowerSeries R) := by
      conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f := g)]
      rw [subst_mul hsub, subst_pow hsub, subst_X hsub]
    have h_sub_g'_cc : constantCoeff (subst f (divXPowOrder g) : PowerSeries R) ≠ 0 := by
      rw [constantCoeff_subst_of_constantCoeff_eq_zero hf, constantCoeff_divXPowOrder]
      exact coeff_order hg0
    have h_sub_g'_order : order (subst f (divXPowOrder g) : PowerSeries R) = 0 := by
      refine le_antisymm ?_ zero_le
      exact_mod_cast order_le (φ := (subst f (divXPowOrder g) : PowerSeries R)) 0
        (by rwa [coeff_zero_eq_constantCoeff])
    rw [h_decomp, order_mul, order_pow, h_sub_g'_order, add_zero, nsmul_eq_mul, ← hn_cast]
  · -- `constantCoeff g ≠ 0`: both orders are `0`.
    have h_sub_cc : constantCoeff (subst f g : PowerSeries R) ≠ 0 := by
      rw [constantCoeff_subst_of_constantCoeff_eq_zero hf]; exact hcg
    have h_sub_order : order (subst f g : PowerSeries R) = 0 := by
      refine le_antisymm ?_ zero_le
      exact_mod_cast order_le (φ := (subst f g : PowerSeries R)) 0
        (by rwa [coeff_zero_eq_constantCoeff])
    have h_g_order : order g = 0 := by
      refine le_antisymm ?_ zero_le
      exact_mod_cast order_le (φ := g) 0 (by rwa [coeff_zero_eq_constantCoeff])
    rw [h_sub_order, h_g_order, zero_mul]

end PowerSeries
