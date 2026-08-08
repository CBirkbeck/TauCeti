/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The order of a power series substitution

Mathlib's `PowerSeries.le_order_subst` bounds the order of a substitution from below,
`order g * order f ≤ order (subst f g)`. Over a ring without zero divisors that bound is an
equality:

`order (subst f g) = order g * order f`.

The hypothesis `constantCoeff f = 0` is what makes `subst f g` defined at all (`HasSubst f`), and
nothing is assumed of `g`.

## Main results

* `PowerSeries.order_subst`: the equality above.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/FormalGroup/OrderSubst.lean`, declarations `constantCoeff_subst_univariate` and
`order_subst`, where it gives additivity of the height of a composition of formal-group
homomorphisms (Silverman IV.7).

The proof here is shorter than the source's: three of its case branches each re-derived
`order φ = 0` from `constantCoeff φ ≠ 0` by `le_antisymm`, which is Mathlib's
`order_ne_zero_iff_constCoeff_eq_zero` contraposed, and the subsingleton branch is handled by
`Subsingleton.elim` rather than by rewriting each series to `0` separately.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- A power series with nonzero constant coefficient has order zero. -/
private theorem order_eq_zero_of_constantCoeff_ne_zero {φ : R⟦X⟧} (h : constantCoeff φ ≠ 0) :
    φ.order = 0 := by
  by_contra hne
  exact h (order_ne_zero_iff_constCoeff_eq_zero.mp hne)

/-- Substituting a series with zero constant coefficient does not change the constant
coefficient. -/
private theorem constantCoeff_subst_eq {f : R⟦X⟧} (hf : constantCoeff f = 0) (g : R⟦X⟧) :
    constantCoeff (subst f g) = constantCoeff g := by
  have hsub : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  rw [← coeff_zero_eq_constantCoeff, coeff_subst' hsub g 0, finsum_eq_single _ 0]
  · simp
  · intro d hd
    have hc : coeff 0 (f ^ d) = (0 : R) := by
      rw [coeff_zero_eq_constantCoeff, map_pow, hf, zero_pow hd]
    rw [hc, smul_zero]

/-- **The order of a substitution.** For `f g : R⟦X⟧` with `constantCoeff f = 0` over a ring
without zero divisors, `order (subst f g) = order g * order f`.

This strengthens Mathlib's `PowerSeries.le_order_subst`, which gives only `≤`. -/
theorem order_subst [NoZeroDivisors R] {f g : R⟦X⟧} (hf : constantCoeff f = 0) :
    PowerSeries.order ((PowerSeries.subst f g : R⟦X⟧)) =
      PowerSeries.order g * PowerSeries.order f := by
  have hsub : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  rcases subsingleton_or_nontrivial R with _ | _
  · have h0 : ∀ h : R⟦X⟧, h = 0 := fun h => by ext n; exact Subsingleton.elim _ _
    rw [h0 ((subst f g : R⟦X⟧)), h0 g, h0 f]
    simp
  rcases eq_or_ne g 0 with rfl | hg0
  · -- `subst f 0 = 0` has order `⊤`, and `⊤ * order f = ⊤` because `order f ≠ 0`.
    have hlhs : PowerSeries.order ((PowerSeries.subst f (0 : R⟦X⟧)) : R⟦X⟧) = ⊤ := by
      rw [show ((PowerSeries.subst f (0 : R⟦X⟧)) : R⟦X⟧) = 0 by
        rw [← coe_substAlgHom hsub]; exact map_zero _]
      exact PowerSeries.order_zero
    rw [hlhs, show PowerSeries.order (0 : R⟦X⟧) = ⊤ from PowerSeries.order_zero]
    exact (ENat.top_mul (order_ne_zero_iff_constCoeff_eq_zero.mpr hf)).symm
  rcases eq_or_ne (constantCoeff g) 0 with hcg | hcg
  · -- Peel `X ^ order g` off `g`; substitution turns it into `f ^ order g`, and the cofactor has
    -- nonzero constant coefficient, hence order zero.
    have hn : ((g.order.toNat : ℕ) : ℕ∞) = g.order := coe_toNat_order hg0
    have hdecomp : ((PowerSeries.subst f g) : R⟦X⟧)
        = f ^ g.order.toNat * ((PowerSeries.subst f (divXPowOrder g)) : R⟦X⟧) := by
      conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f := g)]
      rw [subst_mul hsub, subst_pow hsub, subst_X hsub]
    have hcofactor :
        PowerSeries.order ((PowerSeries.subst f (divXPowOrder g)) : R⟦X⟧) = 0 :=
      order_eq_zero_of_constantCoeff_ne_zero <| by
        rw [constantCoeff_subst_eq hf, constantCoeff_divXPowOrder]; exact coeff_order hg0
    rw [hdecomp, PowerSeries.order_mul, PowerSeries.order_pow, hcofactor, add_zero,
      nsmul_eq_mul, ← hn]
    simp
  · -- Both sides are zero, since neither constant coefficient vanishes.
    have hs : PowerSeries.order ((PowerSeries.subst f g) : R⟦X⟧) = 0 :=
      order_eq_zero_of_constantCoeff_ne_zero (by rwa [constantCoeff_subst_eq hf])
    rw [hs, order_eq_zero_of_constantCoeff_ne_zero hcg, zero_mul]

end PowerSeries
