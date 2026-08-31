/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.RingTheory.Valuation.Integral
import TauCeti.AlgebraicGeometry.EllipticCurve.Integrality
import TauCeti.RingTheory.Valuation.RootMonic

/-!
# Integral points of a Weierstrass curve over a discretely valued field

Let `F` be a field carrying a `ℤᵐ⁰`-valued valuation `v`, let `O` be the valuation subring of `v`,
and let `W` be a Weierstrass curve over `F` that comes from a model `W₀` over `O`. This file
records the valuation estimates that such a model forces, and the dichotomy they produce for the
coordinates of an affine point.

The dichotomy is the sharp one: `v(x)` is never `exp 1`. Either the point is integral,
`v(x) ≤ 1` and `v(y) ≤ 1`, or it is a pole of order at least two in `x`, `exp 2 ≤ v(x)`. There is
nothing in between, because on the curve `v(y)² = v(x)³` at a pole, so `v(x)` has even exponent.

The two halves need different hypotheses, and are stated that way. The coefficient bounds — and
the estimates on the two sides of the Weierstrass equation — never look at the value group, so
they are stated for an arbitrary `Γ₀`. Only the dichotomy needs `Γ₀ = ℤᵐ⁰`, because the parity
argument that rules out `v(x) = exp 1` is about the exponent being an integer.

The motivating instance is the completion of the fraction field of a Dedekind domain at a
height-one prime: there `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers` is by
definition the valuation subring of `Valued.v`, so that case is literally an instance of what is
below. Nothing here uses completeness, or the Dedekind hypothesis behind it — only the valuation
and the fact that its value group is `ℤᵐ⁰`, which is what makes the parity argument work.

## Main results

* `WeierstrassCurve.Affine.valuation_a₁_le_one` and its `a₂`, `a₃`, `a₄`, `a₆` companions: the
  coefficients of a curve with an integral model are integral, over any value group.
* `WeierstrassCurve.Affine.valuation_x_le_one_and_valuation_y_le_one_of_valuation_x_lt_exp_two`:
  an affine point whose `x`-adic pole has order less than two has both coordinates integral.

## Implementation notes

The `y`-half of the dichotomy is not reproved by a valuation computation. Once `x` is known to be
integral, `TauCeti.WeierstrassCurve.isIntegral_y_of_equation_of_isIntegral_x` gives that `y` is
integral over `O` from the curve equation alone, over any algebra and with no valuation in sight;
`O` is a valuation subring, hence integrally closed in `F`, so integrality over it is membership.
That is how the main theorem discharges its `y`-half. Only the `x`-half — the parity argument that
rules out `v(x) = exp 1` — is genuinely about the valuation, and it is the only half that needs
the estimates below.

## Placement

Every declaration here lives in `WeierstrassCurve.Affine` and is about `Affine.Equation`, so the
file sits in `EllipticCurve/Affine/` with the rest of the affine-point API.

It is not under `FormalGroup/`, although the formal group is what makes these estimates wanted:
they are what identifies the kernel of reduction, on which the formal group converges, as the
locus `exp 2 ≤ v(x)`. But nothing here mentions a power series; the content is the integrality of
an affine point. No `FormalGroup/` file imports this module today — the milestones below are the
future consumers.

This supplies the valuation substrate for the formal-group milestones of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 1, item "The formal group — four milestones
with four different hypothesis sets, not one" (README:572): milestone (iii), convergence over a
complete valued field, and milestone (iv), the identification with the kernel of reduction for an
integral model.

## Provenance

Adapted from the Stoll `EllipticCurves` development
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Foundations.lean`: `valued_a₁`–`valued_a₄` (:125–:128),
`valued_a₆` (:129), `valued_lhs_eq_rhs` (:72), `valued_rhs_eq` (:132), `valued_lhs_eq` (:164),
`valued_lhs_le` (:185), `valued_ne_exp_one` (:202) and `integral_of_not_mem` (:264), which is
`valuation_x_le_one_and_valuation_y_le_one_of_valuation_x_lt_exp_two` here.

Five departures. The source's private `coe_a₁`–`coe_a₆` (:110–:122) are not ported: each is a
one-line restatement of the structure map, and the five public coefficient bounds prove it inline
instead. (Mathlib's `WeierstrassCurve.integralModel_a₁_eq`–`a₆_eq` state the same content for
Mathlib's *chosen* integral model, obtained by choice; they cannot discharge these, which are
about a *given* model `W₀`, so the bounds stay — but no separate coercion layer is introduced for
them.) The setting is more general: the source works over `v.adicCompletion K` and
`v.adicCompletionIntegers K`, whereas no step uses completeness or the Dedekind hypothesis, so the
results are stated over any `[Field F] [Valued F ℤᵐ⁰]` and its valuation subring — a weaker
hypothesis set that still covers the source's case definitionally. `valuation_a₆_le_one` is public
here although the source's `valued_a₆` (:129) is private: the five coefficient bounds are one API,
and a consumer holding a given integral model needs all five. The hypothesis is stated positively
as `Valued.v x < exp 2` rather than the source's `¬ exp 2 ≤ Valued.v x`. And the `y`-half is
proved by reuse rather than by the source's valuation computation: the source derives it from a
`valued_rhs_le` bound (:151), whereas here `isIntegral_y_of_equation_of_isIntegral_x` plus
integral closedness of `O` gives it directly, so that bound has no consumer and is not ported.
-/

public section

open WithZero

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F]

/-! ### The coefficient bounds, over an arbitrary value group

Nothing in this section looks at the value group: an integral model bounds the coefficients, and
the two sides of the Weierstrass equation are estimated, for any `Γ₀`. Only the dichotomy below
needs `Γ₀ = ℤᵐ⁰`. -/

section Coefficients

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued F Γ₀] {W : Affine F}
  {W₀ : WeierstrassCurve (Valued.v : Valuation F Γ₀).valuationSubring}
  (hW : W₀.map (algebraMap (Valued.v : Valuation F Γ₀).valuationSubring F) = W)

section

include hW

/-- The `a₁`-coefficient of a curve with an integral model is integral. -/
theorem valuation_a₁_le_one : Valued.v W.a₁ ≤ 1 := by
  rw [← hW, WeierstrassCurve.map_a₁]; exact W₀.a₁.2

/-- The `a₂`-coefficient of a curve with an integral model is integral. -/
theorem valuation_a₂_le_one : Valued.v W.a₂ ≤ 1 := by
  rw [← hW, WeierstrassCurve.map_a₂]; exact W₀.a₂.2

/-- The `a₃`-coefficient of a curve with an integral model is integral. -/
theorem valuation_a₃_le_one : Valued.v W.a₃ ≤ 1 := by
  rw [← hW, WeierstrassCurve.map_a₃]; exact W₀.a₃.2

/-- The `a₄`-coefficient of a curve with an integral model is integral. -/
theorem valuation_a₄_le_one : Valued.v W.a₄ ≤ 1 := by
  rw [← hW, WeierstrassCurve.map_a₄]; exact W₀.a₄.2

/-- The `a₆`-coefficient of a curve with an integral model is integral. -/
theorem valuation_a₆_le_one : Valued.v W.a₆ ≤ 1 := by
  rw [← hW, WeierstrassCurve.map_a₆]; exact W₀.a₆.2

/-- For `v(x) > 1`, the right-hand side of the Weierstrass equation has valuation `v(x)³`: the
`x³` term strictly dominates the rest. This is `Valuation.map_cubic_of_one_lt` at the
coefficients `a₂`, `a₄`, `a₆`, whose integrality the model supplies. -/
private lemma valuation_rhs_eq {x : F} (hA1 : 1 < Valued.v x) :
    Valued.v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) = Valued.v x ^ 3 := by
  rw [show x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆)) = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ by
    ring]
  exact Valued.v.map_cubic_of_one_lt (valuation_a₂_le_one hW) (valuation_a₄_le_one hW)
    (valuation_a₆_le_one hW) hA1

/-- When `v(y)` dominates `v(x)` and exceeds `1`, the left-hand side of the Weierstrass equation
has valuation `v(y)²`: the `y²` term strictly dominates the rest. -/
private lemma valuation_lhs_eq {x y : F} (hAB : Valued.v x < Valued.v y)
    (hB1 : 1 < Valued.v y) : Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) = Valued.v y ^ 2 := by
  set B := Valued.v y
  have h2 : Valued.v (W.a₁ * x * y) < B ^ 2 := by
    rw [map_mul, map_mul]
    calc Valued.v W.a₁ * Valued.v x * B ≤ 1 * Valued.v x * B :=
        mul_le_mul' (mul_le_mul' (valuation_a₁_le_one hW) le_rfl) le_rfl
      _ = Valued.v x * B := by rw [one_mul]
      _ < B * B := mul_lt_mul_of_pos_right hAB (zero_lt_one.trans hB1)
      _ = B ^ 2 := (sq B).symm
  have h3 : Valued.v (W.a₃ * y) < B ^ 2 := by
    rw [map_mul]
    calc Valued.v W.a₃ * B ≤ 1 * B := mul_le_mul' (valuation_a₃_le_one hW) le_rfl
      _ = B ^ 1 := by rw [one_mul, pow_one]
      _ < B ^ 2 := pow_lt_pow_right₀ hB1 (by lia)
  rw [Valuation.map_add_eq_of_lt_left _
    (by rw [map_pow]; exact lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt h2 h3)), map_pow]

/-- A common bound `C ≥ 1` on `v(x)` and `v(y)` bounds the left-hand side of the Weierstrass
equation by `C²`. -/
private lemma valuation_lhs_le {x y : F} {C : Γ₀} (hxC : Valued.v x ≤ C)
    (hyC : Valued.v y ≤ C) (h1C : 1 ≤ C) :
    Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) ≤ C ^ 2 := by
  refine le_trans (Valued.v.map_add _ _) (max_le ?_ (le_trans (Valued.v.map_add _ _)
    (max_le ?_ ?_)))
  · rw [map_pow]
    exact pow_le_pow_left' hyC 2
  · rw [map_mul, map_mul]
    calc Valued.v W.a₁ * Valued.v x * Valued.v y ≤ 1 * C * C :=
        mul_le_mul' (mul_le_mul' (valuation_a₁_le_one hW) hxC) hyC
      _ = C ^ 2 := by rw [one_mul, sq]
  · rw [map_mul]
    calc Valued.v W.a₃ * Valued.v y ≤ 1 * C := mul_le_mul' (valuation_a₃_le_one hW) hyC
      _ = C := one_mul C
      _ ≤ C ^ 2 := le_self_pow h1C (by lia)

end

/-- The two sides of the Weierstrass equation have the same valuation, for any point on the
curve. -/
private lemma valuation_lhs_eq_rhs {x y : F} (hxy : W.Equation x y) :
    Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) =
      Valued.v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) :=
  congrArg Valued.v (by linear_combination (W.equation_iff x y).mp hxy)

end Coefficients

/-! ### The dichotomy, over a discretely valued field

This is where `Γ₀ = ℤᵐ⁰` is used: the parity argument that rules out `v(x) = exp 1` needs the
value group to be `ℤ`. The bounds above are applied at `Γ₀ := ℤᵐ⁰`. -/

section Discrete

variable [Valued F ℤᵐ⁰] {W : Affine F}
  {W₀ : WeierstrassCurve (Valued.v : Valuation F ℤᵐ⁰).valuationSubring}
  (hW : W₀.map (algebraMap (Valued.v : Valuation F ℤᵐ⁰).valuationSubring F) = W)

-- Named rather than inlined because `exp` is not a `simp`-normal form here: the bound produced by
-- `valuation_lhs_le` is `(exp 1) ^ 2` while the right-hand side is compared as `exp _`, and no
-- ordinary rewrite bridges the two.
/-- Squaring `exp 1` gives `exp 2`. -/
private lemma exp_one_sq : (exp (1 : ℤ) : ℤᵐ⁰) ^ 2 = exp (2 : ℤ) := by
  rw [← exp_nsmul, nsmul_eq_mul]; norm_num

section

include hW

/-- **No affine point has `v(x) = exp 1`**: a pole of the `x`-coordinate has even order.

If `v(x) = exp 1` then the right-hand side of the Weierstrass equation has valuation `exp 3`. The
left-hand side cannot match it: for `v(y) ≤ exp 1` it is bounded by `exp 2`, and for `v(y) > exp 1`
it equals `v(y)²`, which is an even power of `exp` and so is never `exp 3`. -/
private lemma valuation_ne_exp_one {x y : F} (hxy : W.Equation x y) :
    Valued.v x ≠ exp (1 : ℤ) := by
  intro hA1
  have hval := valuation_lhs_eq_rhs hxy
  have hRHS : Valued.v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) = exp (3 : ℤ) := by
    rw [valuation_rhs_eq hW (by rw [hA1, ← exp_zero, exp_lt_exp]; lia), hA1, ← exp_nsmul,
      nsmul_eq_mul]
    norm_num
  rcases le_or_gt (Valued.v y) (exp 1) with hB1 | hB1
  · -- `v(y) ≤ exp 1` bounds the left-hand side by `exp 2 < exp 3`
    have hle := valuation_lhs_le hW hA1.le hB1 (by rw [← exp_zero, exp_le_exp]; lia)
    rw [hval, hRHS, exp_one_sq, exp_le_exp] at hle
    lia
  · -- `v(y) > exp 1` gives `v(y)² = exp 3`, impossible by parity
    have hB3 : Valued.v y ^ 2 = exp (3 : ℤ) := by
      rw [← valuation_lhs_eq hW (hA1 ▸ hB1) ((by rw [← exp_zero, exp_lt_exp]; lia :
        (1 : ℤᵐ⁰) < exp (1 : ℤ)).trans hB1), hval, hRHS]
    obtain ⟨b, hb⟩ : ∃ b : ℤ, Valued.v y = exp b :=
      ⟨_, (exp_log (exp_pos.trans hB1).ne').symm⟩
    rw [hb, ← exp_nsmul, exp_inj, nsmul_eq_mul] at hB3
    push_cast at hB3
    lia

/-- The `x`-half of the dichotomy: an `x`-coordinate whose pole has order less than two is
integral. Its valuation is a power of `exp`, the exponent is at most `1` by hypothesis, and
`valuation_ne_exp_one` rules the exponent `1` out. -/
private lemma valuation_x_le_one_of_lt_exp_two {x y : F} (hxy : W.Equation x y)
    (hx : Valued.v x < exp (2 : ℤ)) : Valued.v x ≤ 1 := by
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · exact h0 ▸ zero_le
  · obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v x = exp a := ⟨_, (exp_log h0).symm⟩
    have ha1 : a ≤ 1 := by
      by_contra hlt
      exact absurd (ha ▸ exp_le_exp.mpr (by lia : (2 : ℤ) ≤ a)) (not_le.mpr hx)
    rcases eq_or_lt_of_le ha1 with h1 | h1
    · exact absurd (by rw [ha, h1]) (valuation_ne_exp_one hW hxy)
    · rw [ha, ← exp_zero, exp_le_exp]
      lia

/-- **An affine point whose `x`-coordinate has pole order less than two is integral.**

The `x`-coordinate of an affine point of `W` is either integral or has a pole of order at least
two, and in the former case the `y`-coordinate is integral too. -/
theorem valuation_x_le_one_and_valuation_y_le_one_of_valuation_x_lt_exp_two {x y : F}
    (hxy : W.Equation x y) (hx : Valued.v x < exp (2 : ℤ)) :
    Valued.v x ≤ 1 ∧ Valued.v y ≤ 1 := by
  have hA1 := valuation_x_le_one_of_lt_exp_two hW hxy hx
  refine ⟨hA1, ?_⟩
  -- `x` is integral, so the curve equation makes `y` integral over `O_v`
  -- (`isIntegral_y_of_equation_of_isIntegral_x`), and `O_v` is integrally closed in `K_v`.
  have hxy' : (W₀.map
      (algebraMap (Valued.v : Valuation F ℤᵐ⁰).valuationSubring F)).toAffine.Equation x y :=
    hW ▸ hxy
  have hy : IsIntegral (Valued.v : Valuation F ℤᵐ⁰).valuationSubring y :=
    _root_.TauCeti.WeierstrassCurve.isIntegral_y_of_equation_of_isIntegral_x W₀ hxy'
      (isIntegral_algebraMap (x := (⟨x, hA1⟩ : (Valued.v : Valuation F ℤᵐ⁰).valuationSubring)))
  exact (Valuation.valuationSubring.integers Valued.v).isIntegral_iff_v_le_one.mp hy

end

end Discrete

end WeierstrassCurve.Affine
