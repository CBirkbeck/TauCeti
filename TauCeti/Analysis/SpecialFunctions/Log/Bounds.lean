/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Bounds for the quadratic remainder of the real logarithm

This file bounds `-log (1 - x) - x` by a quadratic term, then specializes the estimate to
`x = y ^ (-s)`. The sharp factor `2` in the denominator comes from reading Mathlib's complex
logarithm bound along the reals.

## Main results

* `TauCeti.neg_log_one_sub_sub_nonneg`: the remainder is nonnegative for `x < 1`.
* `TauCeti.neg_log_one_sub_sub_le`: for `0 ≤ x < 1`, it is at most `x² / (2 (1 - x))`.
* `TauCeti.neg_log_one_sub_rpow_sub_le_div`: for `2 ≤ y` and `0 < s`, it is at most
  `y ^ (-2s) / (2 (1 - 2 ^ (-s)))`.
* `TauCeti.neg_log_one_sub_rpow_sub_le`: for `2 ≤ y` and `1 ≤ s`, it is at most `y⁻²`.

## References

The shape of `neg_log_one_sub_sub_le` follows the private declaration of the same name in
`CebotarevDensity/Density.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
C. Birkbeck and R. Brasca), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The sharper
constant here comes from Mathlib's `Complex.norm_log_one_sub_inv_sub_self_le`.
-/

public section

namespace TauCeti

/-- The quadratic remainder of `-log (1 - x)` is nonnegative for `x < 1`. -/
theorem neg_log_one_sub_sub_nonneg {x : ℝ} (hx1 : x < 1) :
    0 ≤ -Real.log (1 - x) - x := by
  linarith [Real.log_le_sub_one_of_pos (sub_pos.mpr hx1)]

/-- The quadratic remainder of `-log (1 - x)` is at most `x² / (2 (1 - x))` for
`0 ≤ x < 1`. This is Mathlib's complex logarithm bound read along the reals. -/
theorem neg_log_one_sub_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) - x ≤ x ^ 2 / (2 * (1 - x)) := by
  have hz : ‖(x : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg hx0]
  have key := Complex.norm_log_one_sub_inv_sub_self_le hz
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv,
    ← Complex.ofReal_log (by positivity), ← Complex.ofReal_sub, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hx0, Real.log_inv] at key
  exact ((Real.le_norm_self _).trans key).trans_eq (by field_simp)

/-- If `2 ≤ y` and `1 ≤ s`, then `y ^ (-s) ≤ 1 / 2`. -/
theorem rpow_neg_le_half {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) : y ^ (-s) ≤ 1 / 2 :=
  calc y ^ (-s) ≤ (2 : ℝ) ^ (-s) := Real.rpow_le_rpow_of_nonpos two_pos hy (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    _ = 1 / 2 := by norm_num

/-- For `2 ≤ y` and `0 < s`, the quadratic remainder of `-log (1 - y ^ (-s))` is
nonnegative. -/
theorem neg_log_one_sub_rpow_sub_nonneg {y s : ℝ} (hy : 2 ≤ y) (hs : 0 < s) :
    0 ≤ -Real.log (1 - y ^ (-s)) - y ^ (-s) :=
  neg_log_one_sub_sub_nonneg (Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith))

/-- For `2 ≤ y` and `0 < s`, the quadratic remainder of `-log (1 - y ^ (-s))` is bounded by
`y ^ (-2s) / (2 (1 - 2 ^ (-s)))`. -/
theorem neg_log_one_sub_rpow_sub_le_div {y s : ℝ} (hy : 2 ≤ y) (hs : 0 < s) :
    -Real.log (1 - y ^ (-s)) - y ^ (-s) ≤
      y ^ (-(2 * s)) / (2 * (1 - (2 : ℝ) ^ (-s))) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hxle : y ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos two_pos hy (by linarith)
  have h2lt : (2 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  calc
    -Real.log (1 - y ^ (-s)) - y ^ (-s) ≤
        (y ^ (-s)) ^ 2 / (2 * (1 - y ^ (-s))) :=
      neg_log_one_sub_sub_le (Real.rpow_nonneg hy0.le _) (hxle.trans_lt h2lt)
    _ ≤ (y ^ (-s)) ^ 2 / (2 * (1 - (2 : ℝ) ^ (-s))) := by
      gcongr
    _ = y ^ (-(2 * s)) / (2 * (1 - (2 : ℝ) ^ (-s))) := by
      rw [pow_two, ← Real.rpow_add hy0, ← two_mul, mul_neg]

/-- For `2 ≤ y` and `1 ≤ s`, the quadratic remainder of `-log (1 - y ^ (-s))` is at most
`y⁻²`. -/
theorem neg_log_one_sub_rpow_sub_le {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) :
    -Real.log (1 - y ^ (-s)) - y ^ (-s) ≤ y ^ (-(2 : ℝ)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hxhalf : y ^ (-s) ≤ 1 / 2 := rpow_neg_le_half hy hs
  calc
    -Real.log (1 - y ^ (-s)) - y ^ (-s) ≤ (y ^ (-s)) ^ 2 / (2 * (1 - y ^ (-s))) :=
      neg_log_one_sub_sub_le (Real.rpow_nonneg hy0.le _) (by linarith)
    _ ≤ (y ^ (-s)) ^ 2 := div_le_self (sq_nonneg _) (by linarith)
    _ = y ^ (-(2 * s)) := by rw [pow_two, ← Real.rpow_add hy0, ← two_mul, mul_neg]
    _ ≤ y ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end TauCeti
