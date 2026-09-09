/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Perron
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# The arithmetic Perron formula

Layer 6.3 gives the truncated Perron kernel of a single ratio `x`.  This file applies it to an
absolutely convergent `L`-series: the integral over the truncated segment of the series against the
Perron integrand is the series of the individual kernels, one for each `x / n`.

## Main results

* `TauCeti.integral_LSeries_mul_perronIntegrand`: the interchange of the integral with the series.
* `TauCeti.truncatedPerron_LSeries`: the truncated summatory formula, as a series of truncated
  Perron kernels at the ratios `x / n`.
-/

public section

namespace TauCeti

open Complex MeasureTheory

open scoped ENNReal Real

variable {f : ℕ → ℂ} {x c T : ℝ}

private theorem norm_term_mul_perronIntegrand_le (hx : 0 < x) (hc : 0 < c) (n : ℕ) (t : ℝ) :
    ‖LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t‖ ≤
      ‖LSeries.term f (c : ℂ) n‖ * (x ^ c / Real.sqrt (c ^ 2 + t ^ 2)) := by
  rw [norm_mul, norm_perronIntegrand hx]
  gcongr
  rcases n with _ | m
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero m), LSeries.term_of_ne_zero (Nat.succ_ne_zero m),
      norm_div, norm_div, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m),
      Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m)]
    simp

/-- The `L¹` bound `integral_tsum` needs.  `√(c² + t²) ≥ c` avoids the arctangent. -/
theorem lintegral_norm_term_mul_perronIntegrand_ne_top (hx : 0 < x) (hc : 0 < c)
    (h : LSeriesSummable f (c : ℂ)) :
    ∑' n : ℕ, ∫⁻ t in Set.Ioc (-T) T,
        ‖LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t‖ₑ ≠ ∞ := by
  have hstep : ∀ n : ℕ, ∫⁻ t in Set.Ioc (-T) T,
      ‖LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t‖ₑ ≤
        ENNReal.ofReal (‖LSeries.term f (c : ℂ) n‖ * (x ^ c / c)) * ENNReal.ofReal (2 * T) := by
    intro n
    have hbd : ∀ t : ℝ, ‖LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t‖ₑ ≤
        ENNReal.ofReal (‖LSeries.term f (c : ℂ) n‖ * (x ^ c / c)) := by
      intro t
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((norm_term_mul_perronIntegrand_le hx hc n t).trans ?_)
      have hge : c ≤ Real.sqrt (c ^ 2 + t ^ 2) :=
        (Real.sqrt_sq hc.le).ge.trans (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t]))
      have hxc : (0 : ℝ) ≤ x ^ c := Real.rpow_nonneg hx.le c
      gcongr
    calc ∫⁻ t in Set.Ioc (-T) T, ‖LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t‖ₑ
        ≤ ∫⁻ _ in Set.Ioc (-T) T,
            ENNReal.ofReal (‖LSeries.term f (c : ℂ) n‖ * (x ^ c / c)) := lintegral_mono hbd
      _ = ENNReal.ofReal (‖LSeries.term f (c : ℂ) n‖ * (x ^ c / c)) * ENNReal.ofReal (2 * T) := by
          rw [setLIntegral_const, Real.volume_Ioc, show T - -T = 2 * T by ring]
  refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hstep) ?_)
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) (h.norm.mul_right _)]
  exact ENNReal.ofReal_lt_top

/-- Each `L`-series term is continuous in the height along the line `Re s = c`. -/
private theorem continuous_term_line (f : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    Continuous fun t : ℝ ↦ LSeries.term f ((c : ℂ) + t * I) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using continuous_const
  · have hline : Continuous fun t : ℝ ↦ (c : ℂ) + t * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    simp only [LSeries.term_of_ne_zero hn]
    refine continuous_const.div (hline.const_cpow (Or.inl hn0)) fun t ↦ ?_
    exact fun h ↦ hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- **The interchange.**  Where the `L`-series converges absolutely on the line `Re s = c`, the
integral over the truncated segment of the series times the Perron integrand is the series of the
integrals. -/
theorem integral_LSeries_mul_perronIntegrand (hx : 0 < x) (hc : 0 < c)
    (h : LSeriesSummable f (c : ℂ)) :
    ∫ t in Set.Ioc (-T) T, (∑' n : ℕ, LSeries.term f ((c : ℂ) + t * I) n) * perronIntegrand x c t
      = ∑' n : ℕ, ∫ t in Set.Ioc (-T) T,
          LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t := by
  rw [← MeasureTheory.integral_tsum (fun n ↦ ?_) (lintegral_norm_term_mul_perronIntegrand_ne_top
    hx hc h)]
  · exact integral_congr_ae (.of_forall fun t ↦ tsum_mul_right.symm)
  · exact ((continuous_term_line f c n).mul
      (continuous_perronIntegrand hx.ne' hc.ne')).aestronglyMeasurable

/-- **Collecting a term into the integrand.**  The `n`-th `L`-series term against the Perron
integrand at `x` is the coefficient `f n` against the Perron integrand at the ratio `x / n`. -/
theorem term_mul_perronIntegrand (hx : 0 < x) (hc : c ≠ 0) (n : ℕ) (t : ℝ) :
    LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t =
      f n * perronIntegrand (x / n) c t := by
  have hline : (c : ℂ) + t * I ≠ 0 := fun h ↦ hc (by simpa using congrArg Complex.re h)
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, zero_mul, Nat.cast_zero, div_zero, perronIntegrand_apply,
      Complex.ofReal_zero, Complex.zero_cpow hline, zero_div, mul_zero]
  · rw [LSeries.term_of_ne_zero hn, perronIntegrand_apply, perronIntegrand_apply,
      Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg n),
      Complex.ofReal_natCast]
    ring

/-- **The truncated Perron formula for an `L`-series.**  Where the series converges absolutely on
the line `Re s = c`, the truncated Perron integral of the series is the series of the truncated
Perron kernels at the ratios `x / n`. -/
theorem truncatedPerron_LSeries (hx : 0 < x) (hc : 0 < c) (hT : 0 ≤ T)
    (h : LSeriesSummable f (c : ℂ)) :
    ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, LSeries f ((c : ℂ) + t * I) * perronIntegrand x c t
      = ∑' n : ℕ, f n * truncatedPerronKernel (x / n) c T := by
  have hle : -T ≤ T := by linarith
  rw [intervalIntegral.integral_of_le hle,
    show (fun t : ℝ ↦ LSeries f ((c : ℂ) + t * I) * perronIntegrand x c t) =
      fun t : ℝ ↦ (∑' n : ℕ, LSeries.term f ((c : ℂ) + t * I) n) * perronIntegrand x c t from rfl,
    integral_LSeries_mul_perronIntegrand hx hc h, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rw [truncatedPerronKernel_apply, intervalIntegral.integral_of_le hle,
    integral_congr_ae (.of_forall fun t ↦ term_mul_perronIntegrand hx hc.ne' n t),
    MeasureTheory.integral_const_mul]
  ring

end TauCeti
