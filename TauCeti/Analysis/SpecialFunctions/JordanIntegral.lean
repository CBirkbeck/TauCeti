/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Jordan's integral bound

The estimate

$$\int_0^\pi e^{-c\sin\theta}\,d\theta \;\le\; \frac{\pi}{c} \qquad (c > 0)$$

which is the analytic engine of **Jordan's lemma** in contour integration. The integrand is
close to `1` near the endpoints `θ = 0, π`, so the bound is not obtained by a pointwise
estimate on the whole interval; what makes it work is **Jordan's inequality**
`sin θ ≥ (2/π) θ` on `[0, π/2]` (Mathlib's `Real.mul_le_sin`), which forces enough decay near
the endpoint to make the whole integral `O(1/c)`.

That `1/c` is exactly what cancels the length of a semicircular arc of radius `c` when this is
applied to `|e^{iaz}| = e^{-aR\sin\theta}`, and it is why Jordan's lemma beats the naive
`ML` bound: the latter would need the integrand to decay faster than `1/R`, while this needs
no decay at all beyond boundedness.

## Main results

* `TauCeti.integral_exp_neg_mul_sin_le` — the bound above.
* `TauCeti.integral_exp_neg_mul_sin_nonneg` — the integral is nonnegative, so the bound pins it
  to `[0, π/c]`.

## References

* C. Jordan, *Cours d'analyse de l'École Polytechnique*, vol. 2 (1894), §270.
* P. Henrici, *Applied and Computational Complex Analysis*, vol. 1, §4.8.
-/

public section

open Real intervalIntegral MeasureTheory Set

namespace TauCeti

/-- The exponential of a negative multiple of the sine is continuous, hence integrable on any
interval. -/
private theorem intervalIntegrable_exp_neg_mul_sin (c a b : ℝ) :
    IntervalIntegrable (fun θ => Real.exp (-c * Real.sin θ)) volume a b :=
  (Real.continuous_exp.comp (continuous_const.mul Real.continuous_sin)).intervalIntegrable a b

/-- The elementary decaying exponential integral `∫₀^b e^{-kθ} dθ = (1 - e^{-kb})/k`. -/
private theorem integral_exp_neg_mul (k b : ℝ) (hk : k ≠ 0) :
    ∫ θ in (0 : ℝ)..b, Real.exp (-k * θ) = (1 - Real.exp (-k * b)) / k := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.exp) (c := -k) (neg_ne_zero.mpr hk),
    integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

/-- On `[0, π/2]` Jordan's inequality bounds the integrand by a decaying exponential. -/
private theorem exp_neg_mul_sin_le (c : ℝ) (hc : 0 < c) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (π / 2)) :
    Real.exp (-c * Real.sin θ) ≤ Real.exp (-(2 * c / π) * θ) := by
  refine Real.exp_le_exp.mpr ?_
  have hjordan : 2 / π * θ ≤ Real.sin θ := Real.mul_le_sin hθ.1 hθ.2
  have : 2 * c / π * θ ≤ c * Real.sin θ := by
    have := mul_le_mul_of_nonneg_left hjordan hc.le
    calc 2 * c / π * θ = c * (2 / π * θ) := by ring
      _ ≤ c * Real.sin θ := this
  linarith

/-- The integrand is positive, so the integral over `[0, π]` is nonnegative. -/
theorem integral_exp_neg_mul_sin_nonneg (c : ℝ) :
    0 ≤ ∫ θ in (0 : ℝ)..π, Real.exp (-c * Real.sin θ) :=
  intervalIntegral.integral_nonneg Real.pi_nonneg fun _ _ => (Real.exp_pos _).le

/-- Half the interval carries half the integral: `θ ↦ π - θ` exchanges `[0, π/2]` and
`[π/2, π]` and fixes `sin`. -/
private theorem integral_exp_neg_mul_sin_eq_two_mul (c : ℝ) :
    ∫ θ in (0 : ℝ)..π, Real.exp (-c * Real.sin θ)
      = 2 * ∫ θ in (0 : ℝ)..(π / 2), Real.exp (-c * Real.sin θ) := by
  have hsplit : ∫ θ in (0 : ℝ)..π, Real.exp (-c * Real.sin θ)
      = (∫ θ in (0 : ℝ)..(π / 2), Real.exp (-c * Real.sin θ))
        + ∫ θ in (π / 2)..π, Real.exp (-c * Real.sin θ) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_exp_neg_mul_sin c 0 (π / 2))
      (intervalIntegrable_exp_neg_mul_sin c (π / 2) π)).symm
  have hrefl : ∫ θ in (π / 2)..π, Real.exp (-c * Real.sin θ)
      = ∫ θ in (0 : ℝ)..(π / 2), Real.exp (-c * Real.sin θ) := by
    calc ∫ θ in (π / 2)..π, Real.exp (-c * Real.sin θ)
        = ∫ θ in (π / 2)..π, Real.exp (-c * Real.sin (π - θ)) :=
          intervalIntegral.integral_congr fun x _ => by rw [Real.sin_pi_sub]
      _ = ∫ θ in (0 : ℝ)..(π / 2), Real.exp (-c * Real.sin θ) := by
          have h := intervalIntegral.integral_comp_sub_left
            (fun θ => Real.exp (-c * Real.sin θ)) (a := π / 2) (b := π) π
          rw [show π - π = (0 : ℝ) by ring, show π - π / 2 = π / 2 by ring] at h
          exact h
  rw [hsplit, hrefl]
  ring

/-- **Jordan's integral bound.** For `c > 0`,
`∫₀^π e^{-c sin θ} dθ ≤ π / c`. -/
theorem integral_exp_neg_mul_sin_le (c : ℝ) (hc : 0 < c) :
    (∫ θ in (0 : ℝ)..π, Real.exp (-c * Real.sin θ)) ≤ π / c := by
  have hk : 2 * c / π ≠ 0 := by positivity
  have hhalf : (∫ θ in (0 : ℝ)..(π / 2), Real.exp (-c * Real.sin θ)) ≤ π / (2 * c) := by
    have hmono : (∫ θ in (0 : ℝ)..(π / 2), Real.exp (-c * Real.sin θ))
        ≤ ∫ θ in (0 : ℝ)..(π / 2), Real.exp (-(2 * c / π) * θ) := by
      refine intervalIntegral.integral_mono_on (by positivity)
        (intervalIntegrable_exp_neg_mul_sin c 0 (π / 2))
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
        fun θ hθ => exp_neg_mul_sin_le c hc hθ
    refine hmono.trans ?_
    rw [integral_exp_neg_mul _ _ hk]
    have hpi : π * (2 * c / π) = 2 * c := by field_simp
    rw [div_le_div_iff₀ (by positivity) (by positivity), hpi]
    nlinarith [Real.exp_pos (-(2 * c / π) * (π / 2)), hc]
  rw [integral_exp_neg_mul_sin_eq_two_mul]
  calc 2 * ∫ θ in (0 : ℝ)..(π / 2), Real.exp (-c * Real.sin θ)
      ≤ 2 * (π / (2 * c)) := by linarith
    _ = π / c := by field_simp

end TauCeti

end
