/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# `Lᵖ` seminorm bounds out of bounds between the integrals `∫⁻ ‖·‖ₑ ^ p`

For `0 < p < ∞` the `Lᵖ` seminorm of `v` is by definition the `p`-th root of
`∫⁻ ‖v x‖ₑ ^ p ∂μ`, so a bound `∫⁻ ‖v‖ₑ ^ p ≤ c ^ p * ∫⁻ ‖w‖ₑ ^ p` between those integrals is the
same statement as `‖v‖_p ≤ c * ‖w‖_p` between the seminorms. This file records the passage from
the former to the latter, which is the direction an estimate proved by integration produces.

The two functions are allowed to take values in different normed groups, so the statement also
covers comparing a function with its derivative.

## Main declarations

* `TauCeti.eLpNorm_le_eLpNorm_of_lintegral_rpow_le`: from
  `∫⁻ ‖v‖ₑ ^ p ≤ c ^ p * ∫⁻ ‖w‖ₑ ^ p` conclude `‖v‖_p ≤ c * ‖w‖_p`.
* `TauCeti.rpow_lintegral_enorm_le_measure_univ_rpow_mul`: the nesting `L^r ⊆ L^1`, in the same
  `∫⁻` form — `(∫⁻ ‖f‖ₑ) ^ r ≤ μ univ ^ (r - 1) * ∫⁻ ‖f‖ₑ ^ r`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

/-- Turn a bound between the `∫⁻ ‖·‖ₑ ^ p` integrals into a bound between the `Lᵖ` seminorms.
The two functions may have different codomains, which is what lets such a bound compare a
function with its derivative. -/
theorem eLpNorm_le_eLpNorm_of_lintegral_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H] {v : α → G} {w : α → H} {c : ℝ}
    (hc : 0 ≤ c) {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (h : ∫⁻ x, ‖v x‖ₑ ^ p.toReal ∂μ ≤
      ENNReal.ofReal (c ^ p.toReal) * ∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂μ) :
    eLpNorm v p μ ≤ ENNReal.ofReal c * eLpNorm w p μ := by
  have hr0 : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hp₀ hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp]
  calc (∫⁻ x, ‖v x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)
      ≤ (ENNReal.ofReal (c ^ p.toReal) * ∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal c * (∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg hc hr0.le, ← ENNReal.rpow_mul,
          mul_one_div_cancel hr0.ne', ENNReal.rpow_one]

/-- **The nesting `L^r ⊆ L^1`**, in `∫⁻` form and raised to the power `r`: the `L^1` integral is
controlled by the `L^r` integral at the cost of the factor `μ univ ^ (r - 1)`.

This is Hölder's inequality in the shape an estimate proved by integration consumes.  No
finiteness is assumed: when `μ univ = ∞` and `1 < r` the right-hand side is `∞` and the bound is
vacuous. -/
theorem rpow_lintegral_enorm_le_measure_univ_rpow_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {G : Type*} [NormedAddCommGroup G] {f : α → G}
    (hf : AEStronglyMeasurable f μ) {r : ℝ} (hr : 1 ≤ r) :
    (∫⁻ x, ‖f x‖ₑ ∂μ) ^ r ≤ μ Set.univ ^ (r - 1) * ∫⁻ x, ‖f x‖ₑ ^ r ∂μ := by
  have hr0 : (0 : ℝ) < r := one_pos.trans_le hr
  have hCr : eLpNorm f (ENNReal.ofReal r) μ = (∫⁻ x, ‖f x‖ₑ ^ r ∂μ) ^ (1 / r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hr0.le]
  have holder : ∫⁻ x, ‖f x‖ₑ ∂μ
      ≤ (∫⁻ x, ‖f x‖ₑ ^ r ∂μ) ^ (1 / r) * μ Set.univ ^ (1 - 1 / r) := by
    have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := f) (μ := μ) hle hf
    rwa [eLpNorm_one_eq_lintegral_enorm, hCr, ENNReal.toReal_one,
      ENNReal.toReal_ofReal hr0.le, div_one] at this
  have hexp : (1 - r⁻¹) * r = r - 1 := by field_simp
  calc (∫⁻ x, ‖f x‖ₑ ∂μ) ^ r
      ≤ ((∫⁻ x, ‖f x‖ₑ ^ r ∂μ) ^ (1 / r) * μ Set.univ ^ (1 - 1 / r)) ^ r :=
        ENNReal.rpow_le_rpow holder hr0.le
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div, inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one, hexp, mul_comm]

end TauCeti
