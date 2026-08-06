/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.CuspCircle

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Complex.Periodic
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The ceiling contour integral is a `q`-circle integral

The change of variables for the cusp term of the valence contour: along the truncation
ceiling the contour derivative is `1`, the `q`-parameter maps the ceiling onto the
`q`-circle of radius `e^{-2πH}`, and the logarithmic derivative of a width-`1` periodic
function factors through its cusp function — so the ceiling contour integral of the
logarithmic derivative equals the `q`-circle integral of the cusp function's logarithmic
derivative.

## Main declarations

* `TauCeti.ModularForm.intervalIntegral_ceiling_eq_circleIntegral_logDeriv_cuspFunction`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Seg5CuspIntegral.lean`) this file ports
  onto the current Mathlib pin.
-/

public section

open Complex Function intervalIntegral MeasureTheory Set

open scoped Real

namespace TauCeti

namespace ModularForm

/-- The ceiling contour integral of the logarithmic derivative of a width-`1` periodic
function on the upper half-plane is the `q`-circle integral of its cusp function's
logarithmic derivative: the contour derivative is `1` on the ceiling, the `q`-parameter
carries the ceiling onto the `q`-circle, and the logarithmic derivative factors through
the cusp function. -/
theorem intervalIntegral_ceiling_eq_circleIntegral_logDeriv_cuspFunction
    {g : UpperHalfPlane → ℂ} {H : ℝ}
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) 1) :
    ∫ t in (4 : ℝ)..5,
        deriv (fdBoundary H) t • logDeriv (g ∘ UpperHalfPlane.ofComplex) (fdBoundary H t) =
      circleIntegral (logDeriv (UpperHalfPlane.cuspFunction 1 g)) 0 (fdBoundaryQRadius H) := by
  set R := fdBoundaryQRadius H with hR
  set Lc := logDeriv (UpperHalfPlane.cuspFunction 1 g) with hLc
  have hcusp : UpperHalfPlane.cuspFunction 1 g =
      Function.Periodic.cuspFunction 1 (g ∘ UpperHalfPlane.ofComplex) := rfl
  -- the circle integrand is `2π`-periodic
  have hcper : Function.Periodic
      (fun θ ↦ deriv (circleMap 0 R) θ • Lc (circleMap 0 R θ)) (2 * π) := fun θ ↦ by
    simp only []
    rw [TauCeti.Function.Periodic.deriv (periodic_circleMap 0 R) θ,
      periodic_circleMap 0 R θ]
  -- shift the circle integral to `[-π, π]`
  have h2π : -π + 2 * π = π := by ring
  have h0π : (0 : ℝ) + 2 * π = 2 * π := by ring
  have hshift : circleIntegral Lc 0 R = ∫ θ in (-π)..π,
      deriv (circleMap 0 R) θ • Lc (circleMap 0 R θ) := by
    rw [circleIntegral, ← h0π, ← Function.Periodic.intervalIntegral_add_eq hcper (-π) 0,
      h2π]
  -- substitute the affine angle map `θ = 2π·t + -(9π)`
  have h := intervalIntegral.integral_comp_mul_add
    (f := fun θ ↦ deriv (circleMap 0 R) θ • Lc (circleMap 0 R θ))
    (by positivity : (2 * π : ℝ) ≠ 0) (-(9 * π)) (a := 4) (b := 5)
  have h4 : 2 * π * 4 + -(9 * π) = -π := by ring
  have h5 : 2 * π * 5 + -(9 * π) = π := by ring
  rw [h4, h5] at h
  have hcov : (∫ θ in (-π)..π, deriv (circleMap 0 R) θ • Lc (circleMap 0 R θ)) =
      (2 * π) • ∫ t in (4 : ℝ)..5,
        deriv (circleMap 0 R) (2 * π * t + -(9 * π)) •
          Lc (circleMap 0 R (2 * π * t + -(9 * π))) := by
    rw [h, smul_smul, mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), one_smul]
  -- identify the substituted integrand with the contour integrand on the open ceiling
  rw [hshift, hcov, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun t ht ↦ ?_
  have hgt : (4 : ℝ) < t := ht.1
  have hchain := TauCeti.Periodic.logDeriv_eq_logDeriv_cuspFunction_mul_deriv_qParam
    (one_ne_zero) hper (fdBoundary_segment5 H t)
  have hangle : 2 * Real.pi * (t - 9 / 2) = 2 * π * t + -(9 * π) := by ring
  have hqe : Function.Periodic.qParam 1 (fdBoundary_segment5 H t) =
      circleMap 0 R (2 * π * t + -(9 * π)) := by
    rw [qParam_fdBoundary_segment5 H t, hangle, hR]
  rw [deriv_fdBoundary_of_gt_four hgt, one_smul, fdBoundary_of_gt_four hgt, hchain,
    TauCeti.Periodic.deriv_qParam, hqe, hLc, hcusp, deriv_circleMap, smul_eq_mul,
    Complex.real_smul]
  push_cast
  ring

end ModularForm

end TauCeti

end
