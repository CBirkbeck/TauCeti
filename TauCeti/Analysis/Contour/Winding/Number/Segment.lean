/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The generalized winding number of a straight segment through the point

A straight segment traversed symmetrically **through** `z₀` contributes nothing to the
generalized winding number about `z₀`. Concretely, for the real-to-complex inclusion
`γ t = t` on `[-R, R]`, the index integrand `γ̇ t / (γ t - 0) = 1 / t` is odd, so every
`ε`-truncated integral over the symmetric interval `[-R, R]` vanishes identically — not merely
in the limit — and the principal value is `0`.

This is the on-curve counterpart of `ModelSectorWinding.lean`, which computes the winding of an
arc about its *centre*, a point off the curve. Together they supply the two pieces of an
indented contour: a diameter through the singularity contributes `0`, and the semicircular arc
about it contributes `½` (`windingNumber_at_i`), which is the `windingNumber = 1/2` input of the
Hungerbühler–Wasem half-residue theorem `hasCauchyPV_half_residue`.

## Main results

* `TauCeti.Contour.deriv_ofReal` — the real-to-complex inclusion has constant derivative `1`.
* `TauCeti.Contour.integral_eq_zero_of_odd_symm` — an odd integrand has vanishing integral over
  a symmetric interval `[-R, R]`.
* `TauCeti.Contour.hasCauchyPVAt_inv_sub_ofReal` — the principal value of `∮ dz / z` along the
  real segment `[-R, R]` through the origin exists and is `0`.
* `TauCeti.Contour.windingNumber_ofReal` — the corresponding winding number about `0` is `0`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Complex Filter Topology MeasureTheory

namespace TauCeti.Contour

/-- The derivative of the real-to-complex inclusion is constantly `1`. -/
theorem deriv_ofReal : deriv (fun s : ℝ => (s : ℂ)) = fun _ => 1 := by
  funext t
  simpa using ((hasDerivAt_id t).ofReal_comp).deriv

/-- **An odd integrand integrates to zero over a symmetric interval.** No integrability
hypothesis is needed: the substitution `t ↦ -t` maps `[-R, R]` to itself, so the integral equals
its own negative. -/
theorem integral_eq_zero_of_odd_symm {g : ℝ → ℂ} (hodd : ∀ t, g (-t) = -g t) (R : ℝ) :
    ∫ t in (-R)..R, g t = 0 := by
  have hcomp : ∫ t in (-R)..R, g (-t) = ∫ t in (-R)..R, g t := by
    simp [intervalIntegral.integral_comp_neg (a := -R) (b := R) g]
  rw [show (fun t => g (-t)) = fun t => -g t from funext hodd,
    intervalIntegral.integral_neg] at hcomp
  refine add_self_eq_zero.mp ?_
  nth_rewrite 2 [← hcomp]
  ring

/-- The `ε`-truncated index integrand of the real segment through the origin is odd. -/
private theorem truncated_inv_ofReal_odd (ε : ℝ) (t : ℝ) :
    (if ‖((-t : ℝ) : ℂ) - 0‖ > ε then ((((-t : ℝ) : ℂ) - 0)⁻¹ * (1 : ℂ)) else 0) =
      -(if ‖((t : ℝ) : ℂ) - 0‖ > ε then ((((t : ℝ) : ℂ) - 0)⁻¹ * (1 : ℂ)) else 0) := by
  have hnorm : ‖((-t : ℝ) : ℂ) - 0‖ = ‖((t : ℝ) : ℂ) - 0‖ := by
    simp [Complex.norm_real]
  rw [hnorm]
  split_ifs <;> simp

/-- Every `ε`-truncated index integral of the real segment through the origin vanishes. -/
private theorem integral_truncated_inv_ofReal (R ε : ℝ) :
    ∫ t in (-R)..R, (if ‖((t : ℝ) : ℂ) - 0‖ > ε then
      (((t : ℝ) : ℂ) - 0)⁻¹ * deriv (fun s : ℝ => (s : ℂ)) t else 0) = 0 := by
  refine integral_eq_zero_of_odd_symm (fun t => ?_) R
  simpa [deriv_ofReal] using truncated_inv_ofReal_odd ε t

/-- **The real segment through the origin has vanishing principal value.** The index integrand
`1 / t` is odd, so every truncated integral over `[-R, R]` is `0` and the principal value of
`∮ dz / z` along the segment exists with value `0`. -/
theorem hasCauchyPVAt_inv_sub_ofReal (R : ℝ) :
    HasCauchyPVAt (fun t : ℝ => (t : ℂ)) (-R) R (fun z => (z - 0)⁻¹) 0 0 := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine intervalIntegrable_truncated_mul_deriv (γ := fun t : ℝ => (t : ℂ))
      (f := fun z : ℂ => (z - 0)⁻¹) (z₀ := 0) (M := ε⁻¹) ?_ ?_ ?_
    · simp [deriv_ofReal]
    · simp only [deriv_ofReal]
      refine (Measurable.ite ?_ ?_ measurable_const).aestronglyMeasurable
      · exact measurableSet_lt measurable_const (by fun_prop)
      · fun_prop
    · intro t ht
      rw [norm_inv]
      gcongr
  · simp_rw [integral_truncated_inv_ofReal R]
    exact tendsto_const_nhds

/-- **The winding number of a symmetric real segment through the origin vanishes.** -/
theorem windingNumber_ofReal (R : ℝ) :
    windingNumber (fun t : ℝ => (t : ℂ)) (-R) R 0 = 0 := by
  rw [windingNumber_eq_of_hasCauchyPVAt (hasCauchyPVAt_inv_sub_ofReal R)]
  ring

end TauCeti.Contour

end

end
