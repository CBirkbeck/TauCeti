/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Affine
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The generalized winding number of a straight segment through the point

A straight segment traversed symmetrically **through** its reference point contributes nothing to
the generalized winding number about that point. The mechanism is oddness: for the real inclusion
`γ t = t` on `[-R, R]`, the index integrand `γ̇ t / (γ t - 0) = 1 / t` is odd, so every
`ε`-truncated integral over the symmetric interval vanishes *identically* — not merely in the
limit — and the principal value is `0` with no limiting argument at all. The general segment
`γ t = v · t + z₀` about `z₀` then follows by transporting along the affine change of coordinates
of `Winding/Number/Affine.lean`.

This is the on-curve counterpart of `ModelSectorWinding.lean`, which computes the winding of an
arc about its *centre*, a point off the curve. Together they supply the two pieces of an indented
contour: a diameter through the singularity contributes `0`, and the semicircular arc about it
contributes `½` (`windingNumber_at_i`) — the `windingNumber = 1/2` input of the
Hungerbühler–Wasem half-residue theorem `hasCauchyPV_half_residue`.

## Main results

* `intervalIntegral.integral_eq_zero_of_odd` — an odd integrand into a real normed space has
  vanishing integral over a symmetric interval `[-R, R]`.
* `Complex.deriv_ofReal` — the real-to-complex inclusion has constant derivative `1`.
* `TauCeti.Contour.hasCauchyPVAt_inv_sub_segment` / `TauCeti.Contour.windingNumber_segment` — a
  straight segment `v · t + z₀` traversed symmetrically through `z₀` has index principal value
  and winding number `0` about `z₀`.
* `TauCeti.Contour.hasCauchyPVAt_inv_sub_ofReal` / `TauCeti.Contour.windingNumber_ofReal` — the
  real-axis specialization about the origin.

The first two are general-purpose facts, so they are stated in the namespaces of the operations
they describe (`intervalIntegral`, `Complex`) rather than the contour namespace, and are
candidates for upstreaming.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Complex Filter Topology MeasureTheory

/-- **An odd integrand integrates to zero over a symmetric interval.** No integrability
hypothesis is needed: the substitution `t ↦ -t` maps `[-R, R]` to itself, so the integral equals
its own negative. -/
theorem intervalIntegral.integral_eq_zero_of_odd {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → E} (hodd : Function.Odd g) (R : ℝ) :
    ∫ t in (-R)..R, g t = 0 := by
  have hfun : (fun t => g (-t)) = fun t => -g t := funext hodd
  have hcomp : ∫ t in (-R)..R, g (-t) = ∫ t in (-R)..R, g t := by
    simp [intervalIntegral.integral_comp_neg (a := -R) (b := R) g]
  rw [hfun, intervalIntegral.integral_neg] at hcomp
  -- `hcomp` says the integral is its own negative; in a real vector space that forces `0`.
  have htwo : (2 : ℝ) • (∫ t in (-R)..R, g t) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← hcomp]
    abel
  simpa using htwo

/-- The derivative of the real-to-complex inclusion is constantly `1`. -/
@[simp]
theorem Complex.deriv_ofReal : deriv (fun s : ℝ => (s : ℂ)) = fun _ => 1 := by
  funext t
  simpa using ((hasDerivAt_id t).ofReal_comp).deriv

namespace TauCeti.Contour

/-- The `ε`-truncated index integrand of the real segment through the origin is odd. -/
private theorem truncated_inv_ofReal_odd (ε : ℝ) :
    Function.Odd (fun t : ℝ =>
      if ‖((t : ℝ) : ℂ) - 0‖ > ε then ((((t : ℝ) : ℂ) - 0)⁻¹ * (1 : ℂ)) else 0) := by
  intro t
  have hnorm : ‖((-t : ℝ) : ℂ) - 0‖ = ‖((t : ℝ) : ℂ) - 0‖ := by
    simp [Complex.norm_real]
  simp only [hnorm]
  split_ifs <;> simp

/-- Every `ε`-truncated index integral of the real segment through the origin vanishes. -/
private theorem integral_truncated_inv_ofReal (R ε : ℝ) :
    ∫ t in (-R)..R, (if ‖((t : ℝ) : ℂ) - 0‖ > ε then
      (((t : ℝ) : ℂ) - 0)⁻¹ * deriv (fun s : ℝ => (s : ℂ)) t else 0) = 0 := by
  refine intervalIntegral.integral_eq_zero_of_odd (fun t => ?_) R
  simpa using truncated_inv_ofReal_odd ε t

/-- **The real segment through the origin has vanishing principal value.** The index integrand
`1 / t` is odd, so every truncated integral over `[-R, R]` is `0` and the principal value of
`∮ dz / z` along the segment exists with value `0`. -/
theorem hasCauchyPVAt_inv_sub_ofReal (R : ℝ) :
    HasCauchyPVAt (fun t : ℝ => (t : ℂ)) (-R) R (fun z => (z - 0)⁻¹) 0 0 := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine intervalIntegrable_truncated_mul_deriv (γ := fun t : ℝ => (t : ℂ))
      (f := fun z : ℂ => (z - 0)⁻¹) (z₀ := 0) (M := ε⁻¹) ?_ ?_ ?_
    · simp
    · simp only [Complex.deriv_ofReal]
      refine (Measurable.ite ?_ ?_ measurable_const).aestronglyMeasurable
      · exact measurableSet_lt measurable_const (by fun_prop)
      · fun_prop
    · intro t ht
      rw [norm_inv]
      gcongr
  · simp_rw [integral_truncated_inv_ofReal R]
    exact tendsto_const_nhds

/-- **A straight segment through its reference point has vanishing index principal value.** For a
nonzero direction `v`, the segment `γ t = v · t + z₀` traversed over the symmetric interval
`[-R, R]` passes through `z₀` at `t = 0`, and the principal value of `∮ dz / (z - z₀)` along it is
`0`. Transported from the real-axis case by the affine change of coordinates. -/
theorem hasCauchyPVAt_inv_sub_segment {v z₀ : ℂ} (hv : v ≠ 0) (R : ℝ) :
    HasCauchyPVAt (fun t : ℝ => v * (t : ℂ) + z₀) (-R) R (fun z => (z - z₀)⁻¹) z₀ 0 := by
  simpa using hasCauchyPVAt_inv_sub_affine (d := z₀) (hasCauchyPVAt_inv_sub_ofReal R) hv

/-- **The winding number of a straight segment through its reference point vanishes.** -/
theorem windingNumber_segment {v z₀ : ℂ} (hv : v ≠ 0) (R : ℝ) :
    windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) (-R) R z₀ = 0 := by
  rw [windingNumber_eq_of_hasCauchyPVAt (hasCauchyPVAt_inv_sub_segment hv R)]
  ring

/-- The winding number of a symmetric real segment through the origin vanishes: the `v = 1`,
`z₀ = 0` case of `windingNumber_segment`. -/
@[simp]
theorem windingNumber_ofReal (R : ℝ) :
    windingNumber (fun t : ℝ => (t : ℂ)) (-R) R 0 = 0 := by
  rw [windingNumber_eq_of_hasCauchyPVAt (hasCauchyPVAt_inv_sub_ofReal R)]
  ring

end TauCeti.Contour

end

end
