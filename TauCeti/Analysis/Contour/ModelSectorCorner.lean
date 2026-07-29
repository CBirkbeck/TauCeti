/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Segment
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# The two-ray corner and its vanishing index principal value

The Hungerbühler–Wasem model sector (HW (2.4)) is the closed curve made of a radial segment into
its centre, a circular arc of opening angle `α`, and a radial segment back out. The arc's
contribution is `α / 2π` (`windingNumber_modelSector`); this file supplies the other half, that the
two radial segments contribute nothing.

The two segments cannot be treated separately: each excised integral is `log (R / ε)` in absolute
value and diverges as `ε → 0`. Taken together they cancel *exactly*, at every `ε`, so the pair is
packaged here as a single curve through the centre.

## Main definitions

* `TauCeti.Contour.twoRayCorner` — the corner `z₀` approached along direction `u` and left along
  direction `v`, parametrised on `[-R, R]` with the corner at `t = 0`.

## Main results

* `TauCeti.Contour.hasCauchyPVAt_inv_sub_twoRayCorner` — the index principal value along a two-ray
  corner with `‖u‖ = ‖v‖` is `0`.
* `TauCeti.Contour.windingNumber_eq_zero_twoRayCorner` — its generalized winding number vanishes.

This is Layer 1 of the Hungerbühler–Wasem generalized residue theorem (HW Thm 3.3).

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — (2.4).
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- **The two-ray corner at `z₀`.** For `t < 0` the curve sits at distance `|t| ‖u‖` from `z₀`
along `u`, and for `t ≥ 0` at distance `t ‖v‖` along `v`; it meets `z₀` exactly at `t = 0`.

Concatenated with a circular arc this is the Hungerbühler–Wasem model sector, parametrised from
the far end of one radius rather than from the corner. -/
def twoRayCorner (z₀ u v : ℂ) : ℝ → ℂ :=
  fun t => if t < 0 then z₀ - (t : ℂ) * u else z₀ + (t : ℂ) * v

/-- On the negative ray the corner curve is the affine map `t ↦ z₀ - t u`. -/
private theorem twoRayCorner_eventuallyEq_neg {z₀ u v : ℂ} {t : ℝ} (ht : t < 0) :
    twoRayCorner z₀ u v =ᶠ[𝓝 t] fun s : ℝ => z₀ - (s : ℂ) * u := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  simp [twoRayCorner, if_pos (mem_Iio.mp hs)]

/-- On the positive ray the corner curve is the affine map `t ↦ z₀ + t v`. -/
private theorem twoRayCorner_eventuallyEq_pos {z₀ u v : ℂ} {t : ℝ} (ht : 0 < t) :
    twoRayCorner z₀ u v =ᶠ[𝓝 t] fun s : ℝ => z₀ + (s : ℂ) * v := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp [twoRayCorner, if_neg (not_lt.mpr (mem_Ioi.mp hs).le)]

/-- The derivative of the corner curve off the corner: `-u` on the negative ray, `v` on the
positive ray. -/
private theorem deriv_twoRayCorner_of_ne {z₀ u v : ℂ} {t : ℝ} (ht : t ≠ 0) :
    deriv (twoRayCorner z₀ u v) t = if t < 0 then -u else v := by
  have hofReal : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp (z := t)
  rcases lt_or_gt_of_ne ht with h | h
  · rw [Filter.EventuallyEq.deriv_eq (twoRayCorner_eventuallyEq_neg (v := v) h), if_pos h]
    have hd : HasDerivAt (fun s : ℝ => z₀ - (s : ℂ) * u) (-u) t := by
      have h1 := _root_.HasDerivAt.mul_const hofReal u
      simpa using _root_.HasDerivAt.const_sub z₀ h1
    exact hd.deriv
  · rw [Filter.EventuallyEq.deriv_eq (twoRayCorner_eventuallyEq_pos (u := u) h),
      if_neg (not_lt.mpr h.le)]
    have hd : HasDerivAt (fun s : ℝ => z₀ + (s : ℂ) * v) v t := by
      have h1 := _root_.HasDerivAt.mul_const hofReal v
      simpa using _root_.HasDerivAt.const_add z₀ h1
    exact hd.deriv

/-- **The index integrand along a two-ray corner is `1 / t`,** on both rays: the direction cancels
against itself, leaving the same real function on either side of the corner. -/
private theorem integrand_twoRayCorner {z₀ u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) {t : ℝ}
    (ht : t ≠ 0) :
    (twoRayCorner z₀ u v t - z₀)⁻¹ * deriv (twoRayCorner z₀ u v) t = ((t : ℂ))⁻¹ := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [deriv_twoRayCorner_of_ne (z₀ := z₀) (u := u) (v := v) ht]
  rcases lt_or_gt_of_ne ht with h | h
  · rw [if_pos h]
    simp only [twoRayCorner, if_pos h, sub_sub_cancel_left]
    field_simp
  · rw [if_neg (not_lt.mpr h.le)]
    simp only [twoRayCorner, if_neg (not_lt.mpr h.le), add_sub_cancel_left]
    field_simp

/-- The distance from the corner is `|t|` times the common ray length. -/
private theorem norm_twoRayCorner_sub {z₀ u v : ℂ} (huv : ‖u‖ = ‖v‖) (t : ℝ) :
    ‖twoRayCorner z₀ u v t - z₀‖ = |t| * ‖v‖ := by
  rcases lt_or_ge t 0 with h | h
  · simp only [twoRayCorner, if_pos h, sub_sub_cancel_left]
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, huv]
  · simp only [twoRayCorner, if_neg (not_lt.mpr h), add_sub_cancel_left]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The `ε`-truncated index integrand of a two-ray corner is odd. -/
private theorem truncated_inv_twoRayCorner_odd {z₀ u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : ‖u‖ = ‖v‖) (ε : ℝ) :
    Function.Odd (fun t : ℝ =>
      if ‖twoRayCorner z₀ u v t - z₀‖ > ε then
        (twoRayCorner z₀ u v t - z₀)⁻¹ * deriv (twoRayCorner z₀ u v) t else 0) := by
  intro t
  simp only [norm_twoRayCorner_sub huv, abs_neg]
  rcases eq_or_ne t 0 with rfl | ht
  · simp [twoRayCorner]
  · rw [integrand_twoRayCorner hu hv ht, integrand_twoRayCorner hu hv (neg_ne_zero.mpr ht)]
    split_ifs <;> simp

/-- Every `ε`-truncated index integral along a two-ray corner over `[-R, R]` vanishes. -/
private theorem integral_truncated_inv_twoRayCorner {z₀ u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : ‖u‖ = ‖v‖) (R ε : ℝ) :
    ∫ t in (-R)..R, (if ‖twoRayCorner z₀ u v t - z₀‖ > ε then
      (twoRayCorner z₀ u v t - z₀)⁻¹ * deriv (twoRayCorner z₀ u v) t else 0) = 0 :=
  intervalIntegral.integral_eq_zero_of_odd (truncated_inv_twoRayCorner_odd hu hv huv ε) R


/-- **The index principal value along a two-ray corner vanishes.** With the two rays of equal
length the excision `‖γ t - z₀‖ > ε` is the symmetric condition `|t| ‖v‖ > ε`, and the integrand is
the odd function `1 / t` on both rays, so *every* truncated integral is `0` — not merely its limit.
-/
theorem hasCauchyPVAt_inv_sub_twoRayCorner {z₀ u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : ‖u‖ = ‖v‖) (R : ℝ) :
    HasCauchyPVAt (twoRayCorner z₀ u v) (-R) R (fun z => (z - z₀)⁻¹) z₀ 0 := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hae : (fun t : ℝ => if ‖twoRayCorner z₀ u v t - z₀‖ > ε then
          (twoRayCorner z₀ u v t - z₀)⁻¹ * deriv (twoRayCorner z₀ u v) t else 0)
        =ᵐ[volume.restrict (uIoc (-R) R)]
        fun t : ℝ => if |t| * ‖v‖ > ε then ((t : ℂ))⁻¹ else 0 := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
        (MeasureTheory.measure_singleton (0 : ℝ))] with t ht _
      rw [norm_twoRayCorner_sub huv, integrand_twoRayCorner hu hv ht]
    refine (intervalIntegrable_congr_ae hae.symm).mp ?_
    refine (intervalIntegrable_const (c := (‖v‖ / ε : ℝ))).mono_fun' ?_ ?_
    · refine (Measurable.ite ?_ (by fun_prop) measurable_const).aestronglyMeasurable
      exact measurableSet_lt measurable_const (by fun_prop)
    · filter_upwards with t
      by_cases h : |t| * ‖v‖ > ε
      · rw [if_pos h, norm_inv, Complex.norm_real, Real.norm_eq_abs]
        have hε' : 0 < ε := hε
        have ht0 : 0 < |t| := by
          by_contra hc
          push Not at hc
          rw [le_antisymm hc (abs_nonneg t), zero_mul] at h
          linarith
        rw [le_div_iff₀ hε, inv_mul_eq_div, div_le_iff₀ ht0]
        nlinarith
      · simp only [if_neg h, norm_zero]
        exact div_nonneg (norm_nonneg v) (le_of_lt hε)
  · simp_rw [integral_truncated_inv_twoRayCorner hu hv huv R]
    exact tendsto_const_nhds

/-- **The generalized winding number of a two-ray corner vanishes.** The radial approach and
departure contribute nothing to the model sector's index; all of it comes from the arc. -/
theorem windingNumber_eq_zero_twoRayCorner {z₀ u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : ‖u‖ = ‖v‖) (R : ℝ) :
    windingNumber (twoRayCorner z₀ u v) (-R) R z₀ = 0 := by
  rw [windingNumber_eq_of_hasCauchyPVAt (hasCauchyPVAt_inv_sub_twoRayCorner hu hv huv R)]
  ring

end TauCeti.Contour

end

end
