/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Convex
public import TauCeti.Analysis.Contour.Winding.Vanishing
public import TauCeti.Analysis.Contour.Winding.LocallyConstant
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# Winding of the fundamental-domain boundary: the exterior

The boundary contour lies in the half-plane `im ≥ √3/2`, so every point strictly below
that height sits in the unbounded connected component of the complement, where the
winding number vanishes: the exterior determination feeding the valence-formula residue
count.

## Main declarations

* `TauCeti.ModularForm.sqrt_three_div_two_le_im_fdBoundary`: the image height bound.
* `TauCeti.ModularForm.windingNumber_fdBoundary_eq_zero_of_im_lt`: points below the
  contour wind zero, with the analogous determinations on the other three sides
  (`_of_half_lt_re`, `_of_re_lt_neg_half`, `_of_lt_im`).
-/

public noncomputable section

open Complex Set UpperHalfPlane TauCeti.Contour

open scoped Real

namespace TauCeti

namespace ModularForm

variable {H t : ℝ}

/-- Every point of the boundary contour has imaginary part at least `√3/2`, provided the
height parameter clears the corner row. -/
lemma sqrt_three_div_two_le_im_fdBoundary (hH : 1 ≤ H) (ht : t ∈ Icc (0 : ℝ) 5) :
    Real.sqrt 3 / 2 ≤ (fdBoundary H t).im := by
  obtain ⟨ht0, ht5⟩ := ht
  have h32 : Real.sqrt 3 / 2 ≤ 1 := by
    rw [div_le_one (by norm_num)]
    nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]
  rcases le_or_gt t 1 with h1 | h1
  · rw [fdBoundary_of_le_one h1, fdBoundary_segment1_apply, AffineMap.lineMap_apply_module']
    have : ((ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)).im = Real.sqrt 3 / 2 - H := by
      simp [ρ]
    rw [Complex.add_im, Complex.smul_im, this]
    have him : (1 / 2 + H * Complex.I : ℂ).im = H := by simp
    rw [him, smul_eq_mul]
    nlinarith [mul_nonneg (by linarith [ht0] : (0 : ℝ) ≤ t)
      (by linarith : (0 : ℝ) ≤ H - Real.sqrt 3 / 2), h1, h32, hH,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)
      (by linarith : (0 : ℝ) ≤ H - Real.sqrt 3 / 2)]
  · rcases le_or_gt t 3 with h3 | h3
    · rw [eqOn_fdBoundary_arc H ⟨h1.le, h3⟩, circleMap_zero_im, one_mul]
      have harc : Real.pi / 3 ≤ (t + 1) * (Real.pi / 6) ∧
          (t + 1) * (Real.pi / 6) ≤ 2 * Real.pi / 3 := by
        constructor <;> nlinarith [Real.pi_pos, h1, h3]
      calc Real.sqrt 3 / 2 = Real.sin (Real.pi / 3) := (Real.sin_pi_div_three).symm
        _ ≤ Real.sin ((t + 1) * (Real.pi / 6)) := by
            rcases le_or_gt ((t + 1) * (Real.pi / 6)) (Real.pi / 2) with hle | hgt
            · exact Real.sin_le_sin_of_le_of_le_pi_div_two
                (by linarith [Real.pi_pos]) hle harc.1
            · nth_rewrite 2 [← Real.sin_pi_sub]
              refine Real.sin_le_sin_of_le_of_le_pi_div_two
                (by linarith [Real.pi_pos]) ?_ ?_ <;> linarith [Real.pi_pos, harc.2, hgt]
    · rcases le_or_gt t 4 with h4 | h4
      · rw [fdBoundary_of_le_four h3 h4, fdBoundary_segment4_apply,
          AffineMap.lineMap_apply_module']
        have : ((-1 / 2 + H * Complex.I : ℂ) - (ρ : ℂ)).im = H - Real.sqrt 3 / 2 := by
          simp [ρ]
        rw [Complex.add_im, Complex.smul_im, this]
        have hρ : (ρ : ℂ).im = Real.sqrt 3 / 2 := by simp [ρ]
        rw [hρ, smul_eq_mul]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t - 3)
          (by linarith : (0 : ℝ) ≤ H - Real.sqrt 3 / 2)]
      · rw [fdBoundary_of_gt_four h4, fdBoundary_segment5_apply,
          AffineMap.lineMap_apply_module']
        have h5 : ((1 / 2 + H * Complex.I : ℂ) - (-1 / 2 + H * Complex.I)).im = 0 := by
          simp
        rw [Complex.add_im, Complex.smul_im, h5]
        have him : (-1 / 2 + H * Complex.I : ℂ).im = H := by simp
        rw [him, smul_eq_mul, mul_zero]
        nlinarith [hH, h32]

/-- Winding transport through an unbounded convex region avoiding the contour: the
region lies in one connected component of the complement, which reaches points far away
where the winding number vanishes. -/
private lemma windingNumber_fdBoundary_eq_zero_of_mem_convex {S : Set ℂ}
    (hconv : Convex ℝ S) (hdisj : S ⊆ (fdBoundary H '' uIcc (0 : ℝ) 5)ᶜ)
    (hunb : ∀ R : ℝ, ∃ z ∈ S, R < ‖z‖) {w : ℂ} (hw : w ∈ S) :
    windingNumber (fdBoundary H) 0 5 w = 0 := by
  obtain ⟨p, hdiff⟩ := (isPiecewiseC1On_fdBoundary H).exists_finset_differentiableAt
  have hclosed := (fdBoundary_closed H).symm
  have hP : ((p : Set ℝ)).Countable := p.finite_toSet.countable
  have hcont : ContinuousOn (fdBoundary H) (uIcc 0 5) :=
    (continuous_fdBoundary H).continuousOn
  have hint := (isPiecewiseC1On_fdBoundary H).intervalIntegrable_deriv
  have h_ev := windingNumber_eventually_zero_cocompact hclosed hP hcont hdiff hint
  rw [Filter.eventually_iff, Filter.mem_cocompact] at h_ev
  obtain ⟨K, hK, hKsub⟩ := h_ev
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨w₀, hw₀S, hw₀far⟩ := hunb r
  have hw₀_notK : w₀ ∉ K := fun hmem ↦ by
    have := hr hmem
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hw₀_zero : windingNumber (fdBoundary H) 0 5 w₀ = 0 := (hKsub hw₀_notK).2
  have h_sub : S ⊆ connectedComponentIn ((fdBoundary H '' uIcc (0 : ℝ) 5)ᶜ) w₀ :=
    hconv.isPreconnected.subset_connectedComponentIn hw₀S hdisj
  rw [windingNumber_eq_of_mem_connectedComponentIn hclosed hP hcont hdiff hint (h_sub hw)]
  exact hw₀_zero

/-- Every point strictly below the contour's height winds zero. -/
theorem windingNumber_fdBoundary_eq_zero_of_im_lt (hH : 1 ≤ H) {w : ℂ}
    (hw : w.im < Real.sqrt 3 / 2) : windingNumber (fdBoundary H) 0 5 w = 0 := by
  refine windingNumber_fdBoundary_eq_zero_of_mem_convex (convex_halfSpace_im_lt _)
    ?_ (fun R ↦ ⟨-(max R 0 + 1) * Complex.I, ?_, ?_⟩) hw
  · rintro z hz ⟨t, ht, rfl⟩
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at ht
    exact absurd hz (not_lt.mpr (sqrt_three_div_two_le_im_fdBoundary hH ht))
  · have : (-(max R 0 + 1) * Complex.I).im = -(max R 0 + 1) := by simp
    rw [Set.mem_ofPred_eq, this]
    nlinarith [le_max_right R 0, Real.sqrt_nonneg 3]
  · rw [norm_mul, Complex.norm_I, mul_one, norm_neg]
    have hnorm : ‖((max R 0 : ℝ) : ℂ) + 1‖ = max R 0 + 1 := by
      rw [show ((max R 0 : ℝ) : ℂ) + 1 = ((max R 0 + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hnorm]
    linarith [le_max_left R 0]

end ModularForm

end TauCeti

end
