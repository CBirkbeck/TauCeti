/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.RhoTelescope

/-!
# The winding number of the boundary contour at `ρ`

The generalized winding number of the truncated-fundamental-domain boundary about the
corner `ρ` is `-1/6`. The `ε`-excision of the principal value collapses to the
corner-excluded telescope ranges with asymmetric half-widths — chord-matched
`δ_L(ε) = 12/π·arcsin(ε/2)` on the arc side and linear `δ_R(ε) = ε/(H - √3/2)` on the
vertical side; both endpoint distances are then exactly `ε`, the log-norm parts cancel,
and only the corner angle defect `π/3` survives to the limit.

## Main declarations

* `TauCeti.ModularForm.hasCauchyPVAt_fdBoundary_rho` (the principal value `-πi/3`).
* `TauCeti.ModularForm.windingNumber_fdBoundary_rho` (the winding number `-1/6`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/Rho.lean`) this file ports onto
  the current Mathlib pin.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997.
-/

public section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

namespace ModularForm

variable {H ε δ t : ℝ}

/-- The sine of a sub-half-turn multiple of `π/12` factors through the absolute value. -/
private lemma abs_sin_mul_pi_div_twelve_rho {u : ℝ} (hu : |u| ≤ 6) :
    |Real.sin (u * (Real.pi / 12))| = Real.sin (|u| * (Real.pi / 12)) := by
  obtain ⟨hu₁, hu₂⟩ := abs_le.mp hu
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos]))]
  · rw [abs_of_neg h, abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])), neg_mul, Real.sin_neg]

/-- Far from the corner along the arc, the chord distance strictly exceeds the excision
chord. -/
private lemma lt_norm_fdBoundary_sub_rho_arc_of_far (harc : t ∈ Icc (1 : ℝ) 3)
    (hd : 0 < δ) (hd1 : δ < 1) (hfar : δ < |t - 3|) :
    2 * Real.sin (δ * (Real.pi / 12)) < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := by
  have habs2 : |t - 3| ≤ 2 := abs_le.mpr ⟨by linarith [harc.1], by linarith [harc.2]⟩
  rw [norm_fdBoundary_sub_rho_arc H harc,
    abs_sin_mul_pi_div_twelve_rho (habs2.trans (by norm_num))]
  have hmono : Real.sin (δ * (Real.pi / 12)) < Real.sin (|t - 3| * (Real.pi / 12)) := by
    refine Real.strictMonoOn_sin ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos, abs_nonneg (t - 3)], by nlinarith [Real.pi_pos]⟩ ?_
    exact mul_lt_mul_of_pos_right hfar (by positivity)
  linarith

/-- Near the corner along the arc, the chord distance is at most the excision chord. -/
private lemma norm_fdBoundary_sub_rho_arc_le_of_near (harc : t ∈ Icc (1 : ℝ) 3)
    (hd1 : δ < 1) (hnear : |t - 3| ≤ δ) :
    ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ ≤ 2 * Real.sin (δ * (Real.pi / 12)) := by
  have habs1 : |t - 3| ≤ 1 := hnear.trans hd1.le
  have hd0 : 0 ≤ δ := (abs_nonneg _).trans hnear
  rw [norm_fdBoundary_sub_rho_arc H harc,
    abs_sin_mul_pi_div_twelve_rho (habs1.trans (by norm_num))]
  have hmono : Real.sin (|t - 3| * (Real.pi / 12)) ≤ Real.sin (δ * (Real.pi / 12)) := by
    refine Real.strictMonoOn_sin.monotoneOn
      ⟨by nlinarith [Real.pi_pos, abs_nonneg (t - 3)], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩ ?_
    exact mul_le_mul_of_nonneg_right hnear (by positivity)
  linarith

/-- Left of the excised corner, the contour keeps distance more than `ε` from `ρ`. -/
private lemma lt_norm_of_far_left_rho (hε₁ : ε < 1) (hd : 0 < δ) (hd1 : δ < 1)
    (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε) (ht : t ∈ Ico (0 : ℝ) (3 - δ)) :
    ε < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := by
  rcases le_or_gt t 1 with ht1 | ht1
  · calc ε < 1 := hε₁
      _ ≤ ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ :=
        norm_fdBoundary_sub_rho_segment1 H ⟨ht.1, ht1⟩
  · rw [← h2sin]
    refine lt_norm_fdBoundary_sub_rho_arc_of_far ⟨ht1.le, by linarith [ht.2]⟩ hd hd1 ?_
    rw [abs_sub_comm, abs_of_pos (by linarith [ht.2] : (0 : ℝ) < 3 - t)]
    linarith [ht.2]

/-- Right of the excised corner, the contour keeps distance more than `ε` from `ρ`. -/
private lemma lt_norm_of_far_right_rho (hH : Real.sqrt 3 / 2 < H) (hεH : ε < H - Real.sqrt 3 / 2)
    (hd : 0 < δ) (hlin : δ * (H - Real.sqrt 3 / 2) = ε) (ht : t ∈ Ioc (3 + δ : ℝ) 5) :
    ε < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := by
  rcases le_or_gt t 4 with ht4 | ht4
  · rw [fdBoundary_sub_rho_of_mem_Icc_three_four H ⟨by linarith [ht.1], ht4⟩, ← hlin,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith [ht.1] : (0 : ℝ) ≤ (t - 3) * (H - Real.sqrt 3 / 2))]
    have := mul_lt_mul_of_pos_right (by linarith [ht.1] : δ < t - 3) (by linarith :
      (0 : ℝ) < H - Real.sqrt 3 / 2)
    linarith
  · calc ε < H - Real.sqrt 3 / 2 := hεH
      _ ≤ ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ :=
        norm_fdBoundary_sub_rho_segment5 (H := H) ⟨ht4.le, ht.2⟩

/-- Over the excised corner, the contour stays within distance `ε` of `ρ`. -/
private lemma norm_le_of_near_rho {δL δR : ℝ} (hH : Real.sqrt 3 / 2 < H) (hδL : 0 < δL)
    (hδL1 : δL < 1) (h2sin : 2 * Real.sin (δL * (Real.pi / 12)) = ε)
    (hδR1 : δR ≤ 1) (hlin : δR * (H - Real.sqrt 3 / 2) = ε)
    (ht : t ∈ Icc (3 - δL : ℝ) (3 + δR)) :
    ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ ≤ ε := by
  rcases le_or_gt t 3 with h3 | h3
  · rw [← h2sin]
    refine norm_fdBoundary_sub_rho_arc_le_of_near ⟨by linarith [ht.1], h3⟩ hδL1
      (abs_le.mpr ⟨by linarith [ht.1], by linarith⟩)
  · rw [fdBoundary_sub_rho_of_mem_Icc_three_four H ⟨h3.le, by linarith [ht.2]⟩,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith [h3] : (0 : ℝ) ≤ (t - 3) * (H - Real.sqrt 3 / 2)), ← hlin]
    exact mul_le_mul_of_nonneg_right (by linarith [ht.2]) (by linarith)

/-- The arc-side excision half-width `δ_L(ε) = 12/π · arcsin(ε/2)` is positive, below
`1`, and turns the chord identity into the exact excision radius `ε`. -/
private lemma delta_left_spec_rho (hε : 0 < ε) (hε₃ : ε < 2 * Real.sin (Real.pi / 12)) :
    0 < 12 / Real.pi * Real.arcsin (ε / 2) ∧ 12 / Real.pi * Real.arcsin (ε / 2) < 1 ∧
      2 * Real.sin (12 / Real.pi * Real.arcsin (ε / 2) * (Real.pi / 12)) = ε := by
  have hπ := Real.pi_pos
  have hsin1 : Real.sin (Real.pi / 12) ≤ 1 := Real.sin_le_one _
  have harc_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr (by linarith)
  have harc_lt : Real.arcsin (ε / 2) < Real.pi / 12 := by
    have h1 : Real.arcsin (ε / 2) < Real.arcsin (Real.sin (Real.pi / 12)) :=
      Real.arcsin_lt_arcsin (by linarith) (by linarith) hsin1
    rwa [Real.arcsin_sin (by linarith) (by linarith)] at h1
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_lt_one hπ]
    linarith
  · have hδπ : 12 / Real.pi * Real.arcsin (ε / 2) * (Real.pi / 12) = Real.arcsin (ε / 2) := by
      field_simp
    rw [hδπ, Real.sin_arcsin (by linarith) (by linarith)]
    ring

/-- **The excision collapse at `ρ`**: for small `ε`, the `ε`-excised index integrand of
the boundary contour about `ρ` is interval integrable, and its integral is exactly
`-πi/3 - arcsin(ε/2)·i` — the telescope value at the matched asymmetric half-widths. -/
private lemma truncated_integral_spec_rho (hH : Real.sqrt 3 / 2 < H) (hε : 0 < ε)
    (hε₁ : ε < 1) (hεH : ε < H - Real.sqrt 3 / 2)
    (hε₃ : ε < 2 * Real.sin (Real.pi / 12)) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖
        then (fdBoundary H t - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) t else 0)
      volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖
        then (fdBoundary H t - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) t else 0) =
      -((Real.pi : ℂ) / 3) * Complex.I - ((Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
  obtain ⟨hδL_pos, hδL_lt, h2sin⟩ := delta_left_spec_rho hε hε₃
  set δL := 12 / Real.pi * Real.arcsin (ε / 2) with hδL_def
  have hHpos : (0 : ℝ) < H - Real.sqrt 3 / 2 := by linarith
  set δR := ε / (H - Real.sqrt 3 / 2) with hδR_def
  have hδR_pos : 0 < δR := by rw [hδR_def]; positivity
  have hδR_le : δR ≤ 1 := by
    rw [hδR_def, div_le_one hHpos]
    linarith
  have hlin : δR * (H - Real.sqrt 3 / 2) = ε := by
    rw [hδR_def]
    exact div_mul_cancel₀ ε hHpos.ne'
  obtain ⟨hi_left, hi_right, hval⟩ :=
    ftc_logDeriv_telescope_rho H hH hδL_pos hδL_lt hδR_pos hδR_le
  have hconv : ∀ s : ℝ,
      (fdBoundary H s - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) s =
      deriv (fun r ↦ fdBoundary H r - (UpperHalfPlane.ρ : ℂ)) s /
        (fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) :=
    fun s ↦ by rw [deriv_sub_const, inv_mul_eq_div]
  have hae_left : ∀ᵐ s ∂volume, s ∈ uIoc (0 : ℝ) (3 - δL) →
      deriv (fun r ↦ fdBoundary H r - (UpperHalfPlane.ρ : ℂ)) s /
        (fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) =
        (if ε < ‖fdBoundary H s - (UpperHalfPlane.ρ : ℂ)‖
          then (fdBoundary H s - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) s
          else 0) := by
    have hb_ae : ({3 - δL} : Set ℝ)ᶜ ∈ ae volume := by
      simp [MeasureTheory.mem_ae_iff]
    filter_upwards [hb_ae] with s hs_ne hmem
    rw [uIoc_of_le (by linarith)] at hmem
    have hsIco : s ∈ Ico (0 : ℝ) (3 - δL) := ⟨hmem.1.le,
      lt_of_le_of_ne hmem.2 fun h ↦ hs_ne (mem_singleton_iff.mpr h)⟩
    rw [if_pos (lt_norm_of_far_left_rho hε₁ hδL_pos hδL_lt h2sin hsIco), hconv s]
  have hae_right : ∀ᵐ s ∂volume, s ∈ uIoc (3 + δR : ℝ) 5 →
      deriv (fun r ↦ fdBoundary H r - (UpperHalfPlane.ρ : ℂ)) s /
        (fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) =
        (if ε < ‖fdBoundary H s - (UpperHalfPlane.ρ : ℂ)‖
          then (fdBoundary H s - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) s
          else 0) := by
    refine Eventually.of_forall fun s hmem ↦ ?_
    rw [uIoc_of_le (by linarith)] at hmem
    rw [if_pos (lt_norm_of_far_right_rho hH hεH hδR_pos hlin hmem), hconv s]
  have hmid : EqOn (fun s ↦ if ε < ‖fdBoundary H s - (UpperHalfPlane.ρ : ℂ)‖
      then (fdBoundary H s - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) s else 0)
      (fun _ ↦ (0 : ℂ)) (uIcc (3 - δL : ℝ) (3 + δR)) := by
    intro s hs
    rw [uIcc_of_le (by linarith)] at hs
    exact if_neg (not_lt.mpr (norm_le_of_near_rho hH hδL_pos hδL_lt h2sin hδR_le hlin hs))
  have hi02 := hi_left.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae_left)
  have hi25 := hi_right.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae_right)
  have himid : IntervalIntegrable (fun s ↦
      if ε < ‖fdBoundary H s - (UpperHalfPlane.ρ : ℂ)‖
        then (fdBoundary H s - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) s else 0)
      volume (3 - δL) (3 + δR) := by
    refine (intervalIntegrable_const (c := (0 : ℂ))).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun s hs ↦ ?_))
    rw [uIoc_of_le (by linarith)] at hs
    have hsub : s ∈ uIcc (3 - δL : ℝ) (3 + δR) := by
      rw [uIcc_of_le (by linarith : (3 - δL : ℝ) ≤ 3 + δR)]
      exact Ioc_subset_Icc_self hs
    exact (hmid hsub).symm
  refine ⟨(hi02.trans himid).trans hi25, ?_⟩
  have hδ12 : δL * (Real.pi / 12) = Real.arcsin (ε / 2) := by
    rw [hδL_def]
    field_simp
  have hmid0 : ∫ s in (3 - δL : ℝ)..(3 + δR),
      (if ε < ‖fdBoundary H s - (UpperHalfPlane.ρ : ℂ)‖
        then (fdBoundary H s - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) s
        else 0) = 0 := by
    rw [intervalIntegral.integral_congr hmid]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi02.trans himid) hi25,
    ← intervalIntegral.integral_add_adjacent_intervals hi02 himid,
    hmid0, add_zero,
    ← intervalIntegral.integral_congr_ae hae_left,
    ← intervalIntegral.integral_congr_ae hae_right,
    hval, log_fdBoundary_three_sub_sub_rho H hδL_pos (hδL_lt.le.trans one_le_two),
    log_fdBoundary_three_add_sub_rho hH hδR_pos hδR_le, h2sin, hlin, hδ12]
  push_cast
  ring

/-- **The principal value at `ρ`**: the Cauchy principal value of the index integrand of
the boundary contour about the corner `ρ` is `-πi/3` — the corner's angle defect. -/
theorem hasCauchyPVAt_fdBoundary_rho (hH : Real.sqrt 3 / 2 < H) :
    Contour.HasCauchyPVAt (fdBoundary H) 0 5
      (fun z ↦ (z - (UpperHalfPlane.ρ : ℂ))⁻¹) (UpperHalfPlane.ρ : ℂ)
      (-((Real.pi : ℂ) / 3) * Complex.I) := by
  have hsin12 : 0 < 2 * Real.sin (Real.pi / 12) := by
    have := Real.sin_pos_of_pos_of_lt_pi (x := Real.pi / 12) (by positivity)
      (by linarith [Real.pi_pos])
    linarith
  have hε₀ : 0 < min (min (1 : ℝ) (H - Real.sqrt 3 / 2)) (2 * Real.sin (Real.pi / 12)) :=
    lt_min (lt_min (by norm_num) (by linarith)) hsin12
  have hIoo : Ioo (0 : ℝ)
      (min (min (1 : ℝ) (H - Real.sqrt 3 / 2)) (2 * Real.sin (Real.pi / 12))) ∈
      𝓝[>] (0 : ℝ) := by
    rw [← Ioi_inter_Iio]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hε₀))
  have hspec : ∀ ε ∈ Ioo (0 : ℝ)
      (min (min (1 : ℝ) (H - Real.sqrt 3 / 2)) (2 * Real.sin (Real.pi / 12))),
      IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖
          then (fdBoundary H t - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) t
          else 0)
        volume 0 5 ∧
      ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖
          then (fdBoundary H t - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) t
          else 0) =
        -((Real.pi : ℂ) / 3) * Complex.I - ((Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I :=
    fun ε hε ↦ truncated_integral_spec_rho hH hε.1
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      (hε.2.trans_le (min_le_right _ _))
  have hcont : Tendsto (fun ε : ℝ ↦ -((Real.pi : ℂ) / 3) * Complex.I -
      ((Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I) (𝓝[>] 0)
      (𝓝 (-((Real.pi : ℂ) / 3) * Complex.I)) := by
    have hc : Continuous fun ε : ℝ ↦ -((Real.pi : ℂ) / 3) * Complex.I -
        ((Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
      refine continuous_const.sub ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
      exact Real.continuous_arcsin.comp (continuous_id.div_const 2)
    simpa [Real.arcsin_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine Contour.hasCauchyPVAt_iff.mpr ⟨?_, ?_⟩
  · filter_upwards [hIoo] with ε hε
    exact (hspec ε hε).1
  · refine Tendsto.congr' ?_ hcont
    filter_upwards [hIoo] with ε hε
    exact ((hspec ε hε).2).symm

/-- **The winding number of the boundary contour at `ρ` is `-1/6`**: the corner `ρ`
sits on the contour with interior angle `2π/3`, and the principal-value normalization
sees exactly the angle defect `π/3` of a clockwise turn. -/
theorem windingNumber_fdBoundary_rho (hH : Real.sqrt 3 / 2 < H) :
    Contour.windingNumber (fdBoundary H) 0 5 (UpperHalfPlane.ρ : ℂ) = -(1 / 6 : ℂ) := by
  rw [Contour.windingNumber_eq_of_hasCauchyPVAt (hasCauchyPVAt_fdBoundary_rho hH)]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

end ModularForm

end TauCeti

end
