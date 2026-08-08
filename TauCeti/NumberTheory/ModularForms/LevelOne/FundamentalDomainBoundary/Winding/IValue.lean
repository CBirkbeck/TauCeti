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
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.ITelescope

/-!
# The winding number of the boundary contour at `i`

The generalized winding number of the truncated-fundamental-domain boundary about the
elliptic point `i` is `-1/2`. The `ε`-excision of the principal value collapses, through
the chord identity and the monotonicity of the sine, to the `δ(ε)`-excised parameter
ranges of the logarithmic telescope, whose value `-πi - 2·arcsin(ε/2)·i` is exact; the
limit is then plain continuity of `arcsin`.

## Main declarations

* `TauCeti.ModularForm.hasCauchyPVAt_fdBoundary_I` (the principal value `-πi`).
* `TauCeti.ModularForm.windingNumber_fdBoundary_I` (the winding number `-1/2`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/I.lean`) this file ports onto
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
private lemma abs_sin_mul_pi_div_twelve {u : ℝ} (hu : |u| ≤ 1) :
    |Real.sin (u * (Real.pi / 12))| = Real.sin (|u| * (Real.pi / 12)) := by
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
      nlinarith [Real.pi_pos, abs_nonneg u]),
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]

/-- Far from the arc top, the chord distance strictly exceeds the excision chord. -/
private lemma lt_norm_fdBoundary_sub_I_arc_of_far (harc : t ∈ Icc (1 : ℝ) 3) (hd : 0 < δ)
    (hd1 : δ < 1) (hfar : δ < |t - 2|) :
    2 * Real.sin (δ * (Real.pi / 12)) < ‖fdBoundary H t - Complex.I‖ := by
  have habs1 : |t - 2| ≤ 1 := abs_le.mpr ⟨by linarith [harc.1], by linarith [harc.2]⟩
  rw [norm_fdBoundary_sub_I_arc H harc, abs_sin_mul_pi_div_twelve habs1]
  have hmono : Real.sin (δ * (Real.pi / 12)) < Real.sin (|t - 2| * (Real.pi / 12)) := by
    refine Real.strictMonoOn_sin ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos, abs_nonneg (t - 2)], by nlinarith [Real.pi_pos]⟩ ?_
    exact mul_lt_mul_of_pos_right hfar (by positivity)
  linarith

/-- Near the arc top, the chord distance is at most the excision chord. -/
private lemma norm_fdBoundary_sub_I_arc_le_of_near (harc : t ∈ Icc (1 : ℝ) 3) (hd1 : δ < 1)
    (hnear : |t - 2| ≤ δ) :
    ‖fdBoundary H t - Complex.I‖ ≤ 2 * Real.sin (δ * (Real.pi / 12)) := by
  have habs1 : |t - 2| ≤ 1 := hnear.trans hd1.le
  have hd0 : 0 ≤ δ := (abs_nonneg _).trans hnear
  rw [norm_fdBoundary_sub_I_arc H harc, abs_sin_mul_pi_div_twelve habs1]
  have hmono : Real.sin (|t - 2| * (Real.pi / 12)) ≤ Real.sin (δ * (Real.pi / 12)) := by
    refine Real.strictMonoOn_sin.monotoneOn
      ⟨by nlinarith [Real.pi_pos, abs_nonneg (t - 2)], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩ ?_
    exact mul_le_mul_of_nonneg_right hnear (by positivity)
  linarith

/-- Left of the excised arc top, the contour keeps distance more than `ε` from `i`. -/
private lemma lt_norm_of_far_left (hε₁ : ε < 1 / 2) (hd : 0 < δ) (hd1 : δ < 1)
    (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε) (ht : t ∈ Ico (0 : ℝ) (2 - δ)) :
    ε < ‖fdBoundary H t - Complex.I‖ := by
  rcases le_or_gt t 1 with ht1 | ht1
  · calc ε < 1 / 2 := hε₁
      _ ≤ ‖fdBoundary H t - Complex.I‖ := norm_fdBoundary_sub_I_segment1 H ⟨ht.1, ht1⟩
  · rw [← h2sin]
    refine lt_norm_fdBoundary_sub_I_arc_of_far ⟨ht1.le, by linarith [ht.2]⟩ hd hd1 ?_
    rw [abs_sub_comm, abs_of_pos (by linarith [ht.2] : (0 : ℝ) < 2 - t)]
    linarith [ht.2]

/-- Right of the excised arc top, the contour keeps distance more than `ε` from `i`. -/
private lemma lt_norm_of_far_right (hε₁ : ε < 1 / 2) (hε₂ : ε < H - 1)
    (hd : 0 < δ) (hd1 : δ < 1) (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε)
    (ht : t ∈ Ioc (2 + δ : ℝ) 5) :
    ε < ‖fdBoundary H t - Complex.I‖ := by
  rcases le_or_gt t 3 with ht3 | ht3
  · rw [← h2sin]
    refine lt_norm_fdBoundary_sub_I_arc_of_far ⟨by linarith [ht.1], ht3⟩ hd hd1 ?_
    rw [abs_of_pos (by linarith [ht.1] : (0 : ℝ) < t - 2)]
    linarith [ht.1]
  · rcases le_or_gt t 4 with ht4 | ht4
    · calc ε < 1 / 2 := hε₁
        _ ≤ ‖fdBoundary H t - Complex.I‖ := norm_fdBoundary_sub_I_segment4 H ⟨ht3.le, ht4⟩
    · calc ε < H - 1 := hε₂
        _ ≤ |H - 1| := le_abs_self _
        _ ≤ ‖fdBoundary H t - Complex.I‖ :=
          norm_fdBoundary_sub_I_segment5 H ⟨ht4.le, ht.2⟩

/-- Over the excised arc top, the contour stays within distance `ε` of `i`. -/
private lemma norm_le_of_near (hd1 : δ < 1)
    (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε) (ht : t ∈ Icc (2 - δ : ℝ) (2 + δ)) :
    ‖fdBoundary H t - Complex.I‖ ≤ ε := by
  rw [← h2sin]
  refine norm_fdBoundary_sub_I_arc_le_of_near
    ⟨by linarith [ht.1], by linarith [ht.2]⟩ hd1 (abs_le.mpr ⟨?_, ?_⟩)
  · linarith [ht.1]
  · linarith [ht.2]

/-- The excision half-width `δ(ε) = 12/π · arcsin(ε/2)` is positive, below `1`, and
turns the chord identity into the exact excision radius `ε`. -/
private lemma delta_spec (hε : 0 < ε) (hε₁ : ε < 1 / 2)
    (hε₃ : ε < 2 * Real.sin (Real.pi / 12)) :
    0 < 12 / Real.pi * Real.arcsin (ε / 2) ∧ 12 / Real.pi * Real.arcsin (ε / 2) < 1 ∧
      2 * Real.sin (12 / Real.pi * Real.arcsin (ε / 2) * (Real.pi / 12)) = ε := by
  have hπ := Real.pi_pos
  have harc_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr (by linarith)
  have harc_lt : Real.arcsin (ε / 2) < Real.pi / 12 := by
    have h1 : Real.arcsin (ε / 2) < Real.arcsin (Real.sin (Real.pi / 12)) :=
      Real.arcsin_lt_arcsin (by linarith) (by linarith) (Real.sin_le_one _)
    rwa [Real.arcsin_sin (by linarith) (by linarith)] at h1
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_lt_one hπ]
    linarith
  · have hδπ : 12 / Real.pi * Real.arcsin (ε / 2) * (Real.pi / 12) = Real.arcsin (ε / 2) := by
      field_simp
    rw [hδπ, Real.sin_arcsin (by linarith) (by linarith)]
    ring

/-- **The excision collapse**: for small `ε`, the `ε`-excised index integrand of the
boundary contour about `i` is interval integrable, and its integral is exactly
`-πi - 2·arcsin(ε/2)·i` — the telescope value at the matched half-width `δ(ε)`. -/
private lemma truncated_integral_spec (hH : 1 < H) (hε : 0 < ε) (hε₁ : ε < 1 / 2)
    (hε₂ : ε < H - 1) (hε₃ : ε < 2 * Real.sin (Real.pi / 12)) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - Complex.I‖
        then (fdBoundary H t - Complex.I)⁻¹ * deriv (fdBoundary H) t else 0)
      volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - Complex.I‖
        then (fdBoundary H t - Complex.I)⁻¹ * deriv (fdBoundary H) t else 0) =
      -(Real.pi : ℂ) * Complex.I - ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
  obtain ⟨hδ_pos, hδ_lt, h2sin⟩ := delta_spec hε hε₁ hε₃
  set δ := 12 / Real.pi * Real.arcsin (ε / 2) with hδ_def
  obtain ⟨hi_left, hi_right, hval⟩ := ftc_logDeriv_telescope_I H hH hδ_pos hδ_lt
  have hconv : ∀ s : ℝ, (fdBoundary H s - Complex.I)⁻¹ * deriv (fdBoundary H) s =
      deriv (fun r ↦ fdBoundary H r - Complex.I) s / (fdBoundary H s - Complex.I) :=
    fun s ↦ by rw [deriv_sub_const, inv_mul_eq_div]
  have hae_left : ∀ᵐ s ∂volume, s ∈ uIoc (0 : ℝ) (2 - δ) →
      deriv (fun r ↦ fdBoundary H r - Complex.I) s / (fdBoundary H s - Complex.I) =
        (if ε < ‖fdBoundary H s - Complex.I‖
          then (fdBoundary H s - Complex.I)⁻¹ * deriv (fdBoundary H) s else 0) := by
    have hb_ae : ({2 - δ} : Set ℝ)ᶜ ∈ ae volume := by
      simp [MeasureTheory.mem_ae_iff]
    filter_upwards [hb_ae] with s hs_ne hmem
    rw [uIoc_of_le (by linarith)] at hmem
    have hsIco : s ∈ Ico (0 : ℝ) (2 - δ) := ⟨hmem.1.le,
      lt_of_le_of_ne hmem.2 fun h ↦ hs_ne (mem_singleton_iff.mpr h)⟩
    rw [if_pos (lt_norm_of_far_left hε₁ hδ_pos hδ_lt h2sin hsIco), hconv s]
  have hae_right : ∀ᵐ s ∂volume, s ∈ uIoc (2 + δ : ℝ) 5 →
      deriv (fun r ↦ fdBoundary H r - Complex.I) s / (fdBoundary H s - Complex.I) =
        (if ε < ‖fdBoundary H s - Complex.I‖
          then (fdBoundary H s - Complex.I)⁻¹ * deriv (fdBoundary H) s else 0) := by
    refine Eventually.of_forall fun s hmem ↦ ?_
    rw [uIoc_of_le (by linarith)] at hmem
    rw [if_pos (lt_norm_of_far_right hε₁ hε₂ hδ_pos hδ_lt h2sin hmem), hconv s]
  have hmid : EqOn (fun s ↦ if ε < ‖fdBoundary H s - Complex.I‖
      then (fdBoundary H s - Complex.I)⁻¹ * deriv (fdBoundary H) s else 0)
      (fun _ ↦ (0 : ℂ)) (uIcc (2 - δ : ℝ) (2 + δ)) := by
    intro s hs
    rw [uIcc_of_le (by linarith)] at hs
    exact if_neg (not_lt.mpr (norm_le_of_near hδ_lt h2sin hs))
  have hi02 := hi_left.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae_left)
  have hi25 := hi_right.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae_right)
  have himid : IntervalIntegrable (fun s ↦ if ε < ‖fdBoundary H s - Complex.I‖
      then (fdBoundary H s - Complex.I)⁻¹ * deriv (fdBoundary H) s else 0)
      volume (2 - δ) (2 + δ) := by
    refine (intervalIntegrable_const (c := (0 : ℂ))).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun s hs ↦ ?_))
    rw [uIoc_of_le (by linarith)] at hs
    have hsub : s ∈ uIcc (2 - δ : ℝ) (2 + δ) := by
      rw [uIcc_of_le (by linarith : (2 - δ : ℝ) ≤ 2 + δ)]
      exact Ioc_subset_Icc_self hs
    exact (hmid hsub).symm
  refine ⟨(hi02.trans himid).trans hi25, ?_⟩
  have hδ6 : δ * (Real.pi / 6) = 2 * Real.arcsin (ε / 2) := by
    rw [hδ_def]
    field_simp
    ring
  have hmid0 : ∫ s in (2 - δ : ℝ)..(2 + δ), (if ε < ‖fdBoundary H s - Complex.I‖
      then (fdBoundary H s - Complex.I)⁻¹ * deriv (fdBoundary H) s else 0) = 0 := by
    rw [intervalIntegral.integral_congr hmid]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi02.trans himid) hi25,
    ← intervalIntegral.integral_add_adjacent_intervals hi02 himid,
    hmid0, add_zero,
    ← intervalIntegral.integral_congr_ae hae_left,
    ← intervalIntegral.integral_congr_ae hae_right,
    hval, log_fdBoundary_sub_I_two_sub_sub_log_fdBoundary_sub_I_two_add H hδ_pos hδ_lt.le, hδ6.symm]
  push_cast
  ring

/-- **The principal value at `i`**: the Cauchy principal value of the index integrand of
the boundary contour about the elliptic point `i` is `-πi` — half a full turn, as the
contour passes straight through `i` along the arc. -/
theorem hasCauchyPVAt_fdBoundary_I (hH : 1 < H) :
    Contour.HasCauchyPVAt (fdBoundary H) 0 5 (fun z ↦ (z - Complex.I)⁻¹) Complex.I
      (-(Real.pi : ℂ) * Complex.I) := by
  have hsin12 : 0 < 2 * Real.sin (Real.pi / 12) := by
    have := Real.sin_pos_of_pos_of_lt_pi (x := Real.pi / 12) (by positivity)
      (by linarith [Real.pi_pos])
    linarith
  have hε₀ : 0 < min (min (1 / 2) (H - 1)) (2 * Real.sin (Real.pi / 12)) :=
    lt_min (lt_min (by norm_num) (by linarith)) hsin12
  have hIoo : Ioo (0 : ℝ) (min (min (1 / 2) (H - 1)) (2 * Real.sin (Real.pi / 12))) ∈
      𝓝[>] (0 : ℝ) := by
    rw [← Ioi_inter_Iio]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hε₀))
  have hspec : ∀ ε ∈ Ioo (0 : ℝ)
      (min (min (1 / 2) (H - 1)) (2 * Real.sin (Real.pi / 12))),
      IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - Complex.I‖
          then (fdBoundary H t - Complex.I)⁻¹ * deriv (fdBoundary H) t else 0)
        volume 0 5 ∧
      ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - Complex.I‖
          then (fdBoundary H t - Complex.I)⁻¹ * deriv (fdBoundary H) t else 0) =
        -(Real.pi : ℂ) * Complex.I - ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I :=
    fun ε hε ↦ truncated_integral_spec hH hε.1
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      (hε.2.trans_le (min_le_right _ _))
  have hcont : Tendsto (fun ε : ℝ ↦ -(Real.pi : ℂ) * Complex.I -
      ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I) (𝓝[>] 0)
      (𝓝 (-(Real.pi : ℂ) * Complex.I)) := by
    have hc : Continuous fun ε : ℝ ↦ -(Real.pi : ℂ) * Complex.I -
        ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
      refine continuous_const.sub ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
      exact continuous_const.mul (Real.continuous_arcsin.comp (continuous_id.div_const 2))
    simpa [Real.arcsin_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine Contour.hasCauchyPVAt_iff.mpr ⟨?_, ?_⟩
  · filter_upwards [hIoo] with ε hε
    exact (hspec ε hε).1
  · refine Tendsto.congr' ?_ hcont
    filter_upwards [hIoo] with ε hε
    exact ((hspec ε hε).2).symm

/-- **The winding number of the boundary contour at `i` is `-1/2`**: the elliptic point
`i` sits on the contour, and the principal-value normalization sees exactly half a
clockwise turn. -/
theorem windingNumber_fdBoundary_I (hH : 1 < H) :
    Contour.windingNumber (fdBoundary H) 0 5 Complex.I = -(1 / 2 : ℂ) := by
  rw [Contour.windingNumber_eq_of_hasCauchyPVAt (hasCauchyPVAt_fdBoundary_I hH)]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end ModularForm

end TauCeti

end
