/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Complex.Basic

/-!
# The excised integrand is integrable

An `ε`-excision replaces the integrand by `0` wherever the curve comes within `ε` of one of
finitely many centres. That is what makes the integrand integrable when the unexcised one is
not: the singularities all sit at the centres, and the excision deletes a neighbourhood of each.
This file records the resulting integrability, at a fixed `ε`.

What survives the excision is `φ ∘ γ` times `deriv γ` on parameters at distance `≥ ε` from every
centre. Over a bounded interval the curve's image there is compact, so a `φ` continuous on it is
bounded; with `deriv γ` bounded the excised integrand is bounded, and it is measurable because
`deriv` always is. Bounded and measurable on a bounded interval is integrable.

## Main results

* `TauCeti.Contour.intervalIntegrable_excised_of_continuousOn`: the excised integrand is
  interval-integrable.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {φ : ℂ → ℂ} {S : Finset ℂ} {a b ε C : ℝ}

/-- The parameters surviving the `ε`-excision. -/
private def survivingParams (γ : ℝ → ℂ) (S : Finset ℂ) (ε : ℝ) : Set ℝ :=
  {t | ∀ s ∈ S, ε < ‖γ t - s‖}

private theorem measurableSet_survivingParams (hγm : Measurable γ) (S : Finset ℂ) (ε : ℝ) :
    MeasurableSet (survivingParams γ S ε) := by
  have h : survivingParams γ S ε = ⋂ s ∈ S, {t | ε < ‖γ t - s‖} := by
    ext; simp [survivingParams]
  rw [h]
  exact MeasurableSet.biInter S.countable_toSet fun s _ =>
    measurableSet_lt measurable_const ((hγm.sub_const s).norm)

/-- **The excised integrand is integrable.** Off the excision the curve stays at distance `> ε`
from every centre, so over `[a, b]` its image lies in a compact set on which `φ` is continuous,
hence bounded; with `deriv γ` bounded the excised integrand is bounded, and `deriv` is always
measurable, so the integrand is integrable.

`hφ` asks for continuity only on the *closed* condition `ε ≤ ‖z - s‖`, which is what makes the
relevant image compact; the excision itself keeps the strict `ε < ‖γ t - s‖`. -/
theorem intervalIntegrable_excised_of_continuousOn (hγc : Continuous γ) (hC : ∀ t, ‖deriv γ t‖ ≤ C)
    (hφ : ContinuousOn φ (γ '' (uIcc a b ∩ {t | ∀ s ∈ S, ε ≤ ‖γ t - s‖}))) :
    IntervalIntegrable (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else φ (γ t) * deriv γ t)
      MeasureTheory.volume a b := by
  set K : Set ℂ := γ '' (uIcc a b ∩ {t | ∀ s ∈ S, ε ≤ ‖γ t - s‖}) with hK
  have hclosed : IsClosed {t : ℝ | ∀ s ∈ S, ε ≤ ‖γ t - s‖} := by
    have h : {t : ℝ | ∀ s ∈ S, ε ≤ ‖γ t - s‖} = ⋂ s ∈ S, {t | ε ≤ ‖γ t - s‖} := by ext; simp
    rw [h]
    exact isClosed_biInter fun s _ =>
      isClosed_le continuous_const ((hγc.sub continuous_const).norm)
  have hKcompact : IsCompact K := (isCompact_uIcc.inter_right hclosed).image hγc
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn hφ
  -- The integrand is the surviving set's indicator applied to `φ ∘ γ · deriv γ`.
  set g : ℝ → ℂ := fun t => φ (γ t) * deriv γ t with hg
  have hind : (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else g t) =
      (survivingParams γ S ε).indicator g := by
    funext t
    by_cases h : ∃ s ∈ S, ‖γ t - s‖ ≤ ε
    · rw [if_pos h, Set.indicator_of_notMem]
      simpa [survivingParams, not_lt] using h
    · rw [if_neg h, Set.indicator_of_mem]
      simpa [survivingParams, not_lt] using h
  rw [hind]
  -- Membership of the surviving parameters puts the curve in `K`, where `φ` is bounded.
  have hmemK : ∀ t ∈ uIcc a b, t ∈ survivingParams γ S ε → γ t ∈ K :=
    fun t ht hs => ⟨t, ⟨ht, fun s hsS => (hs s hsS).le⟩, rfl⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC a)
  have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hbd : ∀ t ∈ uIcc a b, ‖(survivingParams γ S ε).indicator g t‖ ≤ max M 0 * C := by
    intro t ht
    by_cases hs : t ∈ survivingParams γ S ε
    · rw [Set.indicator_of_mem hs, hg, norm_mul]
      exact mul_le_mul ((hM _ (hmemK t ht hs)).trans (le_max_left _ _)) (hC t) (norm_nonneg _) hM0
    · rw [Set.indicator_of_notMem hs, norm_zero]
      exact mul_nonneg hM0 hC0
  rw [intervalIntegrable_iff]
  have hfin : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_uIoc]
        exact ENNReal.ofReal_lt_top⟩
  refine Integrable.mono' (integrable_const (max M 0 * C)) ?_
    ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr
      (Filter.Eventually.of_forall fun t ht => hbd t (Set.uIoc_subset_uIcc ht)))
  refine (aestronglyMeasurable_indicator_iff
    (measurableSet_survivingParams hγc.measurable S ε)).mpr ?_
  rw [MeasureTheory.Measure.restrict_restrict (measurableSet_survivingParams hγc.measurable S ε)]
  refine AEStronglyMeasurable.mul ?_ (measurable_deriv γ).aestronglyMeasurable
  refine ContinuousOn.aestronglyMeasurable ?_
    ((measurableSet_survivingParams hγc.measurable S ε).inter measurableSet_uIoc)
  exact hφ.comp hγc.continuousOn fun t ht =>
    ⟨t, ⟨Set.uIoc_subset_uIcc ht.2, fun s hsS => (ht.1 s hsS).le⟩, rfl⟩

end TauCeti.Contour
