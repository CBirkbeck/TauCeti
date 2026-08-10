/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Curve.ExcisionMeasure
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

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
  have h : survivingParams γ S ε = {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε}ᶜ := by
    ext; simp [survivingParams, not_le]
  rw [h]
  exact (measurableSet_excision hγm S ε).compl

/-- **The excised integrand is integrable.** Off the excision the curve stays at distance `> ε`
from every centre, so over `[a, b]` its values lie in a compact set on which `φ` is continuous,
hence bounded. The excised integrand is that bounded factor times `deriv γ`, so it is integrable
whenever `deriv γ` is.

`hφ` asks for continuity only on the *closed* condition `ε ≤ ‖z - s‖`, which is what makes the
relevant set compact; the excision itself keeps the strict `ε < ‖γ t - s‖`. -/
theorem intervalIntegrable_excised_of_continuousOn (hγc : ContinuousOn γ (uIcc a b))
    (hγm : Measurable γ) (hd : IntervalIntegrable (deriv γ) MeasureTheory.volume a b)
    (hφ : ContinuousOn φ (γ '' uIcc a b ∩ {z | ∀ s ∈ S, ε ≤ ‖z - s‖})) :
    IntervalIntegrable (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else φ (γ t) * deriv γ t)
      MeasureTheory.volume a b := by
  set K : Set ℂ := γ '' uIcc a b ∩ {z | ∀ s ∈ S, ε ≤ ‖z - s‖} with hK
  have hclosed : IsClosed {z : ℂ | ∀ s ∈ S, ε ≤ ‖z - s‖} := by
    have h : {z : ℂ | ∀ s ∈ S, ε ≤ ‖z - s‖} = ⋂ s ∈ S, {z : ℂ | ε ≤ ‖z - s‖} := by ext; simp
    rw [h]
    exact isClosed_biInter fun s _ =>
      isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)
  have hKcompact : IsCompact K :=
    (isCompact_uIcc.image_of_continuousOn hγc).inter_right hclosed
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn hφ
  -- The excised integrand is a bounded factor times `deriv γ`.
  have hsplit : (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else φ (γ t) * deriv γ t) =
      fun t => (survivingParams γ S ε).indicator (fun t => φ (γ t)) t * deriv γ t := by
    funext t
    by_cases h : ∃ s ∈ S, ‖γ t - s‖ ≤ ε
    · rw [if_pos h, Set.indicator_of_notMem (by simpa [survivingParams, not_lt] using h), zero_mul]
    · rw [if_neg h, Set.indicator_of_mem (by simpa [survivingParams, not_lt] using h)]
  rw [hsplit, intervalIntegrable_iff]
  refine (intervalIntegrable_iff.mp hd).bdd_mul (c := max M 0) ?_ ?_
  · refine (aestronglyMeasurable_indicator_iff
      (measurableSet_survivingParams hγm S ε)).mpr ?_
    rw [MeasureTheory.Measure.restrict_restrict (measurableSet_survivingParams hγm S ε)]
    refine ContinuousOn.aestronglyMeasurable ?_
      ((measurableSet_survivingParams hγm S ε).inter measurableSet_uIoc)
    exact hφ.comp (hγc.mono fun t ht => Set.uIoc_subset_uIcc ht.2) fun t ht =>
      ⟨⟨t, Set.uIoc_subset_uIcc ht.2, rfl⟩, fun s hs => (ht.1 s hs).le⟩
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    by_cases hs : t ∈ survivingParams γ S ε
    · rw [Set.indicator_of_mem hs]
      exact (hM _ ⟨⟨t, Set.uIoc_subset_uIcc ht, rfl⟩,
        fun s hsS => (hs s hsS).le⟩).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hs, norm_zero]
      exact le_max_right _ _

end TauCeti.Contour
