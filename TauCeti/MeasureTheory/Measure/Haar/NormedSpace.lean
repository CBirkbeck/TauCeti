/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Additive Haar measures and continuous linear equivalences

A continuous linear equivalence between finite-dimensional real normed spaces is nonsingular for
any additive Haar measures chosen on its source and target: null sets correspond to null sets
under it, whatever the normalizations. This is uniqueness of additive Haar measure, in the form
`MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure`, applied to the pushforward measure,
which is again an additive Haar measure.

## Main results

* `ContinuousLinearEquiv.quasiMeasurePreserving_addHaar`: a continuous linear equivalence
  is quasi measure preserving for additive Haar measures on its source and target.
* `TauCeti.measureReal_vadd_smul`: a translate of a dilate has real measure `c ^ finrank ℝ E`
  times the original.
-/

public section

open MeasureTheory MeasureTheory.Measure

namespace TauCeti

/-- A continuous linear equivalence is nonsingular for any additive Haar measures on its source
and target. -/
theorem _root_.ContinuousLinearEquiv.quasiMeasurePreserving_addHaar {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (e : E ≃L[ℝ] F) (μ : Measure E) (ν : Measure F)
    [IsAddHaarMeasure μ] [IsAddHaarMeasure ν] : QuasiMeasurePreserving e μ ν :=
  ⟨e.continuous.measurable, absolutelyContinuous_isAddHaarMeasure (μ.map e) ν⟩

open scoped Pointwise in
/-- **A dilated translate, in real measure.** For an additive Haar measure on a finite-dimensional
real normed space, translating leaves the measure unchanged and scaling by `c ≥ 0` multiplies it
by `c ^ finrank ℝ E`. -/
theorem measureReal_vadd_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (v : E) {c : ℝ} (hc : 0 ≤ c) (s : Set E) :
    μ.real (v +ᵥ c • s) = c ^ Module.finrank ℝ E * μ.real s := by
  rw [measureReal_def, measure_vadd, addHaar_smul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (by positivity), measureReal_def]

end TauCeti

end
