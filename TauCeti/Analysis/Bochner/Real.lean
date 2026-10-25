/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Analysis.Bochner.CharFun.Bochner
public import TauCeti.Analysis.Fourier.Pontryagin.Real
import TauCeti.Analysis.Bochner.LocallyCompactGroup

/-!
# Comparing the real and Pontryagin forms of Bochner's theorem

The real Fourier-convention Bochner measure becomes the characteristic-function measure after
rescaling frequencies by `-2π`. Its pushforward to the exponential characters is the unique
representing measure on the Pontryagin dual. Thus the two versions identify the same positive
measure with their stated conventions.

A Gaussian law of mean `m` and variance `v` gives the dual transform
`x ↦ exp(i m x - v x² / 2)`. In particular variance two represents `exp(-‖x‖²)`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable [MeasurableSpace (PontryaginDual (Multiplicative ℝ))]
  [BorelSpace (PontryaginDual (Multiplicative ℝ))]

/-- A Gaussian pushed to real exponential characters has its usual Gaussian characteristic
function as Pontryagin transform, including variance zero. -/
theorem Real.pontryaginMeasureTransform_gaussianReal (x m : ℝ) (v : ℝ≥0) :
    (FiniteMeasure.map (⟨gaussianReal m v, inferInstance⟩ : FiniteMeasure ℝ)
      Real.pontryaginCharacter).pontryaginMeasureTransform x =
      Complex.exp ((x : ℂ) * m * Complex.I - v * (x : ℂ) ^ 2 / 2) := by
  exact (FiniteMeasure.pontryaginMeasureTransform_map_realCharacter
    (⟨gaussianReal m v, inferInstance⟩ : FiniteMeasure ℝ) x).trans (charFun_gaussianReal x)

/-- The Gaussian law of variance two represents `exp(-‖x‖²)` in the Pontryagin convention. -/
example (x : ℝ) :
    (FiniteMeasure.map (⟨gaussianReal 0 2, inferInstance⟩ : FiniteMeasure ℝ)
      Real.pontryaginCharacter).pontryaginMeasureTransform x =
      Complex.exp (-(‖x‖ ^ 2 : ℝ)) := by
  calc
    _ = charFun (gaussianReal 0 2) x :=
      FiniteMeasure.pontryaginMeasureTransform_map_realCharacter _ x
    _ = _ := by
      rw [charFun_gaussianReal]
      congr 1
      simp [Real.norm_eq_abs, sq_abs]

/-- The representing measure on the real Pontryagin dual is the classical Fourier-convention
Bochner measure, first rescaled by `-2π` and then pushed to exponential characters. -/
theorem MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_eq_iff_eq_map_bochnerMeasure
    (ν : FiniteMeasure (PontryaginDual (Multiplicative ℝ)))
    {φ : ℝ → ℂ} (hφ : Continuous φ) (hpd : TauCeti.IsPositiveDefiniteSub φ) :
    ν.pontryaginMeasureTransform = φ ↔
      ν = FiniteMeasure.map
        (⟨(TauCeti.bochnerMeasure φ).map ((-2 * Real.pi) • ·), inferInstance⟩ :
          FiniteMeasure ℝ) Real.pontryaginCharacter := by
  let μ : FiniteMeasure ℝ :=
    ⟨(TauCeti.bochnerMeasure φ).map ((-2 * Real.pi) • ·), inferInstance⟩
  have hchar : charFun μ.toMeasure = φ :=
    TauCeti.charFun_map_neg_two_pi_smul_bochnerMeasure hφ hpd
  simpa only [hchar] using ν.pontryaginMeasureTransform_eq_charFun_iff μ

example (μ : FiniteMeasure ℝ) : (μ.map Real.pontryaginCharacter).toMeasure.InnerRegular := by
  rw [FiniteMeasure.toMeasure_map]
  exact Measure.InnerRegular.map_of_continuous Real.continuous_pontryaginCharacter

open TauCeti in
example (φ : ℝ → ℂ) :
    (∃! ν : FiniteMeasure (PontryaginDual (Multiplicative ℝ)),
      ν.toMeasure.InnerRegular ∧ ν.pontryaginMeasureTransform = φ) ↔
      ∃! μ : Measure ℝ, IsFiniteMeasure μ ∧ charFun μ = φ :=
  (continuous_and_isPositiveDefiniteSub_iff_existsUnique_innerRegular_pontryaginMeasureTransform_eq
    φ).symm.trans (TauCeti.bochner_charFun φ)

example : TauCeti.IsPositiveDefiniteSub (fun x : ℝ => Complex.exp (-(‖x‖ ^ 2 : ℝ))) := by
  let μ : FiniteMeasure (PontryaginDual (Multiplicative ℝ)) :=
    FiniteMeasure.map (⟨gaussianReal 0 2, inferInstance⟩ : FiniteMeasure ℝ)
      Real.pontryaginCharacter
  convert μ.isPositiveDefiniteSub_pontryaginMeasureTransform using 1
  funext x
  have h := Real.pontryaginMeasureTransform_gaussianReal x 0 2
  simpa [Real.norm_eq_abs, sq_abs, μ] using h.symm
