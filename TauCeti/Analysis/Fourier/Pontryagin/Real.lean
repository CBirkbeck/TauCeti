/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.Analysis.Fourier.Pontryagin.Uniqueness
public import TauCeti.Topology.Algebra.PontryaginDual.Real

/-!
# Real characteristic functions as Pontryagin transforms

Pushing a finite measure on real frequencies forward to exponential characters turns its
characteristic function into the Fourier–Stieltjes transform on the Pontryagin dual.
Consequently a finite dual measure with that transform is precisely this pushforward.
-/

public section

open MeasureTheory

variable [MeasurableSpace (PontryaginDual (Multiplicative ℝ))]
  [BorelSpace (PontryaginDual (Multiplicative ℝ))]

namespace MeasureTheory.FiniteMeasure

/-- The Pontryagin transform of the real-character pushforward is the characteristic function
of the original real measure. -/
@[simp] theorem pontryaginMeasureTransform_map_realCharacter (μ : FiniteMeasure ℝ) (x : ℝ) :
    (μ.map Real.pontryaginCharacter).pontryaginMeasureTransform x = charFun μ.toMeasure x := by
  rw [pontryaginMeasureTransform_apply, toMeasure_map,
    integral_map Real.continuous_pontryaginCharacter.aemeasurable]
  · rw [charFun_apply_real]
    congr 1
    funext t
    simp [Circle.coe_exp, mul_comm]
  · exact (TauCeti.PontryaginDual.continuous_coe_eval_const
      (Multiplicative.ofAdd x)).aestronglyMeasurable

/-- A finite dual measure represents the characteristic function of a real measure exactly
when it is the pushforward of that measure to real exponential characters. -/
theorem pontryaginMeasureTransform_eq_charFun_iff
    (ν : FiniteMeasure (PontryaginDual (Multiplicative ℝ))) (μ : FiniteMeasure ℝ) :
    ν.pontryaginMeasureTransform = charFun μ.toMeasure ↔
      ν = μ.map Real.pontryaginCharacter := by
  rw [← funext (pontryaginMeasureTransform_map_realCharacter μ)]
  exact pontryaginMeasureTransform_injective.eq_iff

end MeasureTheory.FiniteMeasure
