/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import TauCeti.MeasureTheory.Function.CurveAction.Geodesic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FrechetMean
import TauCeti.MeasureTheory.Measure.FrechetMean.Selection

/-!
# Dirac laws in Wasserstein space

The native finite-moment law `WassersteinSpace.dirac p x` embeds the base space isometrically.
Consequently moving Dirac laws preserve geodesics and their exact action. For finite weighted
families, a Dirac law is a Wasserstein barycenter of Dirac inputs precisely when its atom is a
base-space Frechet barycenter.

The barycenter comparison does not require properness or normalized weights.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

variable [SecondCountableTopology X] [StandardBorelSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]

example (q : ℝ) (γ : ℝ → X) (a b : ℝ) :
    curveAction q (fun t => WassersteinSpace.dirac p (γ t)) a b = curveAction q γ a b :=
  WassersteinSpace.isometry_dirac.curveAction_comp q γ a b

example {γ : ℝ → X} {x y : X} (hγ : IsGeodesicSegment γ x y) :
    IsGeodesicSegment (fun t => WassersteinSpace.dirac p (γ t))
      (WassersteinSpace.dirac p x) (WassersteinSpace.dirac p y) :=
  hγ.comp_isometry (WassersteinSpace.isometry_dirac (X := X) (p := p))

example {γ : ℝ → X} {x y : X} (hγ : IsGeodesicSegment γ x y) (q : ℝ) :
    curveAction q (fun t => WassersteinSpace.dirac p (γ t)) 0 1 =
      ENNReal.ofReal (dist x y) ^ q :=
  (WassersteinSpace.isometry_dirac.curveAction_comp q γ 0 1).trans (hγ.curveAction_eq q)

variable [CompleteSpace X] {J : Type*} [Fintype J] {w : J → ℝ≥0}

/-- A Dirac law is a Wasserstein barycenter of a finite weighted family of Dirac laws exactly
when its atom is a base-space Frechet barycenter. Weights may vanish and need not sum to one. -/
theorem WassersteinSpace.isFrechetBarycenter_dirac_iff (hp : p ≠ ∞) (x : J → X) (z : X) :
    IsFrechetBarycenter p (∑ j, w j • Measure.dirac (WassersteinSpace.dirac p (x j)))
      (WassersteinSpace.dirac p z) ↔
      IsFrechetBarycenter p (∑ j, w j • Measure.dirac (x j)) z := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hcost (ν : WassersteinSpace p X) :
      ∑ j, (w j : ℝ≥0∞) * wassersteinEDist p ((ν : ProbabilityMeasure X) : Measure X)
        (Measure.dirac (x j)) ^ p.toReal =
      ∫⁻ y, ∑ j, (w j : ℝ≥0∞) * edist y (x j) ^ p.toReal
        ∂((ν : ProbabilityMeasure X) : Measure X) := by
    rw [lintegral_finsetSum _ (fun j _ => by fun_prop)]
    apply Finset.sum_congr rfl
    intro j _
    rw [wassersteinEDist_dirac_right measurable_edist,
      eLpNorm_rpow_eq_lintegral hp0 hp (by fun_prop), lintegral_const_mul _ (by fun_prop)]
  have hbase : IsFrechetBarycenter p (∑ j, w j • Measure.dirac (x j)) z ↔
      ∀ y, ∑ j, (w j : ℝ≥0∞) * edist z (x j) ^ p.toReal ≤
        ∑ j, (w j : ℝ≥0∞) * edist y (x j) ^ p.toReal := by
    rw [isFrechetBarycenter_sum_smul_dirac_iff hp0 hp]
    exact ⟨fun h y => h.trans_le (iInf_le _ y),
      fun h => le_antisymm (le_iInf h) (iInf_le _ z)⟩
  rw [WassersteinSpace.isFrechetBarycenter_sum_smul_dirac_iff_isMinOn hp,
    isMinOn_univ_iff, hbase]
  constructor
  · intro h y
    simpa only [WassersteinSpace.coe_dirac,
      wassersteinEDist_dirac_dirac hp0] using h (WassersteinSpace.dirac p y)
  · intro h ν
    simp only [WassersteinSpace.coe_dirac,
      wassersteinEDist_dirac_dirac hp0]
    rw [hcost]
    calc
      _ = ∫⁻ _y, ∑ j, (w j : ℝ≥0∞) * edist z (x j) ^ p.toReal
          ∂((ν : ProbabilityMeasure X) : Measure X) := by
            simp only [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := lintegral_mono h

end TauCeti
