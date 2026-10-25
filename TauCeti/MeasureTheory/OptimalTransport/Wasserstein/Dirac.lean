/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
public import TauCeti.MeasureTheory.Function.CurveAction.Geodesic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FrechetMean
public import TauCeti.MeasureTheory.Measure.FrechetMean.Selection
public import TauCeti.Probability.Distributions.Dirac

/-!
# Dirac laws in Wasserstein space

The native finite-moment law `WassersteinSpace.dirac p x` embeds the base space isometrically.
Consequently moving Dirac laws preserve geodesics and their exact action. For finite weighted
families, a Dirac law is a Wasserstein barycenter of Dirac inputs precisely when its atom is a
base-space Frechet barycenter. On the real line the quantile barycenter of Dirac laws is the
Dirac law at the weighted mean.

The barycenter comparison does not require properness or normalized weights.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The Dirac law at `x`, as a native finite-moment Wasserstein point. -/
def WassersteinSpace.dirac (p : ℝ≥0∞) (x : X) : WassersteinSpace p X :=
  WassersteinSpace.mk ⟨Measure.dirac x, inferInstance⟩ (hasFiniteMoment_dirac p x)

/-- The underlying measure of the finite-moment Dirac law is the original point mass. -/
@[simp]
theorem WassersteinSpace.coe_dirac (p : ℝ≥0∞) (x : X) :
    ((WassersteinSpace.dirac p x : ProbabilityMeasure X) : Measure X) = Measure.dirac x :=
  congrArg ProbabilityMeasure.toMeasure (WassersteinSpace.coe_mk _ _)

variable [SecondCountableTopology X] [StandardBorelSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Dirac embedding preserves the ground distance for every Wasserstein exponent
at least one. -/
theorem WassersteinSpace.isometry_dirac : Isometry (WassersteinSpace.dirac (X := X) p) := by
  intro x y
  rw [WassersteinSpace.edist_def, WassersteinSpace.coe_dirac, WassersteinSpace.coe_dirac]
  exact wassersteinEDist_dirac_dirac (ne_of_gt (zero_lt_one.trans_le Fact.out)) x y

/-- Moving a Dirac law along any base curve preserves its action, with no extra normalization. -/
theorem WassersteinSpace.curveAction_dirac (q : ℝ) (γ : ℝ → X) (a b : ℝ) :
    curveAction q (fun t => WassersteinSpace.dirac p (γ t)) a b = curveAction q γ a b :=
  WassersteinSpace.isometry_dirac.curveAction_comp q γ a b

/-- A base geodesic becomes a Wasserstein geodesic under the Dirac embedding. -/
theorem WassersteinSpace.isGeodesicSegment_dirac {γ : ℝ → X} {x y : X}
    (hγ : IsGeodesicSegment γ x y) :
    IsGeodesicSegment (fun t => WassersteinSpace.dirac p (γ t))
      (WassersteinSpace.dirac p x) (WassersteinSpace.dirac p y) :=
  hγ.comp_isometry (WassersteinSpace.isometry_dirac (X := X) (p := p))

/-- A moving Dirac mass along a unit-time base geodesic has action equal to the endpoint
distance raised to the action exponent. -/
theorem WassersteinSpace.curveAction_dirac_of_isGeodesicSegment {γ : ℝ → X} {x y : X}
    (hγ : IsGeodesicSegment γ x y) (q : ℝ) :
    curveAction q (fun t => WassersteinSpace.dirac p (γ t)) 0 1 =
      ENNReal.ofReal (dist x y) ^ q := by
  rw [WassersteinSpace.curveAction_dirac]
  exact hγ.curveAction_eq q

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

/-- The real quantile barycenter of Dirac laws is Dirac at the weighted mean of their atoms. -/
theorem quantileBarycenter_dirac (w : J → ℝ≥0) (x : J → ℝ) :
    quantileBarycenter w (fun j => Measure.dirac (x j)) =
      Measure.dirac (∑ j, (w j : ℝ) * x j) := by
  rw [quantileBarycenter_def]
  have h : (fun t => ∑ j, (w j : ℝ) * (Measure.dirac (x j)).quantile t) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] (fun _ => ∑ j, (w j : ℝ) * x j) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [Measure.quantile_dirac _ ht.1 ht.2.le]
  rw [Measure.map_congr h, Measure.map_const]
  simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter, Real.volume_Ioo, sub_zero,
    ENNReal.ofReal_one, one_smul]

end TauCeti
