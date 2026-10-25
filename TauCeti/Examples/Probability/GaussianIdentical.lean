/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.LowDimension
public import Mathlib.Tactic.NormNum
import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Conditioning identical Gaussian coordinates

The all-ones covariance matrix represents two identical centered coordinates of
variance one. Although the joint covariance is singular, the observed scalar block is
positive definite. Its Schur complement vanishes and the native conditional law is
the Dirac measure at the observed coordinate.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Examples.GaussianIdentical

/-- The covariance of two identical unit-variance coordinates. -/
def covariance : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ := fun _ _ => 1

/-- Every entry of the covariance of two identical unit-variance coordinates is one. -/
@[simp] theorem covariance_apply (i j : Unit ⊕ Unit) : covariance i j = 1 := by
  simp only [covariance]

/-- The joint covariance is positive semidefinite. -/
theorem covariance_posSemidef : covariance.PosSemidef := by
  unfold covariance
  exact TauCeti.posSemidef_const_one

/-- Conditioning one coordinate on the other leaves zero residual covariance. -/
@[simp] theorem gaussianCondCov_eq_zero : covariance.gaussianCondCov = 0 := by
  ext i j
  simp only [Matrix.gaussianCondCov_apply_of_unique, covariance, mul_one, ne_eq, one_ne_zero,
    not_false_eq_true, div_self, sub_self, Matrix.zero_apply]

end TauCeti.Examples.GaussianIdentical

namespace EuclideanSpace

/-- The conditional mean of identical Gaussian coordinates is the observed value. -/
@[simp] theorem gaussianCondMean_eq_self_identical (x : EuclideanSpace ℝ Unit) :
    (0 : EuclideanSpace ℝ (Unit ⊕ Unit)).gaussianCondMean
      TauCeti.Examples.GaussianIdentical.covariance x = x := by
  ext i
  cases i
  have h := EuclideanSpace.gaussianCondMean_apply_of_unique_of_posSemidef
    (0 : EuclideanSpace ℝ (Unit ⊕ Unit))
    TauCeti.Examples.GaussianIdentical.covariance_posSemidef x default
    (v₁ := 1) (v₂ := 1) (ρ := 1) rfl rfl
    (by norm_num [TauCeti.Examples.GaussianIdentical.covariance])
  simpa using h

/-- The Gaussian conditional kernel for identical coordinates is the Dirac law at the
observed value. -/
theorem gaussianCondKernel_eq_dirac_identical (x : EuclideanSpace ℝ Unit) :
    (0 : EuclideanSpace ℝ (Unit ⊕ Unit)).gaussianCondKernel
      TauCeti.Examples.GaussianIdentical.covariance x = Measure.dirac x := by
  simp

end EuclideanSpace

namespace TauCeti.Examples.GaussianIdentical

/-- The native conditional distribution of identical Gaussian coordinates is Dirac
almost everywhere under the law of the observation. -/
theorem condDistrib_eq_dirac {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (X : Ω → EuclideanSpace ℝ (Unit ⊕ Unit))
    (hX : HasLaw X (multivariateGaussian 0 covariance) P) :
    ∀ᵐ x ∂P.map (fun ω => (EuclideanSpace.sumEquivProd (X ω)).2),
      condDistrib (fun ω => (EuclideanSpace.sumEquivProd (X ω)).1)
        (fun ω => (EuclideanSpace.sumEquivProd (X ω)).2) P x = Measure.dirac x := by
  have hblock : (covariance.submatrix Sum.inr Sum.inr).PosDef := by
    have heq : covariance.submatrix Sum.inr Sum.inr = (1 : Matrix Unit Unit ℝ) := by
      ext i j
      simp only [Matrix.submatrix_apply, covariance, Matrix.one_apply_eq]
    rw [heq]
    exact Matrix.PosDef.one
  filter_upwards [TauCeti.Probability.condDistrib_multivariateGaussian
    X 0 hX covariance_posSemidef hblock] with x hx
  exact hx.trans (EuclideanSpace.gaussianCondKernel_eq_dirac_identical x)

end TauCeti.Examples.GaussianIdentical
