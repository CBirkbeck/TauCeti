/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Scaling.Support
public import TauCeti.MeasureTheory.OptimalTransport.Finite.ProportionalFitting
public import TauCeti.MeasureTheory.OptimalTransport.Finite.TransportMatrix
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Exact two-by-two scaling and proportional fitting

The kernel `[1,2;3,4] / 10` scales to `[3,8;18,32] / 61`, with probability
marginals `[11,50] / 61` and `[21,40] / 61`. These examples check the numerical
scaling and the bridge to the measure-valued proportional-fitting iteration.
Since proportional fitting ends with a column update, its matrix expression is
transposed and its iteration index is shifted by one.

The triangular example checks that feasible marginals alone do not suffice when
the diagonal scaling must preserve the positive support.
-/

public section

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped BigOperators

namespace TauCeti.Examples.MatrixScaling

/-- A strictly positive probability kernel. -/
def kernel : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 10, 2 / 10; 3 / 10, 4 / 10]

/-- The independently computed scaled probability plan. -/
def plan : Matrix (Fin 2) (Fin 2) ℝ := !![3 / 61, 8 / 61; 18 / 61, 32 / 61]

/-- Positive row factors for the displayed scaling. -/
def rowFactor : Fin 2 → ℝ := ![10 / 61, 20 / 61]

/-- Positive column factors for the displayed scaling. -/
def colFactor : Fin 2 → ℝ := ![3, 4]

/-- The row probability vector. -/
def rowMass : Fin 2 → ℝ := ![11 / 61, 50 / 61]

/-- The column probability vector. -/
def colMass : Fin 2 → ℝ := ![21 / 61, 40 / 61]

/-- Every kernel entry is positive. -/
theorem kernel_pos (i j : Fin 2) : 0 < kernel i j := by
  fin_cases i <;> fin_cases j <;> norm_num [kernel]

/-- Every prescribed row mass is positive. -/
theorem rowMass_pos (i : Fin 2) : 0 < rowMass i := by
  fin_cases i <;> norm_num [rowMass]

/-- Every prescribed column mass is positive. -/
theorem colMass_pos (j : Fin 2) : 0 < colMass j := by
  fin_cases j <;> norm_num [colMass]

/-- Every row scaling factor is positive. -/
theorem rowFactor_pos (i : Fin 2) : 0 < rowFactor i := by
  fin_cases i <;> norm_num [rowFactor]

/-- Every column scaling factor is positive. -/
theorem colFactor_pos (j : Fin 2) : 0 < colFactor j := by
  fin_cases j <;> norm_num [colFactor]

/-- The displayed entries satisfy the diagonal scaling equation. -/
theorem plan_isDiagonalScaling : plan.IsDiagonalScaling kernel rowFactor colFactor := by
  rw [isDiagonalScaling_def]
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [plan, kernel, rowFactor, colFactor]

/-- The displayed plan has the prescribed probability marginals. -/
theorem plan_hasMarginals : plan.HasMarginals rowMass colMass := by
  rw [hasMarginals_def]
  constructor
  · intro i
    fin_cases i <;> norm_num [plan, rowMass, Fin.sum_univ_two]
  · intro j
    fin_cases j <;> norm_num [plan, colMass, Fin.sum_univ_two]

/-- Both marginal masses are one. -/
theorem sum_marginals : (∑ i, rowMass i) = 1 ∧ (∑ j, colMass j) = 1 := by
  norm_num [rowMass, colMass, Fin.sum_univ_two]

/-- Sinkhorn iteration from unit row factors converges to the computed plan. -/
theorem tendsto_sinkhornPlan :
    Tendsto (fun n => kernel.sinkhornPlan rowMass colMass
      ((kernel.sinkhornStep rowMass colMass)^[n] 1)) atTop (𝓝 plan) := by
  exact Matrix.tendsto_sinkhornPlan_iterate kernel_pos rowMass_pos colMass_pos
    plan_isDiagonalScaling plan_hasMarginals rowFactor_pos colFactor_pos (fun _ => one_pos)

/-- The reference probability mass function with matrix `kernel`. -/
def referencePMF : PMF (Fin 2 × Fin 2) :=
  PMF.ofFintype (fun q => ENNReal.ofReal (kernel q.1 q.2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun q _ => (kernel_pos q.1 q.2).le]
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, kernel])

/-- The first marginal probability mass function. -/
def rowPMF : PMF (Fin 2) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (rowMass i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => (rowMass_pos i).le]
    norm_num [Fin.sum_univ_two, rowMass])

/-- The second marginal probability mass function. -/
def colPMF : PMF (Fin 2) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (colMass j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => (colMass_pos j).le]
    norm_num [Fin.sum_univ_two, colMass])

/-- The displayed probability plan, bundled as a native transportation matrix. -/
def transportMatrix : TransportMatrix rowPMF colPMF :=
  TransportMatrix.ofRealFun (f := fun q => plan q.1 q.2) (by
    refine ⟨fun q => ?_, fun i => ?_, fun j => ?_⟩
    · rcases q with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> norm_num [plan]
    · change ∑ j, plan i j = (ENNReal.ofReal (rowMass i)).toReal
      rw [ENNReal.toReal_ofReal (rowMass_pos i).le]
      exact ((hasMarginals_def _ _ _).1 plan_hasMarginals).1 i
    · change ∑ i, plan i j = (ENNReal.ofReal (colMass j)).toReal
      rw [ENNReal.toReal_ofReal (colMass_pos j).le]
      exact ((hasMarginals_def _ _ _).1 plan_hasMarginals).2 j)

/-- The native probability measure is a coupling of the prescribed probability laws. -/
theorem isCoupling_transportMatrix :
    IsCoupling transportMatrix.toPMF.toMeasure rowPMF.toMeasure colPMF.toMeasure :=
  transportMatrix.isCoupling_toPMF_toMeasure

/-- Passing through transportation matrices and PMFs preserves the computed entries. -/
theorem transportMatrix_real_singleton (i j : Fin 2) :
    transportMatrix.toPMF.toMeasure.real {(i, j)} = plan i j := by
  rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [TransportMatrix.toPMF_apply, transportMatrix, TransportMatrix.ofRealFun_apply]
  apply ENNReal.toReal_ofReal
  fin_cases i <;> fin_cases j <;> norm_num [plan]

/-- The reference measure has exactly the displayed real singleton masses. -/
theorem reference_real_singleton (i j : Fin 2) :
    referencePMF.toMeasure.real {(i, j)} = kernel i j := by
  rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact ENNReal.toReal_ofReal (kernel_pos i j).le

/-- The first marginal measure has exactly the displayed singleton masses. -/
theorem row_real_singleton (i : Fin 2) : rowPMF.toMeasure.real {i} = rowMass i := by
  rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact ENNReal.toReal_ofReal (rowMass_pos i).le

/-- The second marginal measure has exactly the displayed singleton masses. -/
theorem col_real_singleton (j : Fin 2) : colPMF.toMeasure.real {j} = colMass j := by
  rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact ENNReal.toReal_ofReal (colMass_pos j).le

/-- Native measure-valued IPFP agrees with the matrix iterates, including their
transpose and one-step index shift. -/
theorem proportionalFitting_real_singleton (n : ℕ) (i j : Fin 2) :
    (referencePMF.toMeasure.proportionalFitting rowPMF.toMeasure colPMF.toMeasure
      (n + 1)).real {(i, j)} =
      (kernelᵀ.sinkhornPlan colMass rowMass
        ((kernelᵀ.sinkhornStep colMass rowMass)^[n] 1))ᵀ i j := by
  exact TauCeti.proportionalFitting_real_singleton reference_real_singleton
    row_real_singleton col_real_singleton kernel_pos rowMass_pos colMass_pos n i j

/-- Every native Schrödinger minimizer has the independently computed entries. -/
theorem schroedinger_minimizer_real_singleton {π : Measure (Fin 2 × Fin 2)}
    (hπ : IsCoupling π rowPMF.toMeasure colPMF.toMeasure)
    (hopt : InformationTheory.klDiv π referencePMF.toMeasure =
      schroedingerValue referencePMF.toMeasure rowPMF.toMeasure colPMF.toMeasure)
    (i j : Fin 2) : π.real {(i, j)} = plan i j := by
  have hscale := (isDiagonalScaling_def _ _ _ _).1 plan_isDiagonalScaling
  have hm := (hasMarginals_def _ _ _).1 plan_hasMarginals
  rw [hscale]
  exact hπ.real_singleton_eq_of_klDiv_eq_schroedingerValue reference_real_singleton
    row_real_singleton col_real_singleton rowFactor_pos colFactor_pos
    (fun i => by simpa only [← hscale] using hm.1 i)
    (fun j => by simpa only [← hscale] using hm.2 j) hopt i j

/-- An upper triangular positive support cannot be preserved by a doubly stochastic
matrix: column zero forces its first entry to be one and destroys the off-diagonal entry. -/
theorem triangular_support_obstruction : ¬ ∃ Q : Matrix (Fin 2) (Fin 2) ℝ,
    (∀ i j, 0 ≤ Q i j) ∧
    (∀ i j, Q i j = 0 ↔ (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j = 0) ∧
    Q.HasMarginals 1 1 := by
  rintro ⟨Q, _, hs, hm⟩
  rcases (hasMarginals_def Q 1 1).1 hm with ⟨hr, hc⟩
  have h10 : Q 1 0 = 0 := (hs 1 0).2 (by norm_num)
  have h00 := hc 0
  have h01 := hr 0
  simp only [Fin.sum_univ_two, Pi.one_apply] at h00 h01
  have hzero : Q 0 1 = 0 := by linarith
  have hfalse := (hs 0 1).1 hzero
  norm_num at hfalse

end TauCeti.Examples.MatrixScaling
