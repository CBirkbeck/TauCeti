/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix
public import TauCeti.Analysis.Normed.Operator.RowCompact.CompletelyContinuous

/-!
# Input and output tails of a row-compact operator

Over a complete nontrivially normed ultrametric field, the operator on null sequences
`x ↦ (∑' j, x j) e₀` is row compact and completely continuous. Nevertheless, every finite
input-coordinate truncation has operator-norm error at least one. This distinguishes input
truncation from the output truncations in the row-compact criterion.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty TauCeti.RingOpNorm

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace ZeroAtInftyContinuousMap

/-- The summation map into the zeroth output coordinate. -/
noncomputable def summationOperator : C₀(ℕ, K) →L[K] C₀(ℕ, K) :=
  Matrix.toZeroAtInftyCLM (Matrix.of fun i _ => single (0 : ℕ) (1 : K) i)
    (fun _ => (single (0 : ℕ) (1 : K)).tendsto_cofinite)
    ⟨1, fun i _ => by
      simpa only [coe_single, Matrix.of_apply, norm_single, norm_one] using
        norm_coe_le_norm (single (0 : ℕ) (1 : K)) i⟩

/-- The summation operator sends a null sequence to its sum in the zeroth coordinate. -/
@[simp]
theorem summationOperator_apply (x : C₀(ℕ, K)) (i : ℕ) :
    summationOperator x i = if i = 0 then ∑' j, x j else 0 := by
  rw [← (summationOperator (K := K)).hasSum_mul_matrixCoeff x i |>.tsum_eq]
  by_cases hi : i = 0 <;>
    simp only [summationOperator, single_apply,
      ContinuousLinearMap.matrixCoeff_toZeroAtInftyCLM, Matrix.of_apply, hi,
      ↓reduceIte, mul_one, mul_zero, tsum_zero]

/-- The summation operator is row compact because only its zeroth output row is nonzero. -/
theorem summationOperator_isRowCompact : (summationOperator (K := K)).IsRowCompact := by
  apply ContinuousLinearMap.isRowCompact_of_norm_matrixCoeff_le
    (r := fun i => ‖single (0 : ℕ) (1 : K) i‖)
    (by simpa only [coe_single, norm_zero] using
      (single (0 : ℕ) (1 : K)).tendsto_cofinite.norm)
  intro i j
  simp only [summationOperator, single_apply, ContinuousLinearMap.matrixCoeff_apply,
    Matrix.toZeroAtInftyCLM_single_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, le_refl]

end ZeroAtInftyContinuousMap

/-- Every finite input truncation of the summation operator has error at least one. -/
theorem Finset.one_le_norm_summationOperator_sub_comp_indicator (s : Finset ℕ) :
    1 ≤ ‖summationOperator (K := K) -
      summationOperator ∘L indicatorCLM K (s : Set ℕ)‖ := by
  obtain ⟨j, hj⟩ := s.exists_notMem
  have hproj : indicatorCLM K (s : Set ℕ) (single j (1 : K)) = 0 := by
    ext k
    by_cases hk : k ∈ s
    · have hkj : k ≠ j := by rintro rfl; exact hj hk
      simp only [coe_indicatorCLM, coe_single, SetLike.mem_coe, hk, Set.indicator_of_mem,
        ne_eq, hkj, not_false_eq_true, Pi.single_eq_of_ne,
        ZeroAtInftyContinuousMap.coe_zero, Pi.zero_apply]
    · simp only [coe_indicatorCLM, coe_single, SetLike.mem_coe, hk, not_false_eq_true,
        Set.indicator_of_notMem, ZeroAtInftyContinuousMap.coe_zero, Pi.zero_apply]
  let v := single j (1 : K)
  let T := summationOperator (K := K) - summationOperator ∘L indicatorCLM K (s : Set ℕ)
  have hval : T v 0 = 1 := by
    simp only [summationOperator, coe_single, _root_.sub_apply, ContinuousLinearMap.comp_apply,
      hproj, map_zero, sub_zero, Matrix.toZeroAtInftyCLM_single_apply, Matrix.of_apply,
      Pi.single_eq_same, mul_one, T, v]
  calc
    1 = ‖T v 0‖ := by rw [hval, norm_one]
    _ ≤ ‖T v‖ := norm_coe_le_norm _ _
    _ ≤ ‖T‖ * ‖v‖ := ContinuousLinearMap.le_ringOpNorm T v
    _ = ‖T‖ := by simp only [norm_single, norm_one, mul_one, v]

namespace ZeroAtInftyContinuousMap

/-- The summation operator is completely continuous by the native row-compact criterion. -/
theorem summationOperator_isCompletelyContinuous :
    (summationOperator (K := K)).IsCompletelyContinuous :=
  ContinuousLinearMap.isRowCompact_iff_isCompletelyContinuous.mp summationOperator_isRowCompact

/-- Input-coordinate truncations fail to approximate the summation operator in norm. -/
theorem not_tendsto_norm_summationOperator_sub_comp_indicator :
    ¬ Tendsto (fun s : Finset ℕ => ‖summationOperator (K := K) -
      summationOperator ∘L indicatorCLM K (s : Set ℕ)‖) atTop (𝓝 0) := by
  intro h
  have hs := (tendsto_order.1 h).2 1 zero_lt_one
  obtain ⟨s, hs⟩ := hs.exists
  exact (s.one_le_norm_summationOperator_sub_comp_indicator).not_gt hs

end ZeroAtInftyContinuousMap
