/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.CubeSlice
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Exact volumes of coordinate and diagonal slices

A real coordinate `k`-plane cuts the unit cube in intrinsic volume `2^k`; a complex coordinate
`k`-plane cuts the unit polydisc in real intrinsic volume `π^k`. Both normalizations give one
in dimension zero. In contrast, the line spanned by `(1,1)` cuts the square in length `2√2`.
All volumes are computed on the actual subspaces using their inherited Euclidean structures.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.Examples

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private noncomputable def coordinateEmbedding (𝕜 : Type*) [RCLike 𝕜] (f : ι ↪ κ) :
    EuclideanSpace 𝕜 ι →ₗᵢ[ℝ] EuclideanSpace 𝕜 κ where
  toLinearMap := (LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 f).toLinearMap.restrictScalars ℝ
  norm_map' := (LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 f).norm_map

private noncomputable abbrev coordinatePlane (𝕜 : Type*) [RCLike 𝕜] (f : ι ↪ κ) :
    Submodule ℝ (EuclideanSpace 𝕜 κ) := (coordinateEmbedding 𝕜 f).range

private theorem coordinateEmbedding_apply (𝕜 : Type*) [RCLike 𝕜] (f : ι ↪ κ)
    (x : EuclideanSpace 𝕜 ι) (j : κ) :
    coordinateEmbedding 𝕜 f x j = Function.extend f (WithLp.ofLp x) 0 j := by rfl

private theorem coordinatePlane_volume (𝕜 : Type*) [RCLike 𝕜] (f : ι ↪ κ) :
    volume {x : coordinatePlane 𝕜 f | ∀ j, ‖(x : EuclideanSpace 𝕜 κ) j‖ ≤ 1} =
      volume (Metric.closedBall (0 : 𝕜) 1) ^ Fintype.card ι := by
  let e := (coordinateEmbedding 𝕜 f).equivRange
  have he := LinearIsometryEquiv.measurePreserving
    (E := EuclideanSpace 𝕜 ι) (F := (coordinateEmbedding 𝕜 f).range) e
  have hpre : e ⁻¹' {x : coordinatePlane 𝕜 f |
      ∀ j, ‖(x : EuclideanSpace 𝕜 κ) j‖ ≤ 1} =
      {x : EuclideanSpace 𝕜 ι | ∀ i, ‖x i‖ ≤ 1} := by
    ext x
    constructor
    · intro h i
      simpa [e, LinearIsometry.equivRange_apply_coe, coordinateEmbedding_apply,
        f.injective.extend_apply] using h (f i)
    · intro h j
      by_cases hj : j ∈ Set.range f
      · obtain ⟨i, rfl⟩ := hj
        simpa [e, LinearIsometry.equivRange_apply_coe, coordinateEmbedding_apply,
          f.injective.extend_apply] using h i
      · simp [e, LinearIsometry.equivRange_apply_coe, coordinateEmbedding_apply,
          Function.extend_apply' _ _ _ hj]
  have hm : MeasurableSet {x : coordinatePlane 𝕜 f | ∀ j,
      ‖(x : EuclideanSpace 𝕜 κ) j‖ ≤ 1} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) measurable_const
  rw [← he.measure_preimage hm.nullMeasurableSet]
  rw [hpre]
  have hπ : MeasurePreserving (WithLp.ofLp : EuclideanSpace 𝕜 ι → (ι → 𝕜)) :=
    PiLp.volume_preserving_symm_measurableEquiv_toLp (fun _ : ι => 𝕜)
  have hset : {x : EuclideanSpace 𝕜 ι | ∀ i, ‖x i‖ ≤ 1} =
      WithLp.ofLp ⁻¹' Set.univ.pi (fun _ : ι => Metric.closedBall (0 : 𝕜) 1) := by
    ext x
    simp
  let : (i : ι) → MeasureSpace 𝕜 := fun _ => inferInstance
  rw [hset, hπ.measure_preimage (MeasurableSet.univ_pi
      (fun _ : ι => measurableSet_closedBall (x := (0 : 𝕜)) (ε := 1))).nullMeasurableSet,
    volume_pi_pi]
  simp

private theorem coordinatePlane_eq_restrictScalars (𝕜 : Type*) [RCLike 𝕜] (f : ι ↪ κ) :
    coordinatePlane 𝕜 f =
      (LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 f).range.restrictScalars ℝ := by
  ext x
  rfl

/-- A real coordinate subspace of dimension `card ι` cuts a cube of intrinsic volume `2 ^ card ι`.
The assertion includes the zero-dimensional case. -/
theorem _root_.Function.Embedding.volume_coordinate_cube (f : ι ↪ κ) :
    volume {x : (LinearIsometry.piLpExtendByZero 2 ℝ ℝ f).range |
      ∀ j, |(x : EuclideanSpace ℝ κ) j| ≤ 1} = 2 ^ Fintype.card ι := by
  let P (V : Submodule ℝ (EuclideanSpace ℝ κ)) : Prop :=
    volume {x : V | ∀ j, |(x : EuclideanSpace ℝ κ) j| ≤ 1} = 2 ^ Fintype.card ι
  have hplane : (LinearIsometry.piLpExtendByZero 2 ℝ ℝ f).range = coordinatePlane ℝ f := by
    ext x
    rfl
  change P _
  rw [hplane]
  simpa [P, Real.volume_closedBall, Real.norm_eq_abs] using coordinatePlane_volume ℝ f

/-- A complex coordinate subspace of dimension `card ι` cuts a unit polydisc of real intrinsic
volume `π ^ card ι`, including the zero-dimensional case. -/
theorem _root_.Function.Embedding.volume_coordinate_polydisc (f : ι ↪ κ) :
    volume {x : (LinearIsometry.piLpExtendByZero 2 ℂ ℂ f).range.restrictScalars ℝ |
      ∀ j, ‖(x : EuclideanSpace ℂ κ) j‖ ≤ 1} =
      ENNReal.ofReal Real.pi ^ Fintype.card ι := by
  rw [← coordinatePlane_eq_restrictScalars]
  have hπ : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  simpa [Complex.volume_closedBall, hπ] using coordinatePlane_volume ℂ f

/-- The zero-dimensional real coordinate slice has volume one. -/
example (f : Empty ↪ κ) :
    volume {x : (LinearIsometry.piLpExtendByZero 2 ℝ ℝ f).range |
      ∀ j, |(x : EuclideanSpace ℝ κ) j| ≤ 1} = 1 := by
  simpa using f.volume_coordinate_cube

/-- The zero-dimensional complex coordinate slice has real volume one. -/
example (f : Empty ↪ κ) :
    volume {x : (LinearIsometry.piLpExtendByZero 2 ℂ ℂ f).range.restrictScalars ℝ |
      ∀ j, ‖(x : EuclideanSpace ℂ κ) j‖ ≤ 1} = 1 := by
  simpa using f.volume_coordinate_polydisc

private noncomputable def diagonalUnit : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹]

private theorem norm_diagonalUnit : ‖diagonalUnit‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  norm_num [diagonalUnit, Fin.sum_univ_two, inv_pow, Real.sq_sqrt]

private noncomputable def diagonalEmbedding : ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearIsometry.toSpanSingleton ℝ _ norm_diagonalUnit

private noncomputable abbrev diagonalPlane : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) :=
  diagonalEmbedding.range

private theorem diagonalEmbedding_apply (x : ℝ) (i : Fin 2) :
    diagonalEmbedding x i = x / Real.sqrt 2 := by
  fin_cases i <;> simp [diagonalEmbedding, diagonalUnit, div_eq_mul_inv]

private theorem mem_diagonalPlane_iff (v : EuclideanSpace ℝ (Fin 2)) :
    v ∈ diagonalPlane ↔ v 0 = v 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp [diagonalEmbedding_apply]
  · intro hv
    refine ⟨v 0 * Real.sqrt 2, ?_⟩
    ext i
    fin_cases i <;>
      simp [diagonalEmbedding_apply, Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2) |>.ne', hv]

private theorem volume_diagonalPlane_cube :
    volume {x : diagonalPlane | ∀ i, |(x : EuclideanSpace ℝ (Fin 2)) i| ≤ 1} =
      ENNReal.ofReal (2 * Real.sqrt 2) := by
  let e := diagonalEmbedding.equivRange
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have he := e.measurePreserving
  have hpre : e ⁻¹' {x : diagonalPlane | ∀ i, |(x : EuclideanSpace ℝ (Fin 2)) i| ≤ 1} =
      Icc (-Real.sqrt 2) (Real.sqrt 2) := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, e, LinearIsometry.equivRange_apply_coe,
      diagonalEmbedding_apply, Fin.forall_fin_two, and_self, abs_div, abs_of_pos hs]
    rw [div_le_one hs, abs_le]
    rfl
  have hm : MeasurableSet {x : diagonalPlane | ∀ i,
      |(x : EuclideanSpace ℝ (Fin 2)) i| ≤ 1} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const
  rw [← he.measure_preimage hm.nullMeasurableSet, hpre, Real.volume_Icc]
  congr 1
  ring

private theorem diagonalPlane_eq_span : diagonalPlane =
    Submodule.span ℝ {WithLp.toLp 2 ![(1 : ℝ), 1]} := by
  ext v
  rw [mem_diagonalPlane_iff, Submodule.mem_span_singleton]
  constructor
  · intro hv
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [hv]
  · rintro ⟨a, rfl⟩
    rfl

/-- The square section by the line spanned by `(1,1)` has intrinsic length `2√2`. -/
theorem volume_diagonal_cube :
    volume {x : Submodule.span ℝ {WithLp.toLp 2 ![(1 : ℝ), 1]} |
      ∀ i, |(x : EuclideanSpace ℝ (Fin 2)) i| ≤ 1} = ENNReal.ofReal (2 * Real.sqrt 2) := by
  let P (V : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
    volume {x : V | ∀ i, |(x : EuclideanSpace ℝ (Fin 2)) i| ≤ 1} =
      ENNReal.ofReal (2 * Real.sqrt 2)
  change P _
  rw [← diagonalPlane_eq_span]
  exact volume_diagonalPlane_cube

end TauCeti.Examples
