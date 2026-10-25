/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded

/-!
# Rectangular polar decompositions

Twice the first-coordinate inclusion has modulus twice the identity and polar factor equal to
the inclusion. Its adjoint is a surjective rectangular operator with a nontrivial kernel; its
modulus is twice the first-coordinate projection and its polar factor is coordinate evaluation.
The computations use the same bounded-operator modulus and polar factor over every RCLike field.
-/

public section

noncomputable section

open scoped InnerProduct
open ContinuousLinearMap

namespace TauCeti.Examples

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

private lemma modulus_two_smul {V : E →L[𝕜] F} (hV : V.IsPartialIsometry) :
    ((2 : 𝕜) • V).modulus = (2 : 𝕜) • (V† ∘L V) := by
  have hp := hV.isStarProjection_adjoint_comp_self
  apply Eq.symm
  apply eq_modulus_iff.mpr
  constructor
  · rw [two_smul]
    exact (IsPositive.of_isStarProjection hp).add (IsPositive.of_isStarProjection hp)
  · have hi : (V† ∘L V) ∘L (V† ∘L V) = V† ∘L V := hp.isIdempotentElem.eq
    simp [two_smul, add_comp, comp_add, hi]

private lemma polarFactor_two_smul {V : E →L[𝕜] F} (hV : V.IsPartialIsometry) :
    ((2 : 𝕜) • V).polarFactor = V := by
  refine (eq_polarFactor ?_ fun x hx => ?_).symm
  · rw [modulus_two_smul hV, comp_smul, hV.comp_adjoint_comp]
  · have hx' : (2 : 𝕜) • V x = 0 := hx
    exact (smul_eq_zero.mp hx').resolve_left (by norm_num)

/-- The isometric first-coordinate inclusion into a two-dimensional Hilbert space. -/
def coordinateIsometry : 𝕜 →ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin 2) :=
  LinearIsometry.toSpanSingleton 𝕜 _ (v := EuclideanSpace.single 0 1) (by simp)

private lemma coordinateIsometry_apply (x : 𝕜) :
    coordinateIsometry (𝕜 := 𝕜) x = EuclideanSpace.single 0 x := by
  ext i
  simp [coordinateIsometry, LinearIsometry.toSpanSingleton_apply, PiLp.single_apply]

/-- Twice coordinate inclusion has coordinate inclusion as its polar factor. -/
@[simp]
theorem polarFactor_two_smul_coordinateIsometry :
    ((2 : 𝕜) • (coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap).polarFactor =
    (coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap :=
  polarFactor_two_smul (coordinateIsometry (𝕜 := 𝕜)).isPartialIsometry_toContinuousLinearMap

/-- Twice coordinate evaluation has coordinate evaluation as its polar factor. -/
@[simp]
theorem polarFactor_two_smul_adjoint_coordinateIsometry :
    ((2 : 𝕜) • (coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap†).polarFactor =
    (coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap† :=
  polarFactor_two_smul
    (coordinateIsometry (𝕜 := 𝕜)).isPartialIsometry_toContinuousLinearMap.adjoint

private lemma adjoint_coordinateIsometry_apply (y : EuclideanSpace 𝕜 (Fin 2)) :
    ((coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap†) y = y 0 := by
  apply ext_inner_left 𝕜
  intro x
  rw [adjoint_inner_right]
  simp [coordinateIsometry, LinearIsometry.toSpanSingleton_apply, inner_smul_left,
    EuclideanSpace.inner_single_left, mul_comm]

/-- The modulus of twice coordinate inclusion is twice the identity. -/
@[simp]
theorem modulus_two_smul_coordinateIsometry :
    ((2 : 𝕜) • (coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap).modulus =
    (2 : 𝕜) • (1 : 𝕜 →L[𝕜] 𝕜) := by
  rw [modulus_two_smul (coordinateIsometry (𝕜 := 𝕜)).isPartialIsometry_toContinuousLinearMap,
    LinearIsometry.adjoint_comp_self]

/-- The modulus of twice coordinate evaluation is twice the coordinate projection. -/
@[simp]
theorem modulus_two_smul_adjoint_coordinateIsometry :
    ((2 : 𝕜) • (coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap†).modulus =
    (2 : 𝕜) • ((coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap ∘L
      (coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap†) := by
  rw [modulus_two_smul
    (coordinateIsometry (𝕜 := 𝕜)).isPartialIsometry_toContinuousLinearMap.adjoint,
    adjoint_adjoint]

example :
    (((2 : 𝕜) • (coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap†).polarFactor)
      (EuclideanSpace.single 1 1) = 0 := by
  rw [polarFactor_two_smul_adjoint_coordinateIsometry, adjoint_coordinateIsometry_apply]
  simp

example (x : 𝕜) :
    (((2 : 𝕜) • (coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap).polarFactor) x =
      EuclideanSpace.single 0 x := by
  rw [polarFactor_two_smul_coordinateIsometry]
  exact coordinateIsometry_apply x

example : let T := (2 : 𝕜) • (coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap
    T.polarFactor = T ∘L Ring.inverse T.modulus ∧
      Isometry (T ∘L Ring.inverse T.modulus) ∧
      (T ∘L Ring.inverse T.modulus) ∘L T.modulus = T ∧
      ∀ x, ‖(T ∘L Ring.inverse T.modulus) x‖ = ‖x‖ := by
  dsimp only
  have hunit : IsUnit ((2 : 𝕜) • (1 : 𝕜 →L[𝕜] 𝕜)) := by
    refine ⟨⟨(2 : 𝕜) • 1, (2 : 𝕜)⁻¹ • 1, ?_, ?_⟩, rfl⟩ <;> ext <;> simp
  have hpol := polarFactor_eq_comp_inverse
    (T := (2 : 𝕜) • (coordinateIsometry (𝕜 := 𝕜)).toContinuousLinearMap)
    (by rwa [modulus_two_smul_coordinateIsometry])
  rw [← hpol]
  refine ⟨rfl, ?_, polarFactor_comp_modulus _, ?_⟩
  · rw [polarFactor_two_smul_coordinateIsometry]
    exact (coordinateIsometry (𝕜 := 𝕜)).isometry
  · intro x
    rw [polarFactor_two_smul_coordinateIsometry]
    exact (coordinateIsometry (𝕜 := 𝕜)).norm_map x

variable (T : E →L[𝕜] F)

example {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) (h : A ∘L A = T† ∘L T) :
    ∃ W : E →L[𝕜] F,
      ‖W‖ ≤ 1 ∧ ‖W†‖ ≤ 1 ∧ W ∘L A = T ∧ W† ∘L T = A :=
  exists_contraction_of_gram_eq (by rwa [hA.adjoint_eq])

example : T.polarFactor.kerᗮ = T.modulus.range.topologicalClosure := by
  rw [ker_polarFactor, topologicalClosure_range_modulus]

example : T.polarFactor.IsPartialIsometry ∧ T.polarFactor ∘L T.modulus = T :=
  ⟨T.isPartialIsometry_polarFactor, T.polarFactor_comp_modulus⟩

example {x : E} (hx : x ∈ T.modulus.range.topologicalClosure) :
    ‖T.polarFactor x‖ = ‖x‖ :=
  T.norm_polarFactor_apply (T.topologicalClosure_range_modulus ▸ hx)

example {x : E} (hx : x ∈ T.modulus.rangeᗮ) : T.polarFactor x = 0 :=
  T.polarFactor_apply_of_mem_ker (T.orthogonal_range_modulus ▸ hx)

example : T.polarFactor.ker = T.modulus.rangeᗮ := by
  rw [ker_polarFactor, orthogonal_range_modulus]

example : T.polarFactor† ∘L T.polarFactor = T.kerᗮ.starProjection :=
  T.adjoint_polarFactor_comp_polarFactor

example : T.polarFactor.range = T.range.topologicalClosure ∧
    T.polarFactor ∘L T.polarFactor† = T.range.topologicalClosure.starProjection :=
  ⟨T.range_polarFactor, T.polarFactor_comp_adjoint_polarFactor⟩

example : (T†).polarFactor = T.polarFactor† := T.polarFactor_adjoint

example {V : E →L[𝕜] F} (hV : V ∘L T.modulus = T)
    (hV₀ : ∀ x ∈ T.modulus.rangeᗮ, V x = 0) : V = T.polarFactor :=
  eq_polarFactor hV (by rwa [T.orthogonal_range_modulus] at hV₀)

example : ‖T - T.polarFactor‖ ≤ ‖T.modulus - 1‖ := T.norm_sub_polarFactor_le

section RealAlgebra

attribute [local instance] realAlgebra realIsScalarTower

example : T.modulus = CFC.sqrt (T† ∘L T) := T.modulus_eq_sqrt

end RealAlgebra

example {U : E →L[𝕜] E} : U.IsPartialIsometry ↔ TauCeti.IsPartialIsometry U :=
  ContinuousLinearMap.isPartialIsometry_iff_starMul

example [FiniteDimensional 𝕜 E] {U : E →ₗ[𝕜] E} :
    U.IsPartialIsometry ↔ TauCeti.IsPartialIsometry U :=
  LinearMap.isPartialIsometry_iff_starMul

end TauCeti.Examples
