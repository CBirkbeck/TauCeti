/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorSquare
public import Mathlib.Algebra.Lie.TensorProduct

/-!
# Lie actions on symmetric squares

The tensor-product Lie action commutes with the flip, so it restricts to the symmetric tensors.
When two is invertible, the canonical comparison with the symmetric-power quotient transports this
action to `Sym[R]^2 M`. Its formula on pure symmetric tensors is the usual Leibniz rule.

The comparison reuses `TauCeti.symmetricTensorsEquivSymmetricPower`, including its normalization
by the inverse of two; no choice of a basis enters the action.
-/

public section

open scoped TensorProduct
open LieModule
namespace TauCeti
section
variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The flip of a tensor square commutes with its tensor-product Lie action. -/
theorem tensor_comm_lie (x : L) (z : M ⊗[R] M) :
    TensorProduct.comm R M M ⁅x, z⁆ = ⁅x, TensorProduct.comm R M M z⁆ := by
  induction z using TensorProduct.inductionOn with
  | tmul m n => simp [TensorProduct.LieModule.lie_tmul_right, add_comm]
  | add z w hz hw => simp [lie_add, hz, hw]

/-- The tensor-product Lie action preserves the symmetric tensors. -/
theorem lie_mem_symmetricTensors (x : L) {z : M ⊗[R] M}
    (hz : z ∈ symmetricTensors R M) : ⁅x, z⁆ ∈ symmetricTensors R M := by
  rw [mem_symmetricTensors] at hz ⊢
  rw [tensor_comm_lie, hz]

/-- The symmetric tensors inherit the tensor-product Lie ring action. -/
instance symmetricTensorsLieRingModule : LieRingModule L (symmetricTensors R M) where
  bracket x z := ⟨⁅x, z.val⁆, lie_mem_symmetricTensors x z.property⟩
  add_lie x y z := Subtype.ext (add_lie x y z.val)
  lie_add x z w := Subtype.ext (lie_add x z.val w.val)
  leibniz_lie x y z := Subtype.ext (leibniz_lie x y z.val)

/-- The symmetric tensors inherit the tensor-product Lie module structure. -/
instance symmetricTensorsLieModule : LieModule R L (symmetricTensors R M) where
  smul_lie r x z := Subtype.ext (smul_lie r x z.val)
  lie_smul r x z := Subtype.ext (lie_smul r x z.val)

/-- The Lie action on symmetric tensors is the restriction of the tensor action. -/
@[simp] theorem coe_lie_symmetricTensors (x : L) (z : symmetricTensors R M) :
    (⁅x, z⁆ : symmetricTensors R M).val = ⁅x, z.val⁆ := by
  unfold symmetricTensorsLieRingModule
  rfl

end
section
variable {R : Type} {L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [Invertible (2 : R)]

/-- The Lie action on the symmetric square, transported from symmetric tensors. -/
noncomputable instance symmetricPowerLieRingModule : LieRingModule L (Sym[R]^2 M) where
  bracket x z := symmetricTensorsEquivSymmetricPower R M
    ⁅x, (symmetricTensorsEquivSymmetricPower R M).symm z⁆
  add_lie x y z := by simp only [add_lie, map_add]
  lie_add x z w := by simp only [map_add, lie_add]
  leibniz_lie x y z := by
    simp only [LinearEquiv.symm_apply_apply]
    rw [leibniz_lie, map_add]

/-- The symmetric square of a Lie module is a Lie module when two is invertible. -/
noncomputable instance symmetricPowerLieModule : LieModule R L (Sym[R]^2 M) where
  smul_lie r x z := by
    -- Expose the transported bracket before applying linearity.
    change symmetricTensorsEquivSymmetricPower R M
      ⁅r • x, (symmetricTensorsEquivSymmetricPower R M).symm z⁆ =
      r • symmetricTensorsEquivSymmetricPower R M
        ⁅x, (symmetricTensorsEquivSymmetricPower R M).symm z⁆
    rw [smul_lie, map_smul]
  lie_smul r x z := by
    -- Expose the transported bracket before applying linearity.
    change symmetricTensorsEquivSymmetricPower R M
      ⁅x, (symmetricTensorsEquivSymmetricPower R M).symm (r • z)⁆ =
      r • symmetricTensorsEquivSymmetricPower R M
        ⁅x, (symmetricTensorsEquivSymmetricPower R M).symm z⁆
    rw [map_smul]
    simpa only [map_smul] using congrArg (symmetricTensorsEquivSymmetricPower R M)
      (LieModule.lie_smul (R := R) (L := L) (M := symmetricTensors R M)
        r x ((symmetricTensorsEquivSymmetricPower R M).symm z))

/-- The symmetric tensors and the symmetric square are canonically equivalent as Lie modules. -/
noncomputable def symmetricTensorsLieEquivSymmetricPower :
    symmetricTensors R M ≃ₗ⁅R, L⁆ Sym[R]^2 M where
  __ := symmetricTensorsEquivSymmetricPower R M
  map_lie' {x z} := by
    -- Expose the transported bracket before applying linearity.
    change symmetricTensorsEquivSymmetricPower R M ⁅x, z⁆ =
      symmetricTensorsEquivSymmetricPower R M
        ⁅x, (symmetricTensorsEquivSymmetricPower R M).symm
          (symmetricTensorsEquivSymmetricPower R M z)⁆
    rw [LinearEquiv.symm_apply_apply]

/-- The Lie-module comparison has the canonical symmetric-square linear equivalence. -/
@[simp]
theorem symmetricTensorsLieEquivSymmetricPower_toLinearEquiv :
    (symmetricTensorsLieEquivSymmetricPower (R := R) (L := L) (M := M)).toLinearEquiv =
      symmetricTensorsEquivSymmetricPower R M := by
  unfold symmetricTensorsLieEquivSymmetricPower
  rfl

/-- The Lie action on a pure symmetric square is the sum of the actions on its two factors. -/
theorem symmetricPower_lie_tprod_two (x : L) (m n : M) :
    ⁅x, (⨂ₛ[R] i, (![m, n] : Fin 2 → M) i)⁆ =
      (⨂ₛ[R] i, (![⁅x, m⁆, n] : Fin 2 → M) i) +
      (⨂ₛ[R] i, (![m, ⁅x, n⁆] : Fin 2 → M) i) := by
  apply (symmetricTensorsEquivSymmetricPower R M).symm.injective
  apply Subtype.ext
  -- The inverse of the transport identifies this action with the tensor action.
  change ((symmetricTensorsEquivSymmetricPower R M).symm
    (symmetricTensorsEquivSymmetricPower R M
      ⁅x, (symmetricTensorsEquivSymmetricPower R M).symm
        (⨂ₛ[R] i, (![m, n] : Fin 2 → M) i)⁆)).val = _
  rw [LinearEquiv.symm_apply_apply, coe_lie_symmetricTensors, map_add]
  simp only [Submodule.coe_add, coe_symmetricTensorsEquivSymmetricPower_symm_tprod]
  -- The inherited subtype action and the tensor action are definitionally equal.
  erw [lie_smul, lie_add]
  simp only [TensorProduct.LieModule.lie_tmul_right, smul_add]
  abel

end
end TauCeti
