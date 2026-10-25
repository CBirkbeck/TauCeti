/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.KMS.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Evaluation states and circle rotation

The real translation action on `C(ℝ/ℤ, ℂ)` is point-norm continuous.
Evaluation at any point is
a positive norm-one tracial functional, hence a KMS state at inverse temperature zero under the
strip convention. Evaluation at zero is not invariant: a half-turn changes the first Fourier
character from one to minus one. Thus the KMS condition at inverse temperature zero
does not imply invariance.
-/

public section

open Complex
open scoped ComplexOrder

namespace TauCeti.Examples

/-- Rotation of the unit circle acts on continuous complex-valued functions by translation. -/
noncomputable def circleRotation : CStarAction (Multiplicative ℝ) C(UnitAddCircle, ℂ) where
  toMonoidHom :=
    { toFun := fun t => (Homeomorph.addRight (t.toAdd : UnitAddCircle)).compStarAlgEquiv' ℂ ℂ
      map_one' := by
        ext f x
        simp only [toAdd_one, QuotientAddGroup.mk_zero, Homeomorph.compStarAlgEquiv'_apply,
          ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
          Homeomorph.coe_addRight, add_zero, StarAlgEquiv.one_apply]
      map_mul' := by
        intros t s
        ext f x
        simp only [toAdd_mul, QuotientAddGroup.mk_add, Homeomorph.compStarAlgEquiv'_apply,
          ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
          Homeomorph.coe_addRight, StarAlgEquiv.mul_apply, ContinuousMap.comp_assoc, add_assoc] }
  continuous_orbit f := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact f.continuous.comp (continuous_snd.add
      (continuous_quotient_mk'.comp (continuous_toAdd.comp continuous_fst)))

end TauCeti.Examples

namespace Multiplicative

open TauCeti.Examples

/-- Rotation translates the argument of a continuous function on the circle. -/
@[simp]
theorem circleRotation_apply (t : Multiplicative ℝ) (f : C(UnitAddCircle, ℂ))
    (x : UnitAddCircle) : circleRotation t f x = f (x + (t.toAdd : UnitAddCircle)) := by rfl

end Multiplicative

namespace AddCircle

open TauCeti.Examples

/-- Evaluation at a circle point, as a positive continuous linear functional. -/
noncomputable def circleEvaluation (x : UnitAddCircle) : C(UnitAddCircle, ℂ) →P[ℂ] ℂ :=
  { ContinuousMap.evalCLM ℂ x with
    monotone' := fun _ _ h => h x }

/-- The evaluation functional has the expected pointwise value. -/
@[simp]
theorem circleEvaluation_apply (x : UnitAddCircle) (f : C(UnitAddCircle, ℂ)) :
    circleEvaluation x f = f x := by rfl

/-- Evaluation at a circle point has norm one. -/
@[simp]
theorem norm_circleEvaluation (x : UnitAddCircle) :
    ‖(circleEvaluation x : C(UnitAddCircle, ℂ) →L[ℂ] ℂ)‖ = 1 := by
  have h := ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mp
    (circleEvaluation x).monotone
  simpa only [circleEvaluation, ofReal_re, ContinuousMap.evalCLM_apply,
    ContinuousMap.one_apply, one_re] using congrArg Complex.re h

/-- Every evaluation state is a KMS state at inverse temperature zero for circle rotation. -/
theorem isKMSState_zero_circleEvaluation (x : UnitAddCircle) :
    circleRotation.IsKMSState 0 (circleEvaluation x) := by
  rw [TauCeti.CStarAction.isKMSState_zero_iff]
  exact ⟨norm_circleEvaluation x, fun a b => congrArg (circleEvaluation x) (mul_comm a b)⟩

end AddCircle

namespace TauCeti.Examples

open AddCircle Multiplicative

/-- Evaluation at zero is not invariant under rotation; a half-turn negates the first mode. -/
theorem circleEvaluation_not_invariant :
    ¬ ∀ t : Multiplicative ℝ, ∀ f : C(UnitAddCircle, ℂ),
      circleEvaluation 0 (circleRotation t f) = circleEvaluation 0 f := by
  intro h
  have hval := h (Multiplicative.ofAdd (1 / 2)) (fourier 1)
  have hhalf := fourier_add_half_inv_index (by norm_num : (1 : ℤ) ≠ 0)
    (by norm_num : (0 : ℝ) < 1) (0 : UnitAddCircle)
  simp only [circleEvaluation_apply, circleRotation_apply, zero_add, fourier_one,
    AddCircle.toCircle_zero, Circle.coe_one] at hval
  norm_num at hhalf
  have hc := hval.symm.trans hhalf
  norm_num at hc

end TauCeti.Examples
