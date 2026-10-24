/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-!
# Elementary automorphisms of free groups

Inverting every generator and multiplying one generator by an integer power of another both give
automorphisms of a free group. These transformations supply bases used to construct primitive
elements.
-/

public section

namespace TauCeti.FreeGroup

universe u

/-- The automorphism that inverts every free generator. -/
noncomputable def generatorInversion {α : Type u} : FreeGroup α ≃* FreeGroup α := by
  let f : FreeGroup α →* FreeGroup α :=
    FreeGroup.lift (fun i => (FreeGroup.of i)⁻¹)
  have hf : f.comp f = MonoidHom.id (FreeGroup α) := by
    apply FreeGroup.ext_hom
    intro i
    simp [f]
  exact MonoidHom.toMulEquiv f f hf hf

/-- Generator inversion sends each generator to its inverse. -/
@[simp] theorem generatorInversion_of {α : Type u} (a : α) :
    generatorInversion (FreeGroup.of a) = (FreeGroup.of a)⁻¹ := by
  simp [generatorInversion]

/-- The inverse automorphism also inverts every generator. -/
@[simp] theorem generatorInversion_symm_of {α : Type u} (a : α) :
    generatorInversion.symm (FreeGroup.of a) = (FreeGroup.of a)⁻¹ := by
  simp [generatorInversion]

/-- Replacing one free generator by its product with an integer power of a different generator
preserves a free basis. This is the elementary Nielsen transformation. -/
noncomputable def nielsenMul {α : Type u} (a b : α) (hab : a ≠ b) (n : ℤ) :
    FreeGroup α ≃* FreeGroup α := by
  classical
  have hba : b ≠ a := Ne.symm hab
  let f : FreeGroup α →* FreeGroup α :=
    FreeGroup.lift (fun i => if i = a then FreeGroup.of a * FreeGroup.of b ^ n else FreeGroup.of i)
  let g : FreeGroup α →* FreeGroup α :=
    FreeGroup.lift (fun i =>
      if i = a then FreeGroup.of a * FreeGroup.of b ^ (-n) else FreeGroup.of i)
  have hinv : g.comp f = MonoidHom.id (FreeGroup α) ∧
      f.comp g = MonoidHom.id (FreeGroup α) := by
    constructor <;> apply FreeGroup.ext_hom <;> intro i <;> by_cases hi : i = a
    all_goals
      first
      | subst i; simp [f, g, hba, mul_assoc]
      | simp [f, g, hi]
  exact MonoidHom.toMulEquiv f g hinv.1 hinv.2

/-- The Nielsen transformation sends the selected generator to its product with the given integer
power of the other. -/
@[simp] theorem nielsenMul_of_left {α : Type u} (a b : α) (hab : a ≠ b) (n : ℤ) :
    nielsenMul a b hab n (FreeGroup.of a) = FreeGroup.of a * FreeGroup.of b ^ n := by
  classical
  simp [nielsenMul]

/-- The Nielsen transformation fixes every other generator. -/
@[simp] theorem nielsenMul_of_ne {α : Type u} (a b i : α) (hab : a ≠ b) (n : ℤ)
    (hi : i ≠ a) :
    nielsenMul a b hab n (FreeGroup.of i) = FreeGroup.of i := by
  classical
  simp [nielsenMul, hi]

/-- The inverse Nielsen transformation replaces the selected generator by its product with
the negative integer power of the other generator. -/
@[simp] theorem nielsenMul_symm_of_left {α : Type u} (a b : α) (hab : a ≠ b) (n : ℤ) :
    (nielsenMul a b hab n).symm (FreeGroup.of a) =
      FreeGroup.of a * FreeGroup.of b ^ (-n) := by
  classical
  simp [nielsenMul]

/-- The inverse Nielsen transformation fixes every other generator. -/
@[simp] theorem nielsenMul_symm_of_ne {α : Type u} (a b i : α) (hab : a ≠ b) (n : ℤ)
    (hi : i ≠ a) :
    (nielsenMul a b hab n).symm (FreeGroup.of i) = FreeGroup.of i := by
  classical
  simp [nielsenMul, hi]

end TauCeti.FreeGroup
