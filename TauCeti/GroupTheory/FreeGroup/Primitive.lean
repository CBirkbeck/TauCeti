/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.NormNum
public import TauCeti.GroupTheory.ProperPower

/-!
# Primitive elements of free groups

An element is primitive if it occurs in a free basis. A primitive element admits an integer
character taking value one, which separates it from proper powers, the identity, and
commutators. The definition uses Mathlib's `FreeGroupBasis`, so it applies to any free group.
-/

public section

open scoped commutatorElement

namespace FreeGroup

universe u

variable {G : Type u} [Group G]

/-- An element of a free group is primitive if it belongs to some free basis. -/
def IsPrimitive (x : G) : Prop :=
  ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x

/-- The canonical generators of a free group are primitive. -/
theorem isPrimitive_of {α : Type u} (a : α) :
    IsPrimitive (FreeGroup.of a) := by
  exact ⟨α, FreeGroupBasis.ofFreeGroup α, a, FreeGroupBasis.ofFreeGroup_apply a⟩

/-- A group isomorphism carries primitive elements to primitive elements. -/
theorem IsPrimitive.map_mulEquiv {H : Type u} [Group H]
    (e : G ≃* H) {x : G} (hx : IsPrimitive x) : IsPrimitive (e x) := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  exact ⟨ι, b.map e, i, FreeGroupBasis.map_apply b e i⟩

/-- Replacing one free generator by its product with a different generator preserves a free
basis. This is the elementary Nielsen transformation. -/
private noncomputable def nielsenMul {α : Type u} (a b : α) (hab : a ≠ b) :
    FreeGroup α ≃* FreeGroup α := by
  classical
  have hba : b ≠ a := Ne.symm hab
  let f : FreeGroup α →* FreeGroup α :=
    FreeGroup.lift (fun i => if i = a then FreeGroup.of a * FreeGroup.of b else FreeGroup.of i)
  let g : FreeGroup α →* FreeGroup α :=
    FreeGroup.lift (fun i => if i = a then FreeGroup.of a * (FreeGroup.of b)⁻¹ else FreeGroup.of i)
  have hgf : g.comp f = MonoidHom.id (FreeGroup α) := by
    apply FreeGroup.ext_hom
    intro i
    by_cases hi : i = a
    · subst i
      simp [f, g, hba]
    · simp [f, g, hi]
  have hfg : f.comp g = MonoidHom.id (FreeGroup α) := by
    apply FreeGroup.ext_hom
    intro i
    by_cases hi : i = a
    · subst i
      simp [f, g, hba]
    · simp [f, g, hi]
  exact MonoidHom.toMulEquiv f g hgf hfg

private theorem nielsenMul_of_left {α : Type u} (a b : α) (hab : a ≠ b) :
    nielsenMul a b hab (FreeGroup.of a) = FreeGroup.of a * FreeGroup.of b := by
  classical
  simp [nielsenMul]

/-- The product of two distinct canonical generators is primitive. -/
theorem isPrimitive_of_mul {α : Type u} (a b : α) (hab : a ≠ b) :
    IsPrimitive (FreeGroup.of a * FreeGroup.of b) := by
  classical
  have h := (isPrimitive_of a).map_mulEquiv (nielsenMul a b hab)
  simpa only [nielsenMul_of_left] using h

/-- A primitive element has an integer character that takes value one on it. -/
theorem IsPrimitive.exists_intCharacter {x : G} (hx : IsPrimitive x) :
    ∃ f : G →* Multiplicative ℤ, f x = Multiplicative.ofAdd 1 := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  classical
  let f : G →* Multiplicative ℤ :=
    (FreeGroup.lift (fun j : ι => if j = i then Multiplicative.ofAdd 1 else 1)).comp
      b.repr.toMonoidHom
  refine ⟨f, ?_⟩
  simp [f, FreeGroupBasis.repr_apply_coe]

/-- Primitive elements cannot be proper powers. -/
theorem IsPrimitive.not_isProperPower {x : G} (hx : IsPrimitive x) :
    ¬ Group.IsProperPower x := by
  obtain ⟨f, hf⟩ := hx.exists_intCharacter
  intro h
  exact Group.not_isProperPower_ofAdd_one (hf ▸ Group.IsProperPower.map f h)

/-- The identity is not primitive in a free group. -/
@[simp] theorem not_isPrimitive_one : ¬ IsPrimitive (1 : G) := by
  intro h
  exact h.not_isProperPower Group.IsProperPower.one

/-- A commutator is never primitive in a free group. -/
theorem not_isPrimitive_commutator (x y : G) : ¬ IsPrimitive ⁅x, y⁆ := by
  intro h
  obtain ⟨f, hf⟩ := h.exists_intCharacter
  have hcomm : ⁅f x, f y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have : (Multiplicative.ofAdd (1 : ℤ)) = 1 := by
    rw [← hf, map_commutatorElement, hcomm]
  norm_num at this

/-- The square of a canonical generator is not primitive. -/
@[simp] theorem not_isPrimitive_of_sq {α : Type u} (a : α) :
    ¬ IsPrimitive (FreeGroup.of a ^ 2) := by
  intro h
  exact h.not_isProperPower (Group.isProperPower_pow _ (by decide))

end FreeGroup
