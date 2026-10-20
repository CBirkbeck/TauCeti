/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Primitive elements of free groups

An element of a group is primitive if it occurs in a free basis. The basis description
works for arbitrary groups and makes invariance under isomorphism immediate. For free
groups, we give an elementary Nielsen move and obstructions obtained by mapping a basis
element to `1` in the integers.

The basis construction follows Mathlib's `FreeGroupBasis` and the classical Nielsen
transformation replacing one generator by its product with another.
-/

public section

universe u

namespace FreeGroup

open scoped commutatorElement

/-- An element of a group is primitive if it belongs to a free basis of that group. -/
def IsPrimitive {G : Type u} [Group G] (x : G) : Prop :=
  ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x

namespace IsPrimitive

variable {G H : Type u} [Group G] [Group H]

/-- A basis member is primitive. -/
theorem of_basis {ι : Type u} (b : FreeGroupBasis ι G) (i : ι) : IsPrimitive (b i) :=
  ⟨ι, b, i, rfl⟩

/-- A group isomorphism preserves primitive elements. -/
theorem map_mulEquiv {x : G} (hx : IsPrimitive x) (e : G ≃* H) :
    IsPrimitive (e x) := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  exact ⟨ι, b.map e, i, FreeGroupBasis.map_apply b e i⟩

/-- A primitive element admits an integer-valued homomorphism taking it to `1`. -/
theorem exists_int_hom {x : G} (hx : IsPrimitive x) :
    ∃ f : G →* Multiplicative ℤ, f x = Multiplicative.ofAdd 1 := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  let f : G →* Multiplicative ℤ := b.lift (fun _ ↦ Multiplicative.ofAdd 1)
  refine ⟨f, ?_⟩
  simp [f]

/-- The identity is not a member of a free basis. -/
theorem ne_one {x : G} (hx : IsPrimitive x) : x ≠ 1 := by
  obtain ⟨f, hf⟩ := hx.exists_int_hom
  intro h
  rw [h] at hf
  rw [f.map_one] at hf
  have : (0 : ℤ) = 1 := congrArg Multiplicative.toAdd hf
  exact (by decide : (0 : ℤ) ≠ 1) this

/-- A square cannot be a member of a free basis. -/
theorem not_sq (x : G) : ¬ IsPrimitive (x ^ 2) := by
  intro h
  obtain ⟨f, hf⟩ := h.exists_int_hom
  rw [pow_two] at hf
  rw [f.map_mul] at hf
  have hz := congrArg Multiplicative.toAdd hf
  simp only [toAdd_mul, toAdd_ofAdd] at hz
  omega

/-- A commutator cannot be a member of a free basis. -/
theorem not_commutator (x y : G) : ¬ IsPrimitive ⁅x, y⁆ := by
  intro h
  obtain ⟨f, hf⟩ := h.exists_int_hom
  rw [map_commutatorElement] at hf
  have hcomm : ⁅f x, f y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rw [hcomm] at hf
  have hz := congrArg Multiplicative.toAdd hf
  exact (by decide : (0 : ℤ) ≠ 1) hz

end IsPrimitive

/-- A free generator is primitive. -/
theorem isPrimitive_of {α : Type u} (a : α) : IsPrimitive (of a) := by
  simpa using IsPrimitive.of_basis (FreeGroupBasis.ofFreeGroup α) a

/-- An element of a free group is primitive exactly when an automorphism
sends a free generator to it. -/
theorem isPrimitive_iff_exists_mulEquiv_of {α : Type u} {x : FreeGroup α} :
    IsPrimitive x ↔ ∃ (e : FreeGroup α ≃* FreeGroup α) (a : α), e (of a) = x := by
  constructor
  · rintro ⟨ι, b, i, rfl⟩
    let c : α ≃ ι := Equiv.ofFreeGroupEquiv b.repr
    let e : FreeGroup α ≃* FreeGroup α := (freeGroupCongr c).trans b.repr.symm
    refine ⟨e, c.symm i, ?_⟩
    have hb : b.repr.symm (of i) = b i := by
      apply b.repr.injective
      simp
    simpa [e] using hb
  · rintro ⟨e, a, rfl⟩
    exact (isPrimitive_of a).map_mulEquiv e

/-- Replacing one free generator by its product with a distinct generator gives
another primitive element. -/
theorem isPrimitive_of_mul {α : Type u} {a b : α} (hab : a ≠ b) :
    IsPrimitive (of a * of b) := by
  classical
  let f : α → FreeGroup α := fun x ↦ if x = a then of a * of b else of x
  let g : α → FreeGroup α := fun x ↦ if x = a then of a * (of b)⁻¹ else of x
  let φ : FreeGroup α →* FreeGroup α := lift f
  let ψ : FreeGroup α →* FreeGroup α := lift g
  have hφψ : φ.comp ψ = MonoidHom.id (FreeGroup α) := by
    ext x
    by_cases hx : x = a
    · subst x
      simp [φ, ψ, f, g, Ne.symm hab]
    · simp [φ, ψ, f, g, hx]
  have hψφ : ψ.comp φ = MonoidHom.id (FreeGroup α) := by
    ext x
    by_cases hx : x = a
    · subst x
      simp [φ, ψ, f, g, Ne.symm hab]
    · simp [φ, ψ, f, g, hx]
  let e : FreeGroup α ≃* FreeGroup α := MonoidHom.toMulEquiv φ ψ hψφ hφψ
  have h : e (of a) = of a * of b := by simp [e, φ, f]
  rw [← h]
  exact (isPrimitive_of a).map_mulEquiv e

/-- The identity of a free group is not primitive. -/
theorem not_isPrimitive_one {α : Type u} : ¬ IsPrimitive (1 : FreeGroup α) :=
  fun h ↦ h.ne_one rfl

/-- The square of a free generator is not primitive. -/
theorem not_isPrimitive_sq {α : Type u} (a : α) : ¬ IsPrimitive ((of a) ^ 2) := by
  exact IsPrimitive.not_sq (of a)

/-- A commutator in a free group is not primitive, since every homomorphism
to the integers kills it. -/
theorem not_isPrimitive_commutator {α : Type u} (a b : α) :
    ¬ IsPrimitive ⁅of a, of b⁆ :=
  IsPrimitive.not_commutator (of a) (of b)

end FreeGroup
