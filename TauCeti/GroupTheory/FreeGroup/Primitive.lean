/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Abelianization.Defs

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

/-- A primitive element is exactly a member of some free basis. -/
theorem isPrimitive_def {G : Type u} [Group G] (x : G) :
    IsPrimitive x ↔ ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x := Iff.rfl

namespace IsPrimitive

variable {G H : Type u} [Group G] [Group H]

/-- A group isomorphism preserves primitive elements. -/
theorem map_mulEquiv {x : G} (hx : IsPrimitive x) (e : G ≃* H) :
    IsPrimitive (e x) := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  exact ⟨ι, b.map e, i, FreeGroupBasis.map_apply b e i⟩

/-- Primitivity is invariant under a group isomorphism. -/
@[simp] theorem map_mulEquiv_iff (e : G ≃* H) (x : G) :
    IsPrimitive (e x) ↔ IsPrimitive x := by
  constructor
  · intro h
    simpa using h.map_mulEquiv e.symm
  · exact fun h ↦ h.map_mulEquiv e

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

/-- A power with exponent other than one cannot be a member of a free basis. -/
theorem not_pow (x : G) {n : ℕ} (hn : n ≠ 1) : ¬ IsPrimitive (x ^ n) := by
  intro h
  obtain ⟨f, hf⟩ := h.exists_int_hom
  rw [map_pow] at hf
  have hz := congrArg Multiplicative.toAdd hf
  simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul] at hz
  have hd : (n : ℤ) ∣ 1 := ⟨(f x).toAdd, by simpa only [mul_comm] using hz.symm⟩
  have hn1 : n = 1 := Nat.dvd_one.mp (by exact_mod_cast hd)
  exact hn hn1

/-- An element of the commutator subgroup cannot be a member of a free basis. -/
theorem not_mem_commutator {x : G} (hx : x ∈ commutator G) : ¬ IsPrimitive x := by
  intro h
  obtain ⟨f, hf⟩ := h.exists_int_hom
  have hfx : f x = 1 := MonoidHom.mem_ker.mp (Abelianization.commutator_le_ker f hx)
  rw [hfx] at hf
  have hz := congrArg Multiplicative.toAdd hf
  exact (by decide : (0 : ℤ) ≠ 1) hz

/-- A commutator cannot be a member of a free basis. -/
theorem not_commutator (x y : G) : ¬ IsPrimitive ⁅x, y⁆ := by
  apply not_mem_commutator
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

end IsPrimitive

end FreeGroup

namespace FreeGroupBasis

/-- A basis member is primitive. -/
@[simp] theorem isPrimitive {ι G : Type u} [Group G] (b : FreeGroupBasis ι G) (i : ι) :
    FreeGroup.IsPrimitive (b i) :=
  ⟨ι, b, i, rfl⟩

end FreeGroupBasis

namespace FreeGroup

open scoped commutatorElement

/-- A free generator is primitive. -/
@[simp] theorem IsPrimitive.of {α : Type u} (a : α) : IsPrimitive (of a) := by
  simpa using (FreeGroupBasis.ofFreeGroup α).isPrimitive a

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
    exact (IsPrimitive.of a).map_mulEquiv e

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
  exact (IsPrimitive.of a).map_mulEquiv e

/-- The identity of a free group is not primitive. -/
@[simp] theorem not_isPrimitive_one {α : Type u} : ¬ IsPrimitive (1 : FreeGroup α) :=
  fun h ↦ h.ne_one rfl

/-- The square of a free generator is not primitive. -/
theorem not_isPrimitive_sq {α : Type u} (a : α) : ¬ IsPrimitive ((of a) ^ 2) := by
  exact IsPrimitive.not_pow (of a) (by decide)

/-- A commutator in a free group is not primitive, since every homomorphism
to the integers kills it. -/
theorem not_isPrimitive_commutator {α : Type u} (a b : α) :
    ¬ IsPrimitive ⁅of a, of b⁆ :=
  IsPrimitive.not_commutator (of a) (of b)

end FreeGroup

namespace FreeGroupBasis

/-- The product of two distinct members of a free basis is primitive. -/
theorem isPrimitive_mul {ι G : Type u} [Group G] (b : FreeGroupBasis ι G)
    {i j : ι} (hij : i ≠ j) : FreeGroup.IsPrimitive (b i * b j) := by
  have h := (FreeGroup.isPrimitive_of_mul hij).map_mulEquiv b.repr.symm
  change FreeGroup.IsPrimitive
    (b.repr.symm (FreeGroup.of i) * b.repr.symm (FreeGroup.of j))
  simpa only [map_mul] using h

end FreeGroupBasis
