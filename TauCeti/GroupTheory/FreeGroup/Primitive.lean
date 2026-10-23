/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import TauCeti.GroupTheory.FreeGroup.ProperPower

/-!
# Primitive elements of free groups

An element is primitive if it occurs in a free basis. The definition applies to any group,
and the basis witness ensures that the group is free. Primitive elements cannot be proper
powers or lie in the commutator subgroup: a basis coordinate maps them to the generator
of the infinite cyclic group. Primitivity is preserved by group isomorphisms.

The Nielsen move replacing one free generator `a` by `a b ^ n` for a distinct generator
`b` and any `n : ℤ` shows that `a b ^ n`, in particular `a b`, is primitive.
-/

public section

namespace Group

universe u
open scoped commutatorElement

/-- An element of a group is primitive when it belongs to some free basis of the group. -/
def IsPrimitive {G : Type u} [Group G] (x : G) : Prop :=
  ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x

theorem isPrimitive_iff {G : Type u} [Group G] {x : G} :
    IsPrimitive x ↔ ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x := Iff.rfl

namespace IsPrimitive

/-- A primitive element is preserved by a group isomorphism. -/
theorem map_mulEquiv {G H : Type u} [Group G] [Group H] {x : G}
    (hx : IsPrimitive x) (e : G ≃* H) : IsPrimitive (e x) := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  exact ⟨ι, b.map e, i, by simp⟩

@[simp] theorem map_mulEquiv_iff {G H : Type u} [Group G] [Group H] {x : G}
    (e : G ≃* H) : IsPrimitive (e x) ↔ IsPrimitive x := by
  constructor
  · intro h
    simpa using h.map_mulEquiv e.symm
  · exact fun h => h.map_mulEquiv e

/-- A primitive element is not a proper power. -/
theorem not_isProperPower {G : Type u} [Group G] {x : G} (hx : IsPrimitive x) :
    ¬ Group.IsProperPower x := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  intro hp
  exact FreeGroup.not_isProperPower_of i (by
    simpa using Group.IsProperPower.map b.repr hp)

/-- A primitive element is nontrivial. -/
theorem ne_one {G : Type u} [Group G] {x : G} (hx : IsPrimitive x) : x ≠ 1 :=
  Group.ne_one_of_not_isProperPower hx.not_isProperPower

/-- Some homomorphism sends a primitive element to the generator
`Multiplicative.ofAdd 1` of the infinite cyclic group. -/
theorem exists_monoidHom_apply_eq_ofAdd_one {G : Type u} [Group G] {x : G}
    (hx : IsPrimitive x) :
    ∃ f : G →* Multiplicative ℤ, f x = Multiplicative.ofAdd 1 := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  obtain ⟨f, hf⟩ := FreeGroup.exists_monoidHom_apply_eq_ofAdd_one i
  refine ⟨f.comp b.repr.toMonoidHom, ?_⟩
  simpa using hf

end IsPrimitive

/-- The identity is not a primitive element. -/
@[simp] theorem not_isPrimitive_one {G : Type u} [Group G] : ¬ IsPrimitive (1 : G) := by
  intro h
  exact h.ne_one rfl

/-- A proper natural power cannot be a primitive element. -/
theorem not_isPrimitive_pow {G : Type u} [Group G] (x : G) {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsPrimitive (x ^ n) := by
  intro h
  exact h.not_isProperPower (Group.isProperPower_pow x hn)

/-- A proper integer power cannot be a primitive element. -/
theorem not_isPrimitive_zpow {G : Type u} [Group G] (x : G) {n : ℤ}
    (hn : 2 ≤ n.natAbs) : ¬ IsPrimitive (x ^ n) := by
  intro h
  exact h.not_isProperPower (Group.isProperPower_zpow x hn)

/-- A square cannot be a primitive element. -/
theorem not_isPrimitive_sq {G : Type u} [Group G] (x : G) : ¬ IsPrimitive (x ^ 2) :=
  not_isPrimitive_pow x (by omega)

/-- An element of the commutator subgroup cannot belong to a free basis. -/
theorem not_isPrimitive_of_mem_commutator {G : Type u} [Group G] {x : G}
    (hx : x ∈ commutator G) : ¬ IsPrimitive x := by
  intro h
  obtain ⟨f, hf⟩ := h.exists_monoidHom_apply_eq_ofAdd_one
  have hcomm : f x = 1 := (Abelianization.commutator_le_ker f hx)
  have hone : (Multiplicative.ofAdd (1 : ℤ)) ≠ 1 := by decide
  exact hone (hf ▸ hcomm)

/-- A commutator cannot belong to a free basis. -/
theorem not_isPrimitive_commutator {G : Type u} [Group G] (x y : G) :
    ¬ IsPrimitive ⁅x, y⁆ :=
  not_isPrimitive_of_mem_commutator
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))

end Group

namespace FreeGroupBasis

/-- Every element of a free basis is primitive. -/
@[simp]
theorem isPrimitive {G : Type u} [Group G] {ι : Type u}
    (b : FreeGroupBasis ι G) (i : ι) : Group.IsPrimitive (b i) :=
  ⟨ι, b, i, rfl⟩

end FreeGroupBasis

namespace FreeGroup

/-- Every free generator is primitive. -/
@[simp]
theorem isPrimitive_of {α : Type u} (a : α) : Group.IsPrimitive (of a) :=
  (FreeGroupBasis.ofFreeGroup α).isPrimitive a

/-- The Nielsen automorphism sending `a` to `a b ^ n` and fixing the other free generators. -/
def mulGeneratorEquiv {α : Type u} [DecidableEq α] (a b : α) (hab : a ≠ b)
    (n : ℤ) :
    FreeGroup α ≃* FreeGroup α := by
  refine MonoidHom.toMulEquiv
    (FreeGroup.lift fun c => if c = a then of a * of b ^ n else of c)
    (FreeGroup.lift fun c => if c = a then of a * of b ^ (-n) else of c) ?_ ?_
  all_goals
    apply FreeGroup.ext_hom
    intro c
    by_cases hca : c = a
    · subst c
      simp [hab.symm, mul_assoc]
    · simp [hca]

@[simp] theorem mulGeneratorEquiv_apply_of_self {α : Type u} [DecidableEq α]
    (a b : α) (hab : a ≠ b) (n : ℤ) :
    mulGeneratorEquiv a b hab n (of a) = of a * of b ^ n := by
  simp [mulGeneratorEquiv]

@[simp] theorem mulGeneratorEquiv_apply_of_ne {α : Type u} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (n : ℤ) (hca : c ≠ a) :
    mulGeneratorEquiv a b hab n (of c) = of c := by
  simp [mulGeneratorEquiv, hca]

/-- The inverse of a Nielsen move uses the opposite exponent. -/
@[simp] theorem mulGeneratorEquiv_symm {α : Type u} [DecidableEq α]
    (a b : α) (hab : a ≠ b) (n : ℤ) :
    (mulGeneratorEquiv a b hab n).symm = mulGeneratorEquiv a b hab (-n) := by
  apply MulEquiv.ext
  intro x
  induction x using FreeGroup.induction_on with
  | one => simp
  | of c =>
    by_cases hca : c = a
    · subst c
      simp [mulGeneratorEquiv, zpow_neg]
    · simp [mulGeneratorEquiv, hca]
  | inv_of c hc => simp [hc]
  | mul x y hx hy =>
    simp [hx, hy]

/-- Multiplying a free generator by an integral power of another gives a primitive element. -/
theorem isPrimitive_of_mul_zpow {α : Type u} (a b : α) (hab : a ≠ b) (n : ℤ) :
    Group.IsPrimitive (of a * of b ^ n) := by
  classical
  simpa using (isPrimitive_of a).map_mulEquiv (mulGeneratorEquiv a b hab n)

/-- The product of two distinct free generators is primitive. -/
theorem isPrimitive_of_mul_of {α : Type u} (a b : α) (hab : a ≠ b) :
    Group.IsPrimitive (of a * of b) := by
  simpa using isPrimitive_of_mul_zpow a b hab 1

end FreeGroup
