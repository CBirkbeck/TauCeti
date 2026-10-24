/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Nielsen
import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
public import TauCeti.GroupTheory.FreeGroup.ProperPower

/-!
# Primitive elements of free groups

An element is primitive if it occurs in a free basis. A primitive element admits an integer
character taking value one, which separates it from proper powers, the identity, and
commutators. The definition uses Mathlib's `FreeGroupBasis`, so it applies to any free group.

For a free group, primitivity is equivalent to an automorphism sending the element to a canonical
generator. Integer Nielsen transformations give primitive products with arbitrary integer powers
of a distinct basis element. The automorphism characterization uses Mathlib's
`Equiv.ofFreeGroupEquiv` to reindex a basis by the canonical generator type.
-/

public section

open scoped commutatorElement

namespace TauCeti.FreeGroup

universe u

variable {G : Type u} [Group G]

/-- An element of a free group is primitive if it belongs to some free basis. -/
def IsPrimitive (x : G) : Prop :=
  ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x

/-- A primitive element is exactly an element of some free basis. -/
theorem isPrimitive_def (x : G) :
    IsPrimitive x ↔ ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x :=
  Iff.rfl

end TauCeti.FreeGroup

namespace FreeGroupBasis

variable {G : Type u} [Group G]

/-- Every element of a free basis is primitive. -/
@[simp] theorem isPrimitive {ι : Type*} (b : FreeGroupBasis ι G) (i : ι) :
    TauCeti.FreeGroup.IsPrimitive (b i) := by
  let e : ι ≃ Set.range b := Equiv.ofInjective b b.injective
  refine ⟨Set.range b, b.reindex e, e i, ?_⟩
  simp [e]

/-- Applying a free basis to an index is the inverse of its representation map applied to
the corresponding canonical generator. -/
@[simp] theorem repr_symm_apply_of {ι : Type*} (b : FreeGroupBasis ι G) (i : ι) :
    b.repr.symm (FreeGroup.of i) = b i :=
  rfl

end FreeGroupBasis

namespace TauCeti.FreeGroup

variable {G : Type u} [Group G]

/-- The canonical generators of a free group are primitive. -/
@[simp] theorem IsPrimitive.of {α : Type u} (a : α) :
    IsPrimitive (FreeGroup.of a) := by
  simpa only [FreeGroupBasis.ofFreeGroup_apply] using
    (FreeGroupBasis.ofFreeGroup α).isPrimitive a

/-- A group isomorphism carries primitive elements to primitive elements. -/
theorem IsPrimitive.map_mulEquiv {H : Type*} [Group H]
    (e : G ≃* H) {x : G} (hx : IsPrimitive x) : IsPrimitive (e x) := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  simpa using (b.map e).isPrimitive i

/-- Primitivity is invariant under group isomorphisms. -/
@[simp] theorem isPrimitive_map_mulEquiv_iff {H : Type*} [Group H]
    (e : G ≃* H) {x : G} : IsPrimitive (e x) ↔ IsPrimitive x := by
  constructor
  · intro hx
    simpa using hx.map_mulEquiv e.symm
  · exact IsPrimitive.map_mulEquiv e

/-- An element of a free group is primitive exactly when it is the image of a canonical
generator under an automorphism. -/
theorem isPrimitive_iff_exists_mulEquiv_of {α : Type u} {x : FreeGroup α} :
    IsPrimitive x ↔
      ∃ (e : FreeGroup α ≃* FreeGroup α) (a : α), e (FreeGroup.of a) = x := by
  constructor
  · rintro ⟨ι, b, i, rfl⟩
    let c : α ≃ ι := Equiv.ofFreeGroupEquiv b.repr
    let e : FreeGroup α ≃* FreeGroup α := (FreeGroup.freeGroupCongr c).trans b.repr.symm
    refine ⟨e, c.symm i, ?_⟩
    simp [e]
  · rintro ⟨e, a, rfl⟩
    exact (IsPrimitive.of a).map_mulEquiv e

/-- Conjugation preserves and reflects primitivity. -/
@[simp] theorem isPrimitive_conj_iff (g x : G) :
    IsPrimitive (g * x * g⁻¹) ↔ IsPrimitive x :=
  isPrimitive_map_mulEquiv_iff (MulAut.conj g)

/-- The inverse of a primitive element is primitive. -/
theorem IsPrimitive.inv {x : G} (hx : IsPrimitive x) : IsPrimitive x⁻¹ := by
  have inv_of {α : Type u} (a : α) : IsPrimitive (FreeGroup.of a)⁻¹ := by
    simpa using (IsPrimitive.of a).map_mulEquiv generatorInversion
  obtain ⟨ι, b, i, rfl⟩ := hx
  simpa only [FreeGroupBasis.repr_symm_apply_of, map_inv] using
    (inv_of i).map_mulEquiv b.repr.symm

/-- An element is primitive exactly when its inverse is primitive. -/
@[simp] theorem isPrimitive_inv {x : G} : IsPrimitive x⁻¹ ↔ IsPrimitive x :=
  ⟨fun h => by simpa using h.inv, IsPrimitive.inv⟩

end TauCeti.FreeGroup

namespace FreeGroupBasis

variable {G : Type u} [Group G]

/-- A basis element times an integer power of a distinct basis element is primitive. -/
theorem isPrimitive_mul_zpow {ι : Type*} (b : FreeGroupBasis ι G) {i j : ι}
    (hij : i ≠ j) (n : ℤ) :
    TauCeti.FreeGroup.IsPrimitive (b i * b j ^ n) := by
  classical
  have h := (TauCeti.FreeGroup.IsPrimitive.of i).map_mulEquiv
    (TauCeti.FreeGroup.nielsenMul i j hij n)
  have h' := h.map_mulEquiv b.repr.symm
  simpa only [TauCeti.FreeGroup.nielsenMul_of_left, map_mul, map_zpow, repr_symm_apply_of] using h'

end FreeGroupBasis

namespace TauCeti.FreeGroup

variable {G : Type u} [Group G]

/-- A canonical generator times any integer power of a distinct generator is primitive. -/
theorem isPrimitive_of_mul_of_zpow {α : Type u} (a b : α) (hab : a ≠ b) (n : ℤ) :
    IsPrimitive (FreeGroup.of a * FreeGroup.of b ^ n) := by
  simpa only [FreeGroupBasis.ofFreeGroup_apply] using
    (FreeGroupBasis.ofFreeGroup α).isPrimitive_mul_zpow hab n

/-- A primitive element has an integer character that takes value one on it. -/
theorem IsPrimitive.exists_monoidHom_apply_eq_ofAdd_one {x : G} (hx : IsPrimitive x) :
    ∃ f : G →* Multiplicative ℤ, f x = Multiplicative.ofAdd 1 := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  classical
  let f : G →* Multiplicative ℤ :=
    b.lift (fun j : ι => if j = i then Multiplicative.ofAdd 1 else 1)
  refine ⟨f, ?_⟩
  simp [f]

/-- Primitive elements cannot be proper powers. -/
theorem IsPrimitive.not_isProperPower {x : G} (hx : IsPrimitive x) :
    ¬ Group.IsProperPower x := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  simpa only [FreeGroupBasis.repr_symm_apply_of] using
    (MulEquiv.isProperPower_map_iff b.repr.symm (x := FreeGroup.of i)).not.mpr
      (FreeGroup.not_isProperPower_of i)

/-- The identity is not primitive in a free group. -/
@[simp] theorem not_isPrimitive_one : ¬ IsPrimitive (1 : G) := by
  intro h
  exact h.not_isProperPower Group.IsProperPower.one

/-- A primitive element does not lie in the commutator subgroup. -/
theorem IsPrimitive.notMem_commutator {x : G} (hx : IsPrimitive x) :
    x ∉ commutator G := by
  obtain ⟨f, hf⟩ := hx.exists_monoidHom_apply_eq_ofAdd_one
  intro h
  have : (Multiplicative.ofAdd (1 : ℤ)) = 1 := by
    rw [← hf]
    exact (Abelianization.commutator_le_ker f) h
  norm_num at this

/-- A commutator is never primitive in a free group. -/
@[simp] theorem not_isPrimitive_commutator (x y : G) : ¬ IsPrimitive ⁅x, y⁆ := by
  intro h
  exact h.notMem_commutator
    (Subgroup.commutator_mem_commutator (show x ∈ (⊤ : Subgroup G) from trivial)
      (show y ∈ (⊤ : Subgroup G) from trivial))

/-- An integer power whose exponent is not a unit is not primitive. -/
theorem not_isPrimitive_zpow (x : G) {n : ℤ} (hn : ¬ IsUnit n) :
    ¬ IsPrimitive (x ^ n) := by
  intro hx
  exact hn (Int.isUnit_iff_natAbs_eq.mpr
    (Group.natAbs_eq_one_of_not_isProperPower_zpow hx.not_isProperPower))

/-- A natural-number power with exponent different from one is not primitive. -/
theorem not_isPrimitive_pow (x : G) {n : ℕ} (hn : n ≠ 1) : ¬ IsPrimitive (x ^ n) := by
  simpa only [zpow_natCast] using
    not_isPrimitive_zpow x (n := n) (by simpa [Int.ofNat_isUnit, Nat.isUnit_iff] using hn)

/-- The square of any group element is not primitive. -/
@[simp] theorem not_isPrimitive_sq (x : G) : ¬ IsPrimitive (x ^ 2) :=
  not_isPrimitive_pow x (by decide)

end TauCeti.FreeGroup

namespace FreeGroup

/-- A free-group element is primitive exactly when an automorphism sends it to a canonical
generator. -/
theorem isPrimitive_iff_exists_mulEquiv {α : Type u} (x : FreeGroup α) :
    TauCeti.FreeGroup.IsPrimitive x ↔
      ∃ (e : FreeGroup α ≃* FreeGroup α) (a : α), e x = of a := by
  constructor
  · rintro ⟨ι, b, i, rfl⟩
    let r : α ≃ ι := Equiv.ofFreeGroupEquiv b.repr
    let b' : FreeGroupBasis α (FreeGroup α) := b.reindex r.symm
    refine ⟨b'.repr, r.symm i, ?_⟩
    have hb : b' (r.symm i) = b i := by simp [b']
    rw [← hb]
    exact b'.repr_apply_coe _
  · rintro ⟨e, a, h⟩
    refine ⟨α, FreeGroupBasis.ofRepr e, a, ?_⟩
    apply e.injective
    exact (FreeGroupBasis.repr_apply_coe (FreeGroupBasis.ofRepr e) a).trans h.symm

end FreeGroup
