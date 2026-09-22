/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.Basic

/-!
# Algebraic integers in the ray fundamental domain

Counting the integral ideals of a ray class goes through the points of the ray fundamental domain
that are images of algebraic integers.  This file introduces that carrier, `rayIntegerSet 𝔪`, and
the map recovering the integer a point comes from.

An element of `rayIntegerSet 𝔪` has a *unique* preimage in `𝓞 K`, because `mixedEmbedding` is
injective, and that preimage is nonzero, since the ray fundamental domain has no point of
vanishing norm (`norm_pos_of_mem_rayFundamentalDomain`).  The preimage is therefore recorded in
`(𝓞 K)⁰`, so that its nonzero-ness travels with the value.

For the trivial modulus this is Mathlib's `NumberField.mixedEmbedding.fundamentalCone.integerSet`.

## Main definitions

* `TauCeti.GlobalNumberFields.rayIntegerSet`: the points of the ray fundamental domain that are
  images of algebraic integers;
* `TauCeti.GlobalNumberFields.preimageOfMemRayIntegerSet`: the nonzero algebraic integer a point
  of `rayIntegerSet` is the image of.

## Main results

* `TauCeti.GlobalNumberFields.mem_rayIntegerSet`: the defining membership condition;
* `TauCeti.GlobalNumberFields.mixedEmbedding_preimageOfMemRayIntegerSet`: the preimage map is a
  section of `mixedEmbedding`;
* `TauCeti.GlobalNumberFields.rayIntegerSet_one`: the trivial modulus recovers Mathlib's
  `integerSet`.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone

open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The points of the ray fundamental domain of `𝔪` that are images of algebraic integers. -/
def rayIntegerSet (𝔪 : Modulus K) : Set (mixedSpace K) :=
  rayFundamentalDomain 𝔪 ∩ mixedEmbedding.integerLattice K

theorem mem_rayIntegerSet {𝔪 : Modulus K} {a : mixedSpace K} :
    a ∈ rayIntegerSet 𝔪 ↔
      a ∈ rayFundamentalDomain 𝔪 ∧ ∃ x : 𝓞 K, mixedEmbedding K x = a := by
  simp only [rayIntegerSet, Set.mem_inter_iff, SetLike.mem_coe, LinearMap.mem_range,
    AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, RingHom.coe_comp, Function.comp_apply]

/-- A point of the ray fundamental domain that is the image of an algebraic integer is the image
of exactly one, since `mixedEmbedding` is injective. -/
theorem existsUnique_preimage_of_mem_rayIntegerSet {𝔪 : Modulus K} {a : mixedSpace K}
    (ha : a ∈ rayIntegerSet 𝔪) : ∃! x : 𝓞 K, mixedEmbedding K x = a := by
  obtain ⟨_, ⟨x, rfl⟩⟩ := mem_rayIntegerSet.mp ha
  refine Function.Injective.existsUnique_of_mem_range ?_ (Set.mem_range_self x)
  exact (mixedEmbedding_injective K).comp RingOfIntegers.coe_injective

/-- A point of `rayIntegerSet` is nonzero, since the ray fundamental domain has no point of
vanishing norm. -/
theorem ne_zero_of_mem_rayIntegerSet {𝔪 : Modulus K} (a : rayIntegerSet 𝔪) :
    (a : mixedSpace K) ≠ 0 := by
  intro h
  have hpos := norm_pos_of_mem_rayFundamentalDomain (mem_rayIntegerSet.mp a.prop).1
  rw [h] at hpos
  simp at hpos

/-- The unique algebraic integer a point of `rayIntegerSet 𝔪` is the image of, recorded as an
element of the nonzero divisors `(𝓞 K)⁰`. -/
noncomputable def preimageOfMemRayIntegerSet {𝔪 : Modulus K} (a : rayIntegerSet 𝔪) : (𝓞 K)⁰ :=
  ⟨(mem_rayIntegerSet.mp a.prop).2.choose, mem_nonZeroDivisors_of_ne_zero fun h ↦
    ne_zero_of_mem_rayIntegerSet a <| by
      simpa [h] using (mem_rayIntegerSet.mp a.prop).2.choose_spec.symm⟩

@[simp]
theorem mixedEmbedding_preimageOfMemRayIntegerSet {𝔪 : Modulus K} (a : rayIntegerSet 𝔪) :
    mixedEmbedding K (preimageOfMemRayIntegerSet a : 𝓞 K) = (a : mixedSpace K) := by
  rw [preimageOfMemRayIntegerSet, (mem_rayIntegerSet.mp a.prop).2.choose_spec]

theorem preimageOfMemRayIntegerSet_mixedEmbedding {𝔪 : Modulus K} {x : 𝓞 K}
    (hx : mixedEmbedding K (x : 𝓞 K) ∈ rayIntegerSet 𝔪) :
    preimageOfMemRayIntegerSet ⟨mixedEmbedding K (x : 𝓞 K), hx⟩ = x := by
  simp_rw [RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    mixedEmbedding_preimageOfMemRayIntegerSet]

/-- **Agreement with Mathlib at the trivial modulus.**  The trivial modulus recovers
`NumberField.mixedEmbedding.fundamentalCone.integerSet`, since its ray fundamental domain is the
fundamental cone. -/
@[simp]
theorem rayIntegerSet_one : rayIntegerSet (Modulus.one K) = integerSet K := by
  rw [rayIntegerSet, rayFundamentalDomain_one, integerSet]

end TauCeti.GlobalNumberFields
