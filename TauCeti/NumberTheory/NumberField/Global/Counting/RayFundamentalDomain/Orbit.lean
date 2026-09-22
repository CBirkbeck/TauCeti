/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.IntegerSet

/-!
# Orbits of the congruence roots of unity on the ray integer set

Two points of `rayIntegerSet 𝔪` lie in the same orbit of the congruence roots of unity exactly
when some unit congruent to one modulo `𝔪` carries one to the other.  So orbits of the *small*
group `unitsCongruenceTorsion 𝔪` on the domain are the traces of the *large* group
`unitsCongruenceSubgroup 𝔪` acting on the whole space: the large group identifies no two points
of the domain that the small group does not already identify.  Together with
`exists_unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain`, which moves each point of
nonzero norm in `posRegion 𝔪` into the domain, that is the sense in which the domain is
fundamental for the large group modulo the small one.

For the trivial modulus the large group is all of `(𝓞 K)ˣ`, translation by it is associatedness
in `(𝓞 K)⁰`, and the statement is Mathlib's `integerSetToAssociates_eq_iff`, whose left-hand side
reads the orbit off in `Associates (𝓞 K)⁰`.  Mathlib has no such quotient type for a proper
subgroup of the units, so this file states the orbit relation directly.

## Main results

* `TauCeti.GlobalNumberFields.exists_unitsCongruenceTorsion_smul_iff`: the orbit relation, as a
  congruence-unit translation.
-/

public section

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone

open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The orbit relation.**  Two points of `rayIntegerSet 𝔪` lie in one orbit of the congruence
roots of unity exactly when some unit congruent to one modulo `𝔪` carries one to the other in
the mixed space.  Since `mixedEmbedding` is injective and multiplicative, that is the same as
their algebraic integers differing by such a unit.

The content is the reverse direction: the right-hand side constrains the unit only by a
congruence, and it is membership of both points in the ray fundamental domain that upgrades it
to a root of unity. -/
theorem exists_unitsCongruenceTorsion_smul_iff {𝔪 : Modulus K} (a b : rayIntegerSet 𝔪) :
    (∃ ζ : unitsCongruenceTorsion 𝔪, ζ • a = b) ↔
      ∃ u ∈ unitsCongruenceSubgroup 𝔪, u • (a : mixedSpace K) = (b : mixedSpace K) := by
  constructor
  · -- Forward: forget that `ζ` is a root of unity and read the action off in the mixed space.
    rintro ⟨⟨ζ, hζ⟩, rfl⟩
    exact ⟨ζ, (mem_unitsCongruenceTorsion.mp hζ).1, by simp⟩
  · -- Reverse: `u` carries `a` to `b`, both in the domain, so `u` is a root of unity.
    rintro ⟨u, hu, hsmul⟩
    have htors : u ∈ NumberField.Units.torsion K :=
      (unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain_iff_mem_torsion
        (mem_rayIntegerSet.mp a.prop).1 hu).mp (hsmul ▸ (mem_rayIntegerSet.mp b.prop).1)
    exact ⟨⟨u, mem_unitsCongruenceTorsion.mpr ⟨hu, htors⟩⟩, Subtype.ext (by simpa using hsmul)⟩

end TauCeti.GlobalNumberFields
