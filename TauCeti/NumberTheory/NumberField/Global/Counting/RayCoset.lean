/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Counting.CongruenceLattice
public import TauCeti.RingTheory.Ideal.CoprimeCoset

/-!
# The admissible generators of a ray class, in the mixed space

Counting the integral ideals of a fixed ray class runs over the generators `α` of an ideal that are
congruent to one modulo the finite part `𝔪₀` of the modulus.  For an ideal `𝔞` prime to `𝔪₀` those
generators form a coset of `𝔞 * 𝔪₀`, and this file records what their images look like in the mixed
space: a single translate of `congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)`.

The lattice being translated depends only on `𝔪` and `𝔞`, not on the generator chosen to name the
translate, so the images of the admissible generators are the points of one translate of a fixed
lattice.

## Main results

* `TauCeti.GlobalNumberFields.image_setOf_mem_and_sub_one_mem_eq_vadd_congruenceLattice`:
  the images of the admissible generators are a translate of the congruence lattice.
-/

public section

open IsDedekindDomain NumberField NumberField.mixedEmbedding

open scoped Pointwise nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The admissible generators map onto a coset of the congruence lattice.**  For a nonzero
integral ideal `𝔞` and an element `ξ` of `𝔞` congruent to one modulo `𝔪₀`, the elements of `𝔞`
congruent to one modulo `𝔪₀` map onto the translate of
`congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)` by the image of `ξ`.

An admissible `ξ` is what `Ideal.isCoprime_iff_exists_mem_and_sub_one_mem` extracts from
coprimality of `𝔞` and `𝔪₀`, and the lattice on the right does not involve `ξ`: two admissible
choices give translates of the same lattice. -/
theorem image_setOf_mem_and_sub_one_mem_eq_vadd_congruenceLattice (𝔪 : Modulus K)
    (𝔞 : (Ideal (𝓞 K))⁰) {ξ : 𝓞 K} (hξ𝔞 : ξ ∈ (𝔞 : Ideal (𝓞 K))) (hξ𝔪 : ξ - 1 ∈ 𝔪.finitePart) :
    (fun y : 𝓞 K ↦ mixedEmbedding K (y : K)) ''
        {α : 𝓞 K | α ∈ (𝔞 : Ideal (𝓞 K)) ∧ α - 1 ∈ 𝔪.finitePart} = mixedEmbedding K (ξ : K) +ᵥ
          (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞) : Set (mixedSpace K)) := by
  rw [Ideal.setOf_mem_and_sub_one_mem_eq_vadd_mul hξ𝔞 hξ𝔪, coe_congruenceLattice_mk0_eq_image]
  -- `rw` cannot finish here: the map in the statement is the coercion of the composite ring hom
  -- only up to unfolding, and `rw` matches syntactically
  exact Set.image_vadd_distrib ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)) ξ _

end TauCeti.GlobalNumberFields
