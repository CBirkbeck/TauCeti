/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count

/-!
# Character sums over the integral ideals of bounded norm

Let `𝔪` be a modulus of a number field `K` and `χ` a ray class character of `𝔪`.  This file
introduces `rayClassCharacterPartialSum 𝔪 χ x`, the sum of `χ` over the nonzero integral ideals
prime to the finite part of `𝔪` whose norm is at most `x`, and identifies it with the
`χ`-weighted combination of the ray class counting functions.

The sum ranges over ideals, not over chosen class representatives.  Regrouping it by ray class is
exactly the partition `idealClassSigmaEquiv`, and on each fibre `χ` is constant, so each class
contributes its counting function scaled by the single value `χ` takes there.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassCharacterPartialSum`: the partial sum of a ray class
  character over the integral ideals of bounded norm.

## Main results

* `TauCeti.GlobalNumberFields.rayClassCharacterPartialSum_eq_sum`: the partial sum is
  `∑ c, χ c * rayClassIdealCountingFunction 𝔪 c x`.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VIII.
-/

public section

namespace TauCeti.GlobalNumberFields

open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **The partial sum of a ray class character.**  The sum of `χ` evaluated on the ray class of `I`,
over the nonzero integral ideals `I` prime to the finite part of `𝔪` with `absNorm I ≤ x`.

The index type is finite, so the `finsum` is an ordinary finite sum; it is written as a `finsum`
because the carrier is a subtype rather than a `Finset`. -/
noncomputable def rayClassCharacterPartialSum
    (𝔪 : Modulus K) (χ : RayClassCharacter 𝔪) (x : ℝ) : ℂ :=
  ∑ᶠ I : {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x},
    (χ (idealClass 𝔪 (I : integralIdealsPrimeTo 𝔪)) : ℂ)

open scoped Classical in
/-- The partial sum unfolded.  A downstream module cannot see through the definition on its own —
the module system does not expose it — so this is the lemma that turns the sum back into the family
it sums. -/
theorem rayClassCharacterPartialSum_def (𝔪 : Modulus K) (χ : RayClassCharacter 𝔪) (x : ℝ) :
    rayClassCharacterPartialSum 𝔪 χ x =
      ∑ᶠ I : {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x},
        (χ (idealClass 𝔪 (I : integralIdealsPrimeTo 𝔪)) : ℂ) :=
  (rfl)

/-- **A character partial sum is the weighted combination of the class counts.**  The partial sum
of `χ` over the integral ideals prime to `𝔪` of norm at most `x` is the sum of the ray class
counting functions, each weighted by the value `χ` takes on its class. -/
theorem rayClassCharacterPartialSum_eq_sum (𝔪 : Modulus K) [Fintype (RayClassGroup 𝔪)]
    (χ : RayClassCharacter 𝔪) (x : ℝ) :
    rayClassCharacterPartialSum 𝔪 χ x =
      ∑ c : RayClassGroup 𝔪, (χ c : ℂ) * rayClassIdealCountingFunction 𝔪 c x := by
  have : Fintype {I : integralIdealsPrimeTo 𝔪 //
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} := Fintype.ofFinite _
  have (c : RayClassGroup 𝔪) : Fintype {I : integralIdealsPrimeTo 𝔪 //
      idealClass 𝔪 I = c ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} := Fintype.ofFinite _
  -- regroup the ideals of norm at most `x` by ray class
  rw [rayClassCharacterPartialSum_def, finsum_eq_sum_of_fintype,
    ← Equiv.sum_comp (idealClassSigmaEquiv 𝔪 x), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  -- on the fibre over `c` the character is constantly `χ c`, so the block is a multiple of it
  simp only [idealClassSigmaEquiv_apply_coe]
  rw [Finset.sum_eq_card_nsmul fun p _ ↦ by rw [p.2.1]]
  simp [rayClassIdealCountingFunction_def, mul_comm]

end TauCeti.GlobalNumberFields
