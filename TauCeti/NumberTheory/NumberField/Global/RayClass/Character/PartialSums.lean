/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Sum
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Asymptotic

/-!
# Cancellation in the partial sums of a nontrivial ray class character

Let `𝔪` be a modulus of a number field `K` and `χ` a nontrivial ray class character of `𝔪`.
This file proves that the sum of `χ` over the nonzero integral ideals prime to `𝔪` of norm at
most `x` is `O(x ^ (1 - δ))` for some `δ > 0`.

The partial sum is the `χ`-weighted combination of the ray class counting functions.  Every class
has the same main term `rayClassIdealMainTerm 𝔪 * x`, and the values of a nontrivial character
of the finite ray class group sum to zero, so the main terms cancel and only the error terms of
the class counts remain.

## Main results

* `TauCeti.GlobalNumberFields.rayClassCharacter_partialSums`: the partial sums of a nontrivial
  ray class character are `O(x ^ (1 - δ))` for some `δ > 0`.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VIII.
-/

public section

open Asymptotics Filter

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **Cancellation of a nontrivial ray class character.**  The partial sums of a nontrivial ray
class character over the integral ideals of norm at most `x` are `O(x ^ (1 - δ))` for some
`δ > 0`. -/
theorem rayClassCharacter_partialSums (𝔪 : Modulus K) (χ : RayClassCharacter 𝔪) (hχ : χ ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧
      (fun x : ℝ => rayClassCharacterPartialSum 𝔪 χ x) =O[atTop]
        (fun x : ℝ => ((x ^ (1 - δ) : ℝ) : ℂ)) := by
  have : Fintype (RayClassGroup 𝔪) := Fintype.ofFinite _
  obtain ⟨δ, hδ, hcount⟩ := rayClassIdealCount 𝔪
  -- the character values sum to zero, so the common main term drops out
  have hχ0 : ∑ c : RayClassGroup 𝔪, (χ c : ℂ) = 0 :=
    sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) fun h ↦ hχ <|
      MonoidHom.ext fun c ↦ Units.ext (DFunLike.congr_fun h c)
  have hsum (x : ℝ) : rayClassCharacterPartialSum 𝔪 χ x = ∑ c : RayClassGroup 𝔪,
      (χ c : ℂ) * (((rayClassIdealCountingFunction 𝔪 c x : ℝ) -
        rayClassIdealMainTerm 𝔪 * x : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast, mul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hχ0, zero_mul, sub_zero]
    exact rayClassCharacterPartialSum_eq_sum 𝔪 χ x
  refine ⟨δ, hδ, ?_⟩
  simp_rw [hsum]
  refine IsBigO.fun_sum fun c _ ↦ IsBigO.const_mul_left ?_ _
  exact Complex.isBigO_ofReal_right.mpr (Complex.isBigO_ofReal_left.mpr (hcount c))

end TauCeti.GlobalNumberFields
