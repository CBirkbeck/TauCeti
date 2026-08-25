/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace

/-!
# The infinite place of a quadratic field `ℚ(√d)`

For `d < 0`, the imaginary quadratic field `ℚ(√d)` is totally complex: a special case of
`NumberField.isTotallyComplex_of_sq_ratCast_of_neg` via the generator `θ` with `θ² = d`.

## Main results

* `NumberField.isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg`.
* `NumberField.InfinitePlace.nrComplexPlaces_eq_one_of_finrank_eq_two`: an imaginary
  quadratic field has exactly one complex place.
-/

public section

open Polynomial NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **An imaginary quadratic field is totally complex.** Any number field `K` containing an
algebraic integer `θ` with `minpoly ℤ θ = X² - d` and `d < 0` is totally complex — in particular the
imaginary quadratic field `ℚ(√d)`. -/
theorem isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hd : d < 0) : IsTotallyComplex K :=
  isTotallyComplex_of_sq_ratCast_of_neg (x := (θ : K)) (r := (d : ℚ))
    (coe_gen_sq_ratCast hmin) (by exact_mod_cast hd)

/-- **An imaginary quadratic field has exactly one complex place.** A totally complex field
satisfies `Module.finrank ℚ K = 2 * nrComplexPlaces K`, so in degree `2` exactly one complex
place remains; together with `NumberField.IsTotallyComplex.nrRealPlaces_eq_zero` it is the
field's only infinite place. -/
theorem InfinitePlace.nrComplexPlaces_eq_one_of_finrank_eq_two [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) : InfinitePlace.nrComplexPlaces K = 1 := by
  have := NumberField.IsTotallyComplex.finrank (K := K)
  omega

end NumberField
