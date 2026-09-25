/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Units of the `p`-adic integers

Complements to Mathlib's `PadicInt` API on the units of `ℤ_p`: `1 + x` is a unit whenever
`p ∣ x`, because `ℤ_p` is a local ring whose maximal ideal is `pℤ_p`. This is the criterion
that makes `1 + p^f ℤ_p` a subgroup of `ℤ_pˣ`.

## Main results

* `PadicInt.isUnit_one_add_of_dvd`: `1 + x` is a unit of `ℤ_[p]` whenever `p ∣ x`.
-/

public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- In `ℤ_p`, `1 + x` is a unit whenever `p ∣ x`. -/
theorem isUnit_one_add_of_dvd {x : ℤ_[p]} (hx : (p : ℤ_[p]) ∣ x) : IsUnit (1 + x) :=
  IsLocalRing.isUnit_of_mem_nonunits_one_sub_self _ <| by
    rw [sub_add_cancel_left, mem_nonunits, norm_neg]
    exact (norm_lt_one_iff_dvd x).mpr hx

end PadicInt
