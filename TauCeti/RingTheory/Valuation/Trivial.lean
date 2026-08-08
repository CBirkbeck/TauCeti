/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The trivial valuation attached to a prime ideal

The trivial valuation of a prime ideal `𝔭` of a commutative ring: it is `0` on `𝔭` and `1`
off it. It is the pullback of Mathlib's trivial valuation `1` on the quotient domain `A ⧸ 𝔭`
along the quotient map.

## Main definitions

* `TauCeti.Valuation.trivialValuation 𝔭` : The trivial valuation attached to a prime
  ideal `𝔭`, with values in `WithZero (Multiplicative ℤ)`.

## Main results

* `TauCeti.Valuation.trivialValuation_eq_zero_iff` : The trivial valuation vanishes exactly
  on `𝔭`.
-/

public section

namespace TauCeti.Valuation

variable {A : Type*} [CommRing A]

open scoped Classical in
/-- The trivial valuation attached to a prime ideal `𝔭`: it is `0` on `𝔭` and `1` off it,
as the pullback of the trivial valuation on the quotient domain `A ⧸ 𝔭` along the quotient
map. -/
noncomputable def trivialValuation (𝔭 : Ideal A) [𝔭.IsPrime] :
    Valuation A (WithZero (Multiplicative ℤ)) :=
  (1 : Valuation (A ⧸ 𝔭) (WithZero (Multiplicative ℤ))).comap (Ideal.Quotient.mk 𝔭)

open scoped Classical in
/-- The value of the trivial valuation, as an `if`. -/
lemma trivialValuation_apply {𝔭 : Ideal A} [𝔭.IsPrime] (a : A) :
    trivialValuation 𝔭 a = if a ∈ 𝔭 then 0 else 1 := by
  rw [trivialValuation, Valuation.comap_apply, Valuation.one_apply_def]
  simp only [Ideal.Quotient.eq_zero_iff_mem]

open scoped Classical in
/-- The trivial valuation vanishes exactly on the prime ideal. -/
@[simp]
lemma trivialValuation_eq_zero_iff {𝔭 : Ideal A} [𝔭.IsPrime] {a : A} :
    trivialValuation 𝔭 a = 0 ↔ a ∈ 𝔭 := by
  rw [trivialValuation, Valuation.comap_apply, Valuation.one_apply_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]

open scoped Classical in
/-- Elements outside the prime ideal have value `1` under the trivial valuation. -/
lemma trivialValuation_eq_one_of_notMem {𝔭 : Ideal A} [𝔭.IsPrime] {a : A} (ha : a ∉ 𝔭) :
    trivialValuation 𝔭 a = 1 := by
  rw [trivialValuation, Valuation.comap_apply,
    Valuation.one_apply_of_ne_zero (by simpa [Ideal.Quotient.eq_zero_iff_mem] using ha)]

end TauCeti.Valuation
