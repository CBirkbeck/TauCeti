/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The fraction `t/s` in an away localisation

A localisation `S` of `A` away from `s` inverts `s`, so it contains `t/s` for every `t : A`.
Mathlib names the inverse itself — `IsLocalization.Away.invSelf s` is `1/s` — but not the general
fraction; this file names it and gives the identities that manipulating it needs: scaling `1/s`
by `t`, and clearing the denominator on either side.

Nothing here is topological or Huber-specific — it is `IsLocalization` algebra over an arbitrary
commutative semiring, for an arbitrary localisation away from `s` — so it is stated outside the
Huber namespace, alongside `TauCeti/RingTheory/Localization/DenIdeal.lean`.

## Main definitions

* `TauCeti.Localization.divByS`: the element `t/s` of a localisation away from `s`.

## Main results

* `TauCeti.Localization.divByS_one`: `1/s` is Mathlib's `IsLocalization.Away.invSelf`.
* `TauCeti.Localization.invSelf_mul_algebraMap`: scaling `1/s` by `t` gives `t/s`.
* `TauCeti.Localization.algebraMap_mul_divByS`: `s · (t/s) = t`.
* `TauCeti.Localization.divByS_self_mul`: `(s · t)/s = t`.

## Provenance

`divByS` and its identities are ported from AINTLIB's
`projects/AdicSpaces/Adic spaces/LocalizationTopology.lean`, branch `dev/adic-spaces`, commit
`d9f2fbbb`, where they are stated for the concrete `Localization.Away s` over a commutative ring
inside the Huber development. They are generalised here to an arbitrary `IsLocalization.Away`
over a commutative semiring, linked to Mathlib's `IsLocalization.Away.invSelf`, and moved out of
the Huber namespace because nothing about them is topological. The topological part of that port
is `TauCeti/RingTheory/Huber/LocalizationTopology.lean`, which records the same provenance.

## References

* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `d9f2fbbb`, `projects/AdicSpaces/Adic spaces/LocalizationTopology.lean`
-/

public section

namespace TauCeti.Localization

variable {A : Type*} [CommSemiring A] {S : Type*} [CommSemiring S] [Algebra A S]
  (t s : A) [IsLocalization.Away s S]

/-- The element `t/s` in a localisation `S` of `A` away from `s`. -/
noncomputable def divByS : S :=
  IsLocalization.mk' S t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

/-- `t/s` is the fraction `mk' t s`. The body of `divByS` is not exported, so this is how a
consumer reaches Mathlib's `IsLocalization` API for it. -/
theorem divByS_def :
    divByS t s = IsLocalization.mk' S t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s) :=
  (rfl)

/-- `1/s` is Mathlib's `IsLocalization.Away.invSelf`, so its simp set applies to `divByS 1 s`. -/
@[simp]
theorem divByS_one : divByS 1 s = (IsLocalization.Away.invSelf s : S) := (rfl)

/-- **Scaling `1/s` by `t` gives `t/s`.** Stated with `IsLocalization.Away.invSelf` rather than
`divByS 1 s` on the left, because `divByS_one` makes `invSelf` the simp-normal form of `1/s`; the
two together normalise a product of a unit fraction and a scalar to a single `divByS`. -/
@[simp]
theorem invSelf_mul_algebraMap :
    (IsLocalization.Away.invSelf s : S) * algebraMap A S t = divByS t s := by
  rw [← divByS_one, divByS_def, divByS_def,
    IsLocalization.mk'_eq_mul_mk'_one t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)]
  exact mul_comm _ _

/-- **Clearing the denominator**: `s · (t/s) = t`. -/
@[simp]
theorem algebraMap_mul_divByS :
    algebraMap A S s * divByS t s = algebraMap A S t := by
  rw [divByS_def]
  exact IsLocalization.mk'_spec' S t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

/-- **Clearing the denominator inside the numerator**: `(s · t)/s = t`. -/
@[simp]
theorem divByS_self_mul : divByS (s * t) s = algebraMap A S t := by
  rw [divByS_def]
  exact IsLocalization.mk'_mul_cancel_left t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

end TauCeti.Localization
