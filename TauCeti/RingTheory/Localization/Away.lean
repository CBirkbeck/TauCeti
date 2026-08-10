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

* `TauCeti.Localization.divSelf`: the element `t/s` of a localisation away from `s`.

## Main results

* `TauCeti.Localization.divSelf_one`: `1/s` is Mathlib's `IsLocalization.Away.invSelf`.
* `TauCeti.Localization.invSelf_mul_algebraMap`: scaling `1/s` by `t` gives `t/s`.
* `TauCeti.Localization.algebraMap_mul_divSelf` and
  `TauCeti.Localization.divSelf_mul_algebraMap`: `s · (t/s) = t` in both orders.
* `TauCeti.Localization.divSelf_zero`, `TauCeti.Localization.divSelf_add` and
  `TauCeti.Localization.divSelf_mul`: `t/s` is additive and `A`-linear in the
  numerator.
* `TauCeti.Localization.divSelf_mul_cancel_left` and
  `TauCeti.Localization.divSelf_mul_cancel_right`: `(s · t)/s = t` and `(t · s)/s = t`.
* `TauCeti.Localization.divSelf_self`: `s/s = 1`.

## Provenance

`divSelf` and its identities are ported from AINTLIB's
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
noncomputable def divSelf : S :=
  IsLocalization.mk' S t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

/-- `t/s` is the fraction `mk' t s`. The body of `divSelf` is not exported, so this is how a
consumer reaches Mathlib's `IsLocalization` API for it. -/
theorem divSelf_def :
    divSelf t s = IsLocalization.mk' S t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s) :=
  (rfl)

/-- `1/s` is Mathlib's `IsLocalization.Away.invSelf`, so its simp set applies to `divSelf 1 s`. -/
@[simp]
theorem divSelf_one : divSelf 1 s = (IsLocalization.Away.invSelf s : S) := (rfl)

/-- **Scaling `1/s` by `t` gives `t/s`.** Stated with `IsLocalization.Away.invSelf` rather than
`divSelf 1 s` on the left, because `divSelf_one` makes `invSelf` the simp-normal form of `1/s`; the
two together normalise a product of a unit fraction and a scalar to a single `divSelf`. -/
@[simp]
theorem invSelf_mul_algebraMap :
    (IsLocalization.Away.invSelf s : S) * algebraMap A S t = divSelf t s := by
  rw [← divSelf_one, divSelf_def, divSelf_def,
    IsLocalization.mk'_eq_mul_mk'_one t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)]
  exact mul_comm _ _

/-- **Clearing the denominator**: `s · (t/s) = t`. -/
@[simp]
theorem algebraMap_mul_divSelf :
    algebraMap A S s * divSelf t s = algebraMap A S t := by
  rw [divSelf_def]
  exact IsLocalization.mk'_spec' S t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

/-- **Clearing the denominator inside the numerator**: `(s · t)/s = t`. -/
@[simp]
theorem divSelf_mul_cancel_left : divSelf (s * t) s = algebraMap A S t := by
  rw [divSelf_def]
  exact IsLocalization.mk'_mul_cancel_left t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

/-- The same on the other side: `(t · s)/s = t`. -/
@[simp]
theorem divSelf_mul_cancel_right : divSelf (t * s) s = algebraMap A S t := by
  rw [divSelf_def]
  exact IsLocalization.mk'_mul_cancel_right t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

/-- **Clearing the denominator on the right**: `(t/s) · s = t`. The mirror of
`algebraMap_mul_divSelf`; `S` is only a `CommSemiring`, `mul_comm` is not `simp`, and Mathlib's
`IsLocalization.Away.mul_invSelf` fixes the other order, so without this the reversed goal is
left open. -/
@[simp]
theorem divSelf_mul_algebraMap :
    divSelf t s * algebraMap A S s = algebraMap A S t := by
  rw [divSelf_def]
  exact IsLocalization.mk'_spec S t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

/-- The mirror of `invSelf_mul_algebraMap`, for the same reason. -/
@[simp]
theorem algebraMap_mul_invSelf :
    algebraMap A S t * (IsLocalization.Away.invSelf s : S) = divSelf t s := by
  rw [mul_comm]; exact invSelf_mul_algebraMap t s

/-! ### The numerator

`divSelf` is additive and `A`-linear in its numerator. The body is not exported, so without these
a consumer computing with `t/s` — products of the generators of a localisation subring are
exactly such fractions — has to `rw [divSelf_def]` down to `IsLocalization.mk'`. Each is read off
`invSelf_mul_algebraMap`, which turns the fraction into a product with a fixed left factor. -/

/-- `0/s = 0`. -/
@[simp]
theorem divSelf_zero : (divSelf 0 s : S) = 0 := by
  simp only [← invSelf_mul_algebraMap, map_zero, mul_zero]

/-- `t/s` is additive in the numerator. -/
theorem divSelf_add (u : A) : divSelf (t + u) s = (divSelf t s : S) + divSelf u s := by
  simp only [← invSelf_mul_algebraMap, map_add, mul_add]

/-- `t/s` is `A`-linear in the numerator. -/
theorem divSelf_mul (a : A) :
    divSelf (a * t) s = algebraMap A S a * divSelf t s := by
  simp only [← invSelf_mul_algebraMap, map_mul]
  ring

/-- `s/s = 1`. Without this the simp set turns `invSelf s * algebraMap A S s` into `divSelf s s`
and stops, where before `invSelf_mul_algebraMap` it could reach `1` through Mathlib's
`IsLocalization.Away.mul_invSelf`. -/
@[simp]
theorem divSelf_self : (divSelf s s : S) = 1 := by
  rw [divSelf_def]
  exact IsLocalization.mk'_self S (Submonoid.mem_powers s)

end TauCeti.Localization
