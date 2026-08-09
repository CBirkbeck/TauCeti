/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The fraction `t/s` in an away localisation

`Localization.Away s` inverts `s`, so it contains `t/s` for every `t`. This file names that
element and gives the two identities that manipulating it needs: scaling `1/s` by `t`, and
clearing the denominator.

Nothing here is topological or Huber-specific — it is `IsLocalization` algebra over an
arbitrary commutative ring — so it is stated outside the Huber namespace, alongside
`TauCeti/RingTheory/Localization/DenIdeal.lean`.

## Main definitions

* `TauCeti.Localization.divByS`: the element `t/s` of `Localization.Away s`.

## Main results

* `TauCeti.Localization.divByS_one_mul_algebraMap`: scaling `1/s` by `t` gives `t/s`.
* `TauCeti.Localization.algebraMap_mul_divByS`: `s · (t/s) = t`.
-/

public section

namespace TauCeti.Localization

variable {A : Type*} [CommRing A]

/-- The element `t/s` in `Localization.Away s`. -/
noncomputable def divByS (t s : A) : Localization.Away s :=
  IsLocalization.mk' (Localization.Away s) t
    (⟨s, ⟨1, pow_one s⟩⟩ : Submonoid.powers s)

/-- `t/s` is the fraction `mk' t s`. The body of `divByS` is not exported, so this is how a
consumer reaches Mathlib's `IsLocalization` API for it. -/
theorem divByS_def (t s : A) :
    divByS t s = IsLocalization.mk' (Localization.Away s) t
      (⟨s, ⟨1, pow_one s⟩⟩ : Submonoid.powers s) := (rfl)

/-- Scaling `1/s` by `t` gives `t/s`. -/
@[simp]
theorem divByS_one_mul_algebraMap (t s : A) :
    divByS 1 s * algebraMap A (Localization.Away s) t = divByS t s := by
  rw [divByS_def, divByS_def, ← IsLocalization.mk'_one (M := Submonoid.powers s)
    (S := Localization.Away s) t, ← IsLocalization.mk'_mul, one_mul, mul_one]

/-- **Clearing the denominator**: `s · (t/s) = t` in `Localization.Away s`. -/
@[simp]
theorem algebraMap_mul_divByS (t s : A) :
    algebraMap A (Localization.Away s) s * divByS t s =
      algebraMap A (Localization.Away s) t := by
  rw [divByS_def]
  exact IsLocalization.mk'_spec' (Localization.Away s) t
    (⟨s, ⟨1, pow_one s⟩⟩ : Submonoid.powers s)

end TauCeti.Localization
