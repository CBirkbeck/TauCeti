/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Ring homomorphisms and `MvPowerSeries.invOfUnit`

`MvPowerSeries.invOfUnit D u` inverts a multivariate power series whose constant coefficient is
the unit `u`. This file records that a ring homomorphism between power series rings commutes
with it.

## Main results

* `MvPowerSeries.map_invOfUnit`: for a ring homomorphism `φ` between multivariate power series
  rings, `φ (invOfUnit D 1) = invOfUnit (φ D) 1`, given that `D` and `φ D` both have constant
  coefficient `1`.

## Implementation notes

The unit is fixed to `1` rather than left general. `invOfUnit D u` carries the hypothesis
`constantCoeff D = u`, so a general statement would have to transport `u` along `φ` as a unit
as well, and every consumer here inverts a series whose constant coefficient is literally `1`.

The homomorphism is taken as a `RingHomClass` rather than a bundled `RingHom` so that the
lemma applies both to `MvPowerSeries.map` and to substitution homomorphisms
(`PowerSeries.substAlgHom`), which are the two ways power series rings are mapped in practice.
Note that the two index types are independent: substitution changes the index type, so
requiring them to agree would exclude the substitution case.

The proof is the usual uniqueness-of-inverses argument: `φ D` has two inverses, the image of
`D`'s and its own, so they agree.
-/

public section

namespace MvPowerSeries

variable {σ τ R S : Type*} [CommRing R] [CommRing S]

/-- A ring homomorphism between multivariate power series rings commutes with `invOfUnit`, for
a series whose constant coefficient is `1` and whose image has constant coefficient `1`. -/
theorem map_invOfUnit {F : Type*} [FunLike F (MvPowerSeries σ R) (MvPowerSeries τ S)]
    [RingHomClass F (MvPowerSeries σ R) (MvPowerSeries τ S)] (φ : F) {D : MvPowerSeries σ R}
    (hD : constantCoeff D = 1) (hD' : constantCoeff (φ D) = 1) :
    φ (invOfUnit D 1) = invOfUnit (φ D) 1 := by
  have h1 : φ D * φ (invOfUnit D 1) = 1 := by
    rw [← map_mul, mul_invOfUnit D 1 (by rw [hD]; rfl), map_one]
  have h2 : φ D * invOfUnit (φ D) 1 = 1 := mul_invOfUnit _ 1 (by rw [hD']; rfl)
  calc φ (invOfUnit D 1)
      = φ (invOfUnit D 1) * (φ D * invOfUnit (φ D) 1) := by rw [h2, mul_one]
    _ = (φ D * φ (invOfUnit D 1)) * invOfUnit (φ D) 1 := by ring
    _ = invOfUnit (φ D) 1 := by rw [h1, one_mul]

end MvPowerSeries
