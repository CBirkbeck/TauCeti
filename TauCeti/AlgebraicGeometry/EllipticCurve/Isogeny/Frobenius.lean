/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The Frobenius isogeny

Over a finite field `F` with `q = Nat.card F` elements, raising to the `q`-th power is an
`F`-algebra endomorphism of any `F`-algebra (`FiniteField.frobeniusAlgHom`). Composing it with
the embedding of the coordinate ring into the function field gives a coordinate pullback, and
that pullback maps infinity to infinity, so it is an isogeny of `W` with itself.

The declarations take `[Finite F]` rather than `[Fintype F]`, matching
`Affine/FrobeniusTower.lean`, and state the exponent as `Nat.card F`: a `Fintype` instance is
chosen enumeration data, and neither the definitions nor the statements should depend on it. The
instance Mathlib's map needs is installed locally where it is required.

## Main definitions

* `TauCeti.Isogeny.frobeniusPullback`: the coordinate pullback `x ↦ x ^ q`.
* `TauCeti.Isogeny.frobeniusIsogeny`: the same map packaged as an `Isogeny W W`.

The `MapsInfinity` condition is the only content: every `x` of the coordinate ring is a root of the
monic polynomial `X ^ q - C x` over the pulled-back copy, since the pullback sends `x` to `x ^ q`.
That is integrality of the coordinates over their `q`-th powers, which is what "Frobenius fixes the
point at infinity" amounts to here.

Its degree is `q`, and the field-theoretic half of that statement is already available as
`TauCeti.WeierstrassCurve.Affine.finrank_fieldRange_frobeniusAlgHom`; the isogeny-level
`degree` is not yet on `main`, so the degree computation is deliberately left to a later PR.

This is the `frobeniusIsogeny` seed of `TauCetiRoadmap/EllipticCurves/README.md` §Layer 1, where it
is described as "`f ↦ f ^ q` out of the coordinate ring into the function field … whose
`MapsInfinity` is the integrality of the coordinates over their `q`-th powers". The roadmap's
`Suggested.lean` states it with `sorry`; the proof here is original.
-/

public section

namespace TauCeti

open Polynomial WeierstrassCurve.Affine

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve.Affine F)

namespace Isogeny

/-- The Frobenius coordinate pullback: an element of the coordinate ring is sent to its `q`-th
power, viewed in the function field, where `q = Nat.card F`. -/
noncomputable def frobeniusPullback : CoordinatePullback W W :=
  letI := Fintype.ofFinite F
  (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField).comp
    (FiniteField.frobeniusAlgHom F W.CoordinateRing)

/-- The Frobenius pullback raises to the `q`-th power. -/
@[simp]
theorem frobeniusPullback_apply (x : W.CoordinateRing) :
    frobeniusPullback W x = algebraMap W.CoordinateRing W.FunctionField (x ^ Nat.card F) := by
  let _ := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  rfl

/-- **Frobenius maps the point at infinity to itself.** Every `x` satisfies the monic polynomial
`X ^ q - C x` over the pulled-back coordinate ring, because the pullback carries `x` to `x ^ q`. -/
theorem mapsInfinity_frobeniusPullback : (frobeniusPullback W).MapsInfinity := by
  rw [CoordinatePullback.mapsInfinity_iff]
  intro x
  refine ⟨X ^ Nat.card F - C x, monic_X_pow_sub_C x Nat.card_pos.ne', ?_⟩
  -- The two `algebraMap`s below are different instances: the point is taken along the canonical
  -- embedding, while `eval₂` uses the pullback's, for which `algebraMap` *is* the pullback. The
  -- step that matters is `frobeniusPullback_apply`, named here rather than left implicit.
  have hpull := frobeniusPullback_apply W x
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C]
  exact sub_eq_zero.mpr ((map_pow _ x _).symm.trans hpull.symm)

/-- **The Frobenius isogeny** of a Weierstrass curve over a finite field. -/
noncomputable def frobeniusIsogeny : Isogeny W W where
  pullback := frobeniusPullback W
  mapsInfinity := mapsInfinity_frobeniusPullback W

/-- The Frobenius isogeny's pullback is the `q`-th power map. -/
@[simp]
theorem frobeniusIsogeny_pullback : (frobeniusIsogeny W).pullback = frobeniusPullback W := (rfl)

end Isogeny

end TauCeti

end
