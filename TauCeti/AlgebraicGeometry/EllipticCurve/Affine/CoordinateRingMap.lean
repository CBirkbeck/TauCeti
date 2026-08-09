/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Surjectivity of the coordinate-ring map

Mathlib's `WeierstrassCurve.Affine.CoordinateRing.map` sends a ring homomorphism `f : R →+* S` to
`R[W] →+* S[W.map f]`, and proves it injective when `f` is (`CoordinateRing.map_injective`). This
file adds the two companions Mathlib does not state, at the same generality: surjectivity and
bijectivity.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.map_surjective` and
  `WeierstrassCurve.Affine.CoordinateRing.map_bijective`: stated, like Mathlib's
  `CoordinateRing.map_injective`, for an arbitrary `f : R →+* S`.

For a base *equivalence* `e` these give `RingEquiv.ofBijective (map W e) (map_bijective W
e.bijective)` in one line at the use site, so no equivalence is defined here; Mathlib's generic
`AdjoinRoot.mapRingEquiv` is the other route to the same object.

Stated over arbitrary commutative rings; the curve need not be elliptic.

This supports the Hasse strand of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 3. That
roadmap's Layer-0 narrative makes the Frobenius "the key input to Layer 3", and the arithmetic
Frobenius of the function field over a finite field is obtained by transporting the `q`-power map
of the base along exactly this construction: it is a ring *equivalence* of `K̄` and so must be
carried to an equivalence of coordinate rings before it can be pushed to the fraction field. The
roadmap's §"What Mathlib already has (consume)" lists `Affine.CoordinateRing` as consumed
infrastructure that "is load-bearing API here, not an implementation detail"; this is a complement
to that API, not a reimplementation of it.

## Provenance

The need for this step, and the surjectivity argument (lift `e.symm` through `AdjoinRoot.mk` and
`Polynomial.map`), are from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`,
Apache-2.0, pinned by that roadmap at `dev/hasse-weil @ 513e83879e2f`),
`HasseWeil/WeilPairing/FrobeniusFunctionFieldEquiv.lean`, declaration `coordRingMap_bijective`.
There it is bundled as bijectivity of one map, for a ring equivalence only, inside a 267-line file
that also constructs the function-field Frobenius. Here it is split out and generalised: the
surjectivity is stated for any surjective `f : R →+* S`, matching the generality of Mathlib's
`CoordinateRing.map_injective`, and the equivalence it was bundled
for is left to the use site.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve.Affine R)

/-- **`CoordinateRing.map` is surjective when the base map is**, the companion of Mathlib's
`CoordinateRing.map_injective`. -/
lemma map_surjective {f : R →+* S} (hf : Function.Surjective f) :
    Function.Surjective (map W f) := fun y => by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective (mapRingHom f) (Polynomial.map_surjective f hf) p
  exact ⟨mk W q, map_mk f q⟩

/-- **`CoordinateRing.map` is bijective when the base map is.** -/
lemma map_bijective {f : R →+* S} (hf : Function.Bijective f) :
    Function.Bijective (map W f) :=
  ⟨map_injective hf.1, map_surjective W hf.2⟩

end WeierstrassCurve.Affine.CoordinateRing

end
