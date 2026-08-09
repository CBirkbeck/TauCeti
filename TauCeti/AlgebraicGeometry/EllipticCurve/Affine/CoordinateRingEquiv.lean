/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# A ring equivalence of the base induces one of the coordinate rings

Mathlib's `WeierstrassCurve.Affine.CoordinateRing.map` sends a ring homomorphism `f : R →+* S` to
`R[W] →+* S[W.map f]`, and proves it injective when `f` is (`CoordinateRing.map_injective`). This
file adds the two companions Mathlib does not state — surjectivity and bijectivity, at the same
generality — and packages the bijective case as a ring equivalence.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.map_surjective` and
  `WeierstrassCurve.Affine.CoordinateRing.map_bijective`: stated, like Mathlib's
  `CoordinateRing.map_injective`, for an arbitrary `f : R →+* S`.
* `WeierstrassCurve.Affine.CoordinateRing.mapEquiv`: the induced `R[W] ≃+* S[W.map e]`, with
  `mapEquiv_apply` identifying it with `CoordinateRing.map` so that the `map_mk`, `map_smul` and
  `map_injective` API applies to it unchanged.

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
`CoordinateRing.map_injective`, and the equivalence is the packaging of the bijective case.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve.Affine R)

/-- **`CoordinateRing.map` is surjective when the base map is**, the companion of Mathlib's
`CoordinateRing.map_injective`. A class upstairs is `mk` of a polynomial, and a polynomial over
`S` is the image of one over `R`. -/
lemma map_surjective {f : R →+* S} (hf : Function.Surjective f) :
    Function.Surjective (map W f) := fun y => by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective (mapRingHom f) (Polynomial.map_surjective f hf) p
  exact ⟨mk W q, map_mk f q⟩

/-- **`CoordinateRing.map` is bijective when the base map is.** -/
lemma map_bijective {f : R →+* S} (hf : Function.Bijective f) :
    Function.Bijective (map W f) :=
  ⟨map_injective hf.1, map_surjective W hf.2⟩

/-- **A ring equivalence of the base induces one of the coordinate rings**, packaging
`map_bijective`. -/
noncomputable def mapEquiv (e : R ≃+* S) :
    W.CoordinateRing ≃+* (W.map (e : R →+* S)).CoordinateRing :=
  RingEquiv.ofBijective (map W (e : R →+* S)) (map_bijective W e.bijective)

/-- The induced equivalence is `CoordinateRing.map`, so all of `map_mk`, `map_smul` and
`map_injective` apply to it. -/
@[simp]
lemma mapEquiv_apply (e : R ≃+* S) (x : W.CoordinateRing) :
    mapEquiv W e x = map W (e : R →+* S) x :=
  RingEquiv.ofBijective_apply _ _ _

end WeierstrassCurve.Affine.CoordinateRing

end
