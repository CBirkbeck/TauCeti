/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# A ring equivalence of the base induces one of the coordinate rings

Mathlib's `WeierstrassCurve.Affine.CoordinateRing.map` sends a ring homomorphism `f : R →+* S` to
`R[W] →+* S[W.map f]`, and proves it injective when `f` is (`CoordinateRing.map_injective`). When
`f` is an equivalence the induced map is an equivalence too, which is what this file adds: the
missing surjectivity, and the resulting `≃+*`.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.map_surjective`: `CoordinateRing.map` along a ring
  equivalence is surjective.
* `WeierstrassCurve.Affine.CoordinateRing.mapEquiv`: the induced ring equivalence
  `R[W] ≃+* S[W.map e]`.

Stated over arbitrary commutative rings; the curve need not be elliptic, since the argument is
just that `Polynomial.map` along `e` and along `e.symm` are mutually inverse.

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
There the statement is bundled as bijectivity of a map between the coordinate rings of a curve and
of its image; here it is split into the surjectivity Mathlib is missing and the packaged `≃+*`,
with injectivity taken from Mathlib's `CoordinateRing.map_injective` rather than reproved.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve.Affine R)

/-- `CoordinateRing.map` along a ring equivalence is surjective: a class upstairs is the image of
the class of the same polynomial pulled back along `e.symm`. -/
lemma map_surjective (e : R ≃+* S) :
    Function.Surjective (map W (e : R →+* S)) := fun y => by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨mk W (p.map (mapRingHom (e.symm : S →+* R))), ?_⟩
  rw [map_mk, Polynomial.map_map]
  simp

/-- **A ring equivalence of the base induces one of the coordinate rings.** Injectivity is
Mathlib's `CoordinateRing.map_injective`; surjectivity is `map_surjective` above. -/
noncomputable def mapEquiv (e : R ≃+* S) :
    W.CoordinateRing ≃+* (W.map (e : R →+* S)).CoordinateRing :=
  RingEquiv.ofBijective (map W (e : R →+* S))
    ⟨map_injective e.injective, map_surjective W e⟩

@[simp]
lemma mapEquiv_apply (e : R ≃+* S) (x : W.CoordinateRing) :
    mapEquiv W e x = map W (e : R →+* S) x := RingEquiv.ofBijective_apply _ _ _

end WeierstrassCurve.Affine.CoordinateRing

end
