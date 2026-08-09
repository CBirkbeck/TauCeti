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
`f` is an equivalence the induced map is an equivalence, and Mathlib already has the construction
generically: `R[W]` is by definition `AdjoinRoot W.polynomial`, so `AdjoinRoot.mapRingEquiv`
applies. What is missing is the bridge — that the generic equivalence *is* `CoordinateRing.map` —
without which the equivalence is cut off from the `map_mk`, `map_smul` and `map_injective` API
stated about `CoordinateRing.map`.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.mapEquiv`: the induced ring equivalence
  `R[W] ≃+* S[W.map e]`, as `AdjoinRoot.mapRingEquiv` along `map_polynomial`.
* `WeierstrassCurve.Affine.CoordinateRing.mapEquiv_apply`: it agrees with `CoordinateRing.map`.
* `WeierstrassCurve.Affine.CoordinateRing.map_bijective`: hence `CoordinateRing.map` along an
  equivalence is bijective.

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
There the equivalence is rebuilt by hand — injectivity from `map_injective`, surjectivity by
lifting `e.symm` through `AdjoinRoot.mk` — inside a 267-line file that also constructs the
function-field Frobenius. Here neither half is reproved: the equivalence is Mathlib's
`AdjoinRoot.mapRingEquiv`, and the only new content is that it agrees with `CoordinateRing.map`.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve.Affine R)

/-- **A ring equivalence of the base induces one of the coordinate rings.** This is Mathlib's
generic `AdjoinRoot.mapRingEquiv`, specialised along `map_polynomial`: `R[W]` is by definition
`AdjoinRoot W.polynomial`, and `(W.map e).polynomial` is `W.polynomial.map (mapRingHom e)`. -/
noncomputable def mapEquiv (e : R ≃+* S) :
    W.CoordinateRing ≃+* (W.map (e : R →+* S)).CoordinateRing :=
  AdjoinRoot.mapRingEquiv (Polynomial.mapEquiv e) W.polynomial (W.map (e : R →+* S)).polynomial
    (by rw [WeierstrassCurve.Affine.map_polynomial]; rfl)

/-- **The induced equivalence is Mathlib's `CoordinateRing.map`.** Without this the equivalence
would be cut off from the `map_mk`, `map_smul` and `map_injective` API stated about
`CoordinateRing.map`. -/
@[simp]
lemma mapEquiv_apply (e : R ≃+* S) (x : W.CoordinateRing) :
    mapEquiv W e x = map W (e : R →+* S) x := by
  induction x using AdjoinRoot.induction_on with
  | _ p =>
    simp only [mapEquiv, AdjoinRoot.mapRingEquiv, RingEquiv.ofRingHom_apply, AdjoinRoot.map, map,
      AdjoinRoot.lift_mk]
    rfl

/-- `CoordinateRing.map` along a ring equivalence is bijective. -/
lemma map_bijective (e : R ≃+* S) : Function.Bijective (map W (e : R →+* S)) := by
  simpa only [funext (mapEquiv_apply W e)] using (mapEquiv W e).bijective

end WeierstrassCurve.Affine.CoordinateRing

end
