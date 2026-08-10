/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.XYIdealMaximal
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# The local ring of an elliptic curve at an affine point is a discrete valuation ring

The coordinate ring of an elliptic curve is a Dedekind domain
(`TauCeti.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing`), and the ideal of a point is
maximal and nonzero (`XYIdeal_isMaximal_of_equation`, `XYIdeal_ne_bot`). Localising at that ideal
therefore gives a discrete valuation ring.

## Main results

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.isDiscreteValuationRing_of_isLocalizationAtPrime`:
  a localisation of the coordinate ring at any nonzero prime is a discrete valuation ring.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.isDiscreteValuationRing_localizationAtPrime`: the
  same for `Localization.AtPrime` at a point of the curve, from the curve equation alone.

No valuation is defined here: the results give the `IsDiscreteValuationRing` structure, which is
what an order-of-vanishing and uniformiser API would be built on.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors).
That layer's §Places asks for the affine places as the maximal ideals of the coordinate ring, "for
elliptic `W` a Dedekind domain — itself a worthwhile lemma", together with an API of `ord_v`,
uniformisers and residue fields; this supplies the local rings that such an API is stated over. The
layer says its own place types are new API to be built there rather than pinned, and it seeds no
declaration this competes with; it also records that the design is coordinated with D. Angdinata's
in-flight upstream `CoordinateRing` work.

## Provenance

The statement is that of `localRing_isDVR` in the AINTLIB `HasseWeil` project
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by that roadmap at
`dev/hasse-weil @ 513e83879e2f`), `HasseWeil/Valuation.lean`. Its proof is not ported: with the
coordinate ring already known to be a Dedekind domain, Mathlib's
`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` gives the conclusion directly.
The source's hypothesis is nonsingularity of the point; here the curve equation suffices, matching
the weakening already made for `XYIdeal_isMaximal_of_equation`.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F} {x : F}

/-- **A localisation of the coordinate ring of an elliptic curve at a nonzero prime is a discrete
valuation ring.** Stated for an arbitrary localisation `S`, so that it covers `Localization.AtPrime`
and any other model of it. -/
theorem isDiscreteValuationRing_of_isLocalizationAtPrime [W.IsElliptic] {P : Ideal W.CoordinateRing}
    [P.IsPrime] (hP : P ≠ ⊥)
    (S : Type*) [CommRing S] [IsDomain S] [Algebra W.CoordinateRing S]
    [IsLocalization.AtPrime S P] :
    IsDiscreteValuationRing S :=
  have := isDedekindDomain_coordinateRing W
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hP S

/-- **The local ring at a point of an elliptic curve is a discrete valuation ring**, in the
`Localization.AtPrime` model and from the curve equation alone. The primality of the point's ideal
is a consequence of that equation, through `XYIdeal_isMaximal_of_equation`, so it is installed in
the statement rather than assumed. -/
theorem isDiscreteValuationRing_localizationAtPrime [W.IsElliptic] {y : F}
    (h : W.Equation x y) :
    haveI : (CoordinateRing.XYIdeal W x (C y)).IsPrime := (XYIdeal_isMaximal_of_equation h).isPrime
    IsDiscreteValuationRing (Localization.AtPrime (CoordinateRing.XYIdeal W x (C y))) :=
  haveI : (CoordinateRing.XYIdeal W x (C y)).IsPrime := (XYIdeal_isMaximal_of_equation h).isPrime
  isDiscreteValuationRing_of_isLocalizationAtPrime (P := CoordinateRing.XYIdeal W x (C y))
    (XYIdeal_ne_bot x (C y)) (Localization.AtPrime (CoordinateRing.XYIdeal W x (C y)))

end WeierstrassCurve.Affine.CoordinateRing

end TauCeti

end
