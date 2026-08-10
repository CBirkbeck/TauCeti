/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.XYIdealMaximal
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# The local ring of an elliptic curve at an affine point is a discrete valuation ring

The coordinate ring of an elliptic curve is a Dedekind domain
(`TauCeti.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing`), and the ideal of a point is
maximal (`TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation`). Localising
at that ideal therefore gives a discrete valuation ring: the local ring of the curve at the point,
whose valuation is the order of vanishing there.

## Main results

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot`: the ideal of a point is nonzero.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.isDiscreteValuationRing_of_isLocalization`: any
  localisation of the coordinate ring at the ideal of a point is a discrete valuation ring.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors).
That layer's §Places asks for the affine places as the maximal ideals of the coordinate ring, "for
elliptic `W` a Dedekind domain — itself a worthwhile lemma", together with the API of `ord_v`,
uniformisers and residue fields. A discrete valuation ring at each affine place is what carries
that API: the valuation is `ord_v`, and a uniformiser is a generator of its maximal ideal. The
layer states that its own place types are new API to be built there rather than pinned, and it
seeds no declaration this competes with; it also records that the design is coordinated with
D. Angdinata's in-flight upstream `CoordinateRing` work.

## Provenance

The statement is that of `localRing_isDVR` in the AINTLIB `HasseWeil` project
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by that roadmap at
`dev/hasse-weil @ 513e83879e2f`), `HasseWeil/Valuation.lean`.

The **proof is not ported**. The source argues directly: it splits on which partial derivative is
nonzero at the point, exhibits a uniformiser in each case, and needs
`set_option maxHeartbeats 3200000` to elaborate the resulting ideal computations, along with the
four supporting theorems of that file (each itself under an `800000` override). None of that is
needed here. Since `TauCeti.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing` gives the
Dedekind property outright, Mathlib's
`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` supplies the conclusion, and
the only remaining side condition is that the ideal is nonzero — which is one of its two span
generators being nonzero, Mathlib's `CoordinateRing.XClass_ne_zero`. The source's hypothesis is
nonsingularity of the point; here the curve equation suffices, matching the weakening already made
for `XYIdeal_isMaximal_of_equation`.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F}

/-- **The ideal `⟨X - x, Y - y(X)⟩` of the coordinate ring is nonzero**: it contains the class of
`X - x`, which is nonzero over a nontrivial base. -/
lemma XYIdeal_ne_bot (x : F) (y : F[X]) : CoordinateRing.XYIdeal W x y ≠ ⊥ := fun hbot => by
  have hmem : CoordinateRing.XClass W x ∈ CoordinateRing.XYIdeal W x y :=
    Ideal.subset_span (Set.mem_insert _ _)
  rw [hbot, Ideal.mem_bot] at hmem
  exact CoordinateRing.XClass_ne_zero x hmem

/-- **The local ring of an elliptic curve at an affine point is a discrete valuation ring.** Stated
for an arbitrary localisation `S` of the coordinate ring at the ideal of the point, so that it
covers `Localization.AtPrime` and any other model of it. The valuation is the order of vanishing at
the point, and a uniformiser generates the maximal ideal. -/
theorem isDiscreteValuationRing_of_isLocalization [W.IsElliptic] {y : F}
    (P : Ideal W.CoordinateRing) [P.IsPrime] (hP : P = CoordinateRing.XYIdeal W x (C y))
    (S : Type*) [CommRing S] [IsDomain S] [Algebra W.CoordinateRing S]
    [IsLocalization.AtPrime S P] :
    IsDiscreteValuationRing S :=
  have := isDedekindDomain_coordinateRing W
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _
    (hP ▸ XYIdeal_ne_bot x (C y)) S

end WeierstrassCurve.Affine.CoordinateRing

end TauCeti

end
