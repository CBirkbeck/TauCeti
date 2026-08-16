/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# The intermediate ring is a Dedekind domain

For an isogeny `φ : Isogeny W₁ W₂`, the intermediate ring — the integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField` — is a Dedekind domain whenever the target's coordinate
ring is one and the extension of function fields is separable.

This is what the relative ideal norm asks of the *middle* ring: `ClassGroup.relNorm`, and through
it `ClassGroup.extendedRelNormHom`, is stated over a module-finite extension of Dedekind domains,
so `Isogeny.pushClass` needs `φ.intermediateRing` to be Dedekind and not merely normal.

## Main results

* `TauCeti.Isogeny.isDedekindDomain_intermediateRing`: `φ.intermediateRing` is a Dedekind domain.

## Design

**Why this is separate from `IntegrallyClosed.lean`, and why it costs more.**
`Isogeny.isIntegrallyClosed_intermediateRing` is hypothesis-free: an integral closure is integrally
closed because integral closure is idempotent, and that argument sees no trace form. Being
*Dedekind* is a conjunction — integrally closed, Noetherian, dimension at most one — and the
Noetherian half is where the cost enters. Mathlib's route, `IsIntegralClosure.isDedekindDomain`,
is stated for a finite **separable** extension of the fraction field, because it obtains
Noetherianity from the trace pairing, which is nondegenerate exactly in the separable case.

So the hypothesis set here matches the sibling `Isogeny.moduleFinite_intermediateRing` rather than
`Isogeny.isIntegrallyClosed_intermediateRing`, and for the same reason: both go through the trace.
In particular this statement does **not** cover inseparable isogenies, Frobenius included, whereas
the normality of the same ring does. That asymmetry is real rather than an artefact of the route
taken — see `IntermediateRing/Finite.lean`, which flags the general case as separate work.

`IsDedekindDomain W₂.CoordinateRing` is taken as a hypothesis rather than derived. For an elliptic
curve it is supplied by `WeierstrassCurve.Affine.isDedekindDomain_coordinateRing`, which needs
`[W₂.IsElliptic]`; taking the Dedekind property directly keeps that ellipticity out of this file,
exactly as the sibling takes `[IsIntegrallyClosed W₂.CoordinateRing]` rather than assuming a curve.

## Provenance

⚠ *mathlib-track*. `TauCetiRoadmap/EllipticCurves/README.md:1092` lists the `IntermediateRing`
with `intermediateRingFinite` and `intermediateRingIsIntegrallyClosed` among the components of
D. Angdinata's shared isogeny development, on the way to `pushClass` and `toPointHom`; the Dedekind
property is what those two facts are combined for.

AINTLIB proves the same statement about the same object as
`NormConormIntegralClosure.instDedekindB` (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`HasseWeil/Curves/NormConormIntegralClosure.lean`, by Chris Birkbeck), for
`B := integralClosure C₂.CoordinateRing C₁.FunctionField`. What is adapted here is the reduction to
`intermediateRing` as this repository defines it — through the corestricted pullback and
`Isogeny.isIntegralClosure_intermediateRing` — rather than to Mathlib's literal `integralClosure`
subalgebra.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The intermediate ring is a Dedekind domain.** It is the integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField`, and the integral closure of a Dedekind domain in a
finite separable extension of its fraction field is again Dedekind.

Separability is genuinely needed, unlike for `Isogeny.isIntegrallyClosed_intermediateRing`: the
Noetherian half of the conjunction comes from the trace pairing. -/
theorem isDedekindDomain_intermediateRing (φ : Isogeny W₁ W₂)
    [IsDedekindDomain W₂.CoordinateRing]
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    [Algebra.IsSeparable W₂.FunctionField W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    IsDedekindDomain φ.intermediateRing := by
  -- the integral-closure property is not assumed: it is what `intermediateRing` is
  have := φ.isIntegralClosure_intermediateRing h
  have := φ.finiteDimensional_functionField (φ.algebraMap_functionField_eq_fieldPullback h)
  exact IsIntegralClosure.isDedekindDomain W₂.CoordinateRing W₂.FunctionField W₁.FunctionField
    φ.intermediateRing

end Isogeny

end TauCeti
