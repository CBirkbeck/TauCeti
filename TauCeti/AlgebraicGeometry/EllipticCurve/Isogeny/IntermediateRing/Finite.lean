/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# The intermediate ring is module-finite over the target coordinate ring

For a separable isogeny, `φ.intermediateRing` is a finite `W₂.CoordinateRing`-module. This is the
finiteness that the relative ideal norm — and through it `pushClass` and the induced map on
points — needs.

Separability is a genuine hypothesis rather than an artefact of the proof: the only route
available is `IsIntegralClosure.finite`, which goes through the trace pairing, and the trace form
degenerates exactly on purely inseparable extensions. The Frobenius isogeny is therefore *not*
covered, and this file does not claim it. `IntermediateRing/Basic.lean`, which defines the object
and proves it is the integral closure, assumes no separability and does cover Frobenius.

## Main results

* `TauCeti.Isogeny.finiteDimensional_functionField`: the function-field extension an isogeny
  induces is finite. This is `Isogeny.finiteDimensional` transported off the field range, and is
  what makes the finiteness below hypothesis-free in that respect.
* `TauCeti.Isogeny.moduleFinite_intermediateRing`: `φ.intermediateRing` is module-finite over
  `W₂.CoordinateRing` when the function-field extension is separable.

## Design

Both results are stated for arbitrary algebra structures whose structure maps are the pullback,
matching `Isogeny.degree_eq_finrank`, rather than for one fixed choice: registering such a
structure globally would be a diamond, since different isogenies induce different ones. A
consumer produces the `W₂.CoordinateRing`-structure on the intermediate ring from the bundled
`φ.pullbackToIntermediateRing` — `letI := φ.pullbackToIntermediateRing.toAlgebra` — which is why
`IntermediateRing/Basic.lean` corestricts the pullback rather than registering an instance.

## Provenance

The statement and the proof route — `IsIntegralClosure.finite` against a normal base — are those
of AINTLIB's `module_finite` (`HasseWeil/Curves/RamificationFinite.lean`), Apache 2.0,
`dev/hasse-weil @ 513e83879e2f`. The object it is stated about came from the same source in
#3306. What is not taken from there: that file *assumes* the integral-closure property, which
`isIntegralClosure_intermediateRing` proves, and it assumes the finite-dimensionality that
`finiteDimensional_functionField` derives here.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **An isogeny's function-field extension is finite.**

`Isogeny.finiteDimensional` gives this over `φ.fieldPullback.fieldRange`; this transports it to
any `W₂.FunctionField`-structure whose structure map is the pullback, which is the form consumers
state things in. Nothing needs to be assumed: the degree is positive for every isogeny, and it is
the relevant `finrank`.

The hypothesis is at the coordinate-ring level because that is what callers already hold; the
function-field statement it needs is forced, since `W₂.FunctionField` is a fraction field of
`W₂.CoordinateRing` and a map out of it is determined by its restriction. -/
theorem finiteDimensional_functionField (φ : Isogeny W₁ W₂)
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    FiniteDimensional W₂.FunctionField W₁.FunctionField := by
  have hfield : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z := by
    have hr : (algebraMap W₂.FunctionField W₁.FunctionField)
        = (φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField) :=
      IsFractionRing.ringHom_ext (A := W₂.CoordinateRing) fun x ↦ by
        rw [← IsScalarTower.algebraMap_apply, h]
        exact (φ.fieldPullback_algebraMap x).symm
    exact fun z ↦ congrFun (congrArg DFunLike.coe hr) z
  exact FiniteDimensional.of_finrank_pos (φ.degree_eq_finrank hfield ▸ φ.degree_pos)

/-- **The intermediate ring is module-finite over the target coordinate ring**, for a separable
isogeny.

Integral closedness of `W₂.CoordinateRing` is what the proof actually spends, so it is assumed
directly rather than through `[W₂.IsElliptic]`, matching the sibling `id_intermediateRing`; for an
elliptic curve it is discharged by
`WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing`.

Separability is a genuine hypothesis — see the module docstring. -/
theorem moduleFinite_intermediateRing (φ : Isogeny W₁ W₂)
    [IsIntegrallyClosed W₂.CoordinateRing]
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    [Algebra.IsSeparable W₂.FunctionField W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Module.Finite W₂.CoordinateRing φ.intermediateRing := by
  -- the integral-closure property is not assumed: it is what `intermediateRing` is
  have := φ.isIntegralClosure_intermediateRing h
  have := φ.finiteDimensional_functionField h
  exact IsIntegralClosure.finite W₂.CoordinateRing W₂.FunctionField W₁.FunctionField
    φ.intermediateRing

end Isogeny

end TauCeti
