/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
-- Proof-only: Noether's finiteness theorem for integral closures.
import TauCeti.RingTheory.IntegralClosure.NormalizationFinite

/-!
# The intermediate ring is module-finite over the target coordinate ring

For an isogeny with separable function-field extension and integrally closed target coordinate
ring, `φ.intermediateRing` is a finite `W₂.CoordinateRing`-module. This is the finiteness that the
relative ideal norm — and through it `pushClass` and the induced map on points — needs.

**Separability is a limitation of the available proof, not of the result.** The statement is
expected to hold without it: `W₂.CoordinateRing` is a finitely generated domain over `F` and
`W₁.FunctionField` is finite over `W₂.FunctionField`, so Noether's finiteness theorem gives
module-finiteness of the integral closure, Frobenius included. What forces the hypothesis here is
that the only route Mathlib provides is `IsIntegralClosure.finite`, whose section carries
`[Algebra.IsSeparable K L]` because it argues through the trace pairing, and the trace form is
nondegenerate exactly for separable extensions. The general case needs a different argument —
excellence, or N-2 finiteness for finitely generated algebras over a field — which is not available
upstream and is left as separate work.

## Main results

* `TauCeti.Isogeny.moduleFinite_intermediateRing`: `φ.intermediateRing` is module-finite over
  `W₂.CoordinateRing`, for an integrally closed `W₂.CoordinateRing` and separable function-field
  extension.

## Design

The result is stated for arbitrary algebra structures whose structure maps are the pullback,
matching `Isogeny.degree_eq_finrank`, rather than for one fixed choice: registering such a
structure globally would be a diamond, since different isogenies induce different ones. A consumer
produces the `W₂.CoordinateRing`-structure on the intermediate ring from the bundled
`φ.pullbackToIntermediateRing` — `letI := φ.pullbackToIntermediateRing.toAlgebra` — which is why
`IntermediateRing/Basic.lean` corestricts the pullback rather than registering an instance.

That `letI` supplies the `Algebra` but not the `IsScalarTower` this theorem also takes, so it is
not by itself the whole setup. `Isogeny.isScalarTower_intermediateRing` supplies the tower from the
same corestriction, and the two together are what a caller needs.

## Provenance

The statement and the proof route — `IsIntegralClosure.finite` against a normal base — are those of
`module_finite` in AINTLIB's `HasseWeil/Curves/RamificationFinite.lean`
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `dev/hasse-weil @ 513e83879e2f`); that file's header
reads `Authors: Chris Birkbeck`, credited here rather than in the copyright header, following this
repository's convention for adapted material and matching `IntermediateRing/Basic.lean`. The source
*assumes* the integral-closure property that `isIntegralClosure_intermediateRing` proves, and
assumes the finite-dimensionality that `Isogeny.finiteDimensional_functionField` derives.

⚠ *mathlib-track*. `TauCetiRoadmap/EllipticCurves/README.md` also pins D. Angdinata's shared
isogeny development as carrying both the function-field form of `finiteDimensional` and the
intermediate ring with its finiteness, under the same flag the sibling `Isogeny` files carry. What
is built here rather than taken from either source is the reduction to `intermediateRing` as this
repository defines it, through the corestricted pullback.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

-- Skeleton of the normalization-finiteness development: `sorry` is an error under the library's
-- `warningAsError`, so it is downgraded here until the proofs land. Remove with the last `sorry`.
set_option warningAsError false

/-- **The intermediate ring is module-finite over the target coordinate ring.** Source: Noether's
finiteness theorem, `TauCeti.IsIntegralClosure.finite_of_finiteType`, applied to the finite-type
`F`-domain `W₂.CoordinateRing` and the finite extension `W₁.FunctionField / W₂.FunctionField`;
no separability of the function-field extension is needed.

Integral closedness of `W₂.CoordinateRing` is what the proof spends, so it is assumed directly
rather than through `[W₂.IsElliptic]`, matching the sibling `id_intermediateRing`; for an elliptic
curve it is discharged by `WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing`. -/
theorem moduleFinite_intermediateRing (φ : Isogeny W₁ W₂)
    [IsIntegrallyClosed W₂.CoordinateRing]
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Module.Finite W₂.CoordinateRing φ.intermediateRing := by
  sorry

end Isogeny

end TauCeti
