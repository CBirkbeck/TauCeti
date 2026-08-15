/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The intermediate ring is integrally closed

For an isogeny `φ : Isogeny W₁ W₂`, the intermediate ring — the integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField` — is itself integrally closed. Together with
module-finiteness (`Isogeny.moduleFinite_intermediateRing`) this is the normality half of what the
relative ideal norm needs, and through it `pushClass` and the induced map on points.

**This costs strictly less than the finiteness half.** `Isogeny.moduleFinite_intermediateRing`
carries `[Algebra.IsSeparable W₂.FunctionField W₁.FunctionField]` because its only upstream route,
`IsIntegralClosure.finite`, argues through the trace pairing. Nothing here does: an integral closure
inside a finite field extension is integrally closed for the formal reason that integral closure is
idempotent. So this statement holds for **inseparable** isogenies too, Frobenius included, and does
not inherit the sibling's limitation.

## Main results

* `TauCeti.Isogeny.isIntegrallyClosed_intermediateRing`: `φ.intermediateRing` is integrally closed.

## Design

The hypotheses mirror `Isogeny.moduleFinite_intermediateRing` — arbitrary algebra structures whose
structure maps are the pullback, rather than one fixed choice, since registering such a structure
globally would be a diamond. A consumer builds them from the bundled `φ.pullbackToIntermediateRing`
(`letI := φ.pullbackToIntermediateRing.toAlgebra`) together with
`Isogeny.isScalarTower_intermediateRing`, exactly as for the finiteness result.

Two hypotheses of the sibling are **absent** rather than merely unused, and the difference is the
point of this file: `[Algebra.IsSeparable W₂.FunctionField W₁.FunctionField]` and
`[IsIntegrallyClosed W₂.CoordinateRing]`. Integral closedness of the base is not needed because the
conclusion is about the closure, not about the base:
`integralClosure.isIntegrallyClosedOfFiniteExtension` asks only that the base be a domain with
`W₂.FunctionField` as its fraction field.

## Provenance

Original work against Mathlib's `integralClosure.isIntegrallyClosedOfFiniteExtension` and this
repository's `Isogeny.isIntegralClosure_intermediateRing`. The transfer from Mathlib's literal
`integralClosure` subalgebra to `φ.intermediateRing` goes through `IsIntegralClosure.equiv`, the
standard way two integral closures of the same base in the same field are identified.

AINTLIB's `HasseWeil/Curves/RamificationFinite.lean` (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`dev/hasse-weil @ 513e83879e2f`) — the source of the sibling `moduleFinite_intermediateRing` —
proves the finiteness half only; it *assumes* normality of the closure where it needs it rather
than deriving it, so this statement is not a port of anything there.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The intermediate ring is integrally closed.** It is the integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField`, and an integral closure inside a finite extension of the
base's fraction field is integrally closed.

Unlike the sibling `Isogeny.moduleFinite_intermediateRing`, this needs neither separability of the
function-field extension nor integral closedness of `W₂.CoordinateRing` — see the module
docstring. -/
theorem isIntegrallyClosed_intermediateRing (φ : Isogeny W₁ W₂)
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    IsIntegrallyClosed φ.intermediateRing := by
  -- the integral-closure property is not assumed: it is what `intermediateRing` is
  have := φ.isIntegralClosure_intermediateRing h
  have := φ.finiteDimensional_functionField (φ.algebraMap_functionField_eq_fieldPullback h)
  have hclosure : IsIntegrallyClosed (integralClosure W₂.CoordinateRing W₁.FunctionField) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension W₂.FunctionField
  exact IsIntegrallyClosed.of_equiv
    (IsIntegralClosure.equiv W₂.CoordinateRing
      (integralClosure W₂.CoordinateRing W₁.FunctionField) W₁.FunctionField
      φ.intermediateRing).toRingEquiv

end Isogeny

end TauCeti
