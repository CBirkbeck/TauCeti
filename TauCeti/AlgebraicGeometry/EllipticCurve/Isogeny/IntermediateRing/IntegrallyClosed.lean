/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The intermediate ring is integrally closed

For an isogeny `φ : Isogeny W₁ W₂`, the intermediate ring — the integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField` — is itself integrally closed. With
`Isogeny.moduleFinite_intermediateRing` this is the normality half of what the relative ideal norm
needs, and through it `pushClass` and the induced map on points.

**No finiteness is involved.** An integral closure is integrally closed in the ambient ring for the
formal reason that integrality is transitive: an element of `W₁.FunctionField` integral over the
closure is integral over `W₂.CoordinateRing`, hence already in it. Since `W₁.FunctionField` is a
field, being integrally closed *in* it upgrades to `IsIntegrallyClosed`
(`IsIntegrallyClosed.of_isIntegrallyClosedIn`). In particular this holds for **inseparable**
isogenies, Frobenius included, and does not inherit the separability hypothesis that the sibling
`Isogeny.moduleFinite_intermediateRing` carries for want of a trace-free route to finiteness.

## Main results

* `TauCeti.Isogeny.isIntegrallyClosed_intermediateRing`: `φ.intermediateRing` is integrally closed.

## Design

The hypotheses are those needed to *name* the integral closure, not to prove it normal. `h` fixes
the `W₂.CoordinateRing`-algebra structure on `W₁.FunctionField` as the pullback, which is what
`Isogeny.isIntegralClosure_intermediateRing` needs; the algebra structure on `φ.intermediateRing`
and its scalar tower are what let integrality transit through it. A consumer builds both from the
bundled `φ.pullbackToIntermediateRing` — `letI := φ.pullbackToIntermediateRing.toAlgebra` — together
with `Isogeny.isScalarTower_intermediateRing`, exactly as for the finiteness result.

**Why not hypothesis-free.** The statement itself mentions no algebra structure, and mathematically
it needs none: `intermediateRing` builds its own internally, and Mathlib's
`IsIntegrallyClosedIn (integralClosure R A).toSubring A` is an unconditional instance. That instance
cannot be used here, because `intermediateRing`'s body is not exposed across the module boundary —
`Basic.lean` says so and offers `mem_intermediateRing_iff` as the escape hatch — so synthesis cannot
see the two objects coincide. Every route from this module to the integral-closure property runs
through `Isogeny.isIntegralClosure_intermediateRing`, which takes `h`. Removing the remaining
hypotheses is therefore a change to `Basic.lean`'s exposed surface, not to this file.

## Provenance

⚠ *mathlib-track*. `TauCetiRoadmap/EllipticCurves/README.md:1092` lists
`intermediateRingIsIntegrallyClosed` among the components of D. Angdinata's shared isogeny
development, under the same flag the sibling `Isogeny` files carry.

The result is also proved in the AINTLIB project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, by
Chris Birkbeck), though not separately: `HasseWeil/Curves/RamificationFinite.lean` proves
`instDedekindB` for `B := integralClosure C₂.CoordinateRing C₁.FunctionField`, the same object this
file calls `φ.intermediateRing`, and a Dedekind domain is integrally closed. What is built here
rather than taken from there is the reduction to `intermediateRing` as this repository defines it,
through the corestricted pullback, and the statement of normality on its own rather than as a
by-product of the Dedekind instance — which is what lets it hold without the finiteness that
instance carries.

The proof route — transitivity of integrality, then
`IsIntegrallyClosed.of_isIntegrallyClosedIn` — is assembled from Mathlib and is not the source's.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The intermediate ring is integrally closed.** It is the integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField`, and an integral closure is integrally closed in the
ambient ring by transitivity of integrality; over a field that upgrades to `IsIntegrallyClosed`.

No finiteness and no separability: unlike the sibling `Isogeny.moduleFinite_intermediateRing` this
covers inseparable isogenies, Frobenius included. -/
theorem isIntegrallyClosed_intermediateRing (φ : Isogeny W₁ W₂)
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    IsIntegrallyClosed φ.intermediateRing := by
  -- the integral-closure property is not assumed: it is what `intermediateRing` is
  have := φ.isIntegralClosure_intermediateRing h
  have : Algebra.IsIntegral W₂.CoordinateRing φ.intermediateRing :=
    IsIntegralClosure.isIntegral_algebra W₂.CoordinateRing W₁.FunctionField
  have : IsIntegrallyClosedIn φ.intermediateRing W₁.FunctionField := by
    rw [isIntegrallyClosedIn_iff]
    refine ⟨FaithfulSMul.algebraMap_injective _ _, fun {x} hx ↦ ?_⟩
    -- `x` is integral over the closure, hence over `W₂.CoordinateRing`, hence already in it
    exact (IsIntegralClosure.isIntegral_iff (A := φ.intermediateRing)).mp
      (isIntegral_trans (R := W₂.CoordinateRing) x hx)
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn _ W₁.FunctionField

end Isogeny

end TauCeti
