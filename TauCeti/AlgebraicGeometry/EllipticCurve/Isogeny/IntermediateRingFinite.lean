/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# The intermediate ring is module-finite over the target coordinate ring

For a separable isogeny, `φ.intermediateRing` is a finite `W₂.CoordinateRing`-module. This is the
finiteness that the relative ideal norm — and through it `pushClass` and the induced map on
points — needs.

## The separability hypothesis is real, and the roadmap overstates its absence

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 1, describes the intermediate ring as
"module-finite over `W₂.CoordinateRing` and integrally closed (both proven upstream, Frobenius
included)". **The parenthetical does not hold for module-finiteness.** The upstream proof
(AINTLIB `HasseWeil/Curves/RamificationFinite.lean`, `module_finite`) is
`IsIntegralClosure.finite`, which goes through the trace pairing and carries
`[Algebra.IsSeparable K L]`; its own docstring says "in the separable case". The trace form
degenerates exactly on purely inseparable extensions, so the Frobenius isogeny — the one this
repository has a concrete construction for — is the case *not* covered.

This file therefore proves the separable case and says so, rather than claiming a generality it
does not have. The inseparable case needs a different argument (excellence, or N-2 finiteness for
finitely generated algebras over a field); Mathlib has no separability-free statement to invoke,
which was checked before writing.

## Main results

* `TauCeti.Isogeny.moduleFinite_intermediateRing`: `φ.intermediateRing` is module-finite over
  `W₂.CoordinateRing` when the function-field extension is separable.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The intermediate ring really is the integral closure**, in Mathlib's `IsIntegralClosure`
sense. Both fields are already available: the inclusion of a subring into its ambient field is
injective, and the integrality characterisation is `mem_intermediateRing_iff`.

Stated for an arbitrary `W₂.CoordinateRing`-algebra structure on `W₁.FunctionField` whose
structure map is the pullback, so that a caller's own structure is accepted rather than the
locally-built one that `intermediateRing` is defined against. -/
theorem isIntegralClosure_intermediateRing (φ : Isogeny W₁ W₂)
    [inst : Algebra W₂.CoordinateRing W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    IsIntegralClosure φ.intermediateRing W₂.CoordinateRing W₁.FunctionField := by
  -- the caller's structure and the pullback-induced one agree on the structure map, so they are
  -- literally the same instance; substituting makes `mem_intermediateRing_iff` apply on the nose
  have halg : inst = φ.pullback.toRingHom.toAlgebra := Algebra.algebra_ext _ _ h
  subst halg
  let _ := φ.pullback.toRingHom.toAlgebra
  exact
    { algebraMap_injective := Subtype.val_injective
      isIntegral_iff := fun {x} ↦
        ⟨fun hx ↦ ⟨⟨x, (φ.mem_intermediateRing_iff x).2 hx⟩, rfl⟩,
         fun ⟨y, hy⟩ ↦ hy ▸ (φ.mem_intermediateRing_iff _).1 y.2⟩ }

/-- **The intermediate ring is module-finite over the target coordinate ring**, for a separable
isogeny of elliptic curves.

Stated for arbitrary algebra structures whose structure maps are the pullback, rather than for one
fixed choice, matching `Isogeny.degree_eq_finrank`: registering such structures globally would
create a diamond, since different isogenies induce different ones.

Separability is a genuine hypothesis, not an artefact — see the module docstring. -/
theorem moduleFinite_intermediateRing (φ : Isogeny W₁ W₂) [W₂.IsElliptic]
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    [FiniteDimensional W₂.FunctionField W₁.FunctionField]
    [Algebra.IsSeparable W₂.FunctionField W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Module.Finite W₂.CoordinateRing φ.intermediateRing := by
  -- the integral-closure property is not assumed: it is what `intermediateRing` is
  have := φ.isIntegralClosure_intermediateRing h
  -- `IsIntegralClosure.finite` wants the base normal; that is the seeded smoothness milestone
  have := WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing W₂
  exact IsIntegralClosure.finite W₂.CoordinateRing W₂.FunctionField W₁.FunctionField
    φ.intermediateRing

end Isogeny

end TauCeti
