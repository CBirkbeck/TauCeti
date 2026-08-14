/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic

/-!
# The intermediate ring of an isogeny

The integral closure of the target coordinate ring inside the source function field, taken along
an isogeny's pullback. This is the normalization that `CoordinatePullback.MapsInfinity` names,
and it receives both coordinate rings: the target's through the pullback, and the source's
because `mapsInfinity` is precisely the assertion that it lands there.

## Main definitions

* `TauCeti.Isogeny.intermediateRing`: the integral closure of `W₂.CoordinateRing` in
  `W₁.FunctionField` along `φ.pullback`.

## Main results

* `TauCeti.Isogeny.algebraMap_mem_intermediateRing`: the source coordinate ring lands in it.
* `TauCeti.Isogeny.pullback_mem_intermediateRing`: so does the target coordinate ring.
* `TauCeti.Isogeny.id_intermediateRing`: the identity isogeny's intermediate ring is the
  coordinate ring itself, sitting inside its own fraction field.

## Design

The result is a `Subring W₁.FunctionField`, not a `Subalgebra`. The algebra structure that
`φ.pullback` induces on `W₁.FunctionField` is deliberately not a global instance — different
isogenies induce different ones, so registering any would be a diamond, as `Isogeny/Basic.lean`
explains. A `Subalgebra` would put that structure into the *type*, forcing every statement about
the object to fix a choice of it; a `Subring` keeps it inside the definition, exactly where
`MapsInfinity` already keeps it.

Nothing here assumes separability, so purely inseparable isogenies such as Frobenius are covered.

The structural theory of this ring — module-finiteness over `W₂.CoordinateRing`, and its being a
Dedekind domain — is deliberately not proved here. Every route to it in Mathlib
(`IsIntegralClosure.finite`, `integralClosure.isDedekindDomain`) carries an
`Algebra.IsSeparable` hypothesis, so the inseparable case that this roadmap wants is separate
work rather than a corollary of the definition.

This opens the "points come along" milestone of Layer 1 of
`TauCetiRoadmap/EllipticCurves/README.md`, which names this object as "the **intermediate ring**
— the integral closure of `W₂.CoordinateRing` in `W₁.FunctionField`, the normalization
`mapsInfinity` names", receiving both coordinate rings on the way to `pushClass` and
`toPointHom`. It follows Silverman, *The Arithmetic of Elliptic Curves*, II.2.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The intermediate ring of an isogeny**: the integral closure of the target coordinate ring
inside the source function field, along the isogeny's pullback. -/
noncomputable def intermediateRing (φ : Isogeny W₁ W₂) : Subring W₁.FunctionField :=
  letI := φ.pullback.toRingHom.toAlgebra
  (integralClosure W₂.CoordinateRing W₁.FunctionField).toSubring

/-- Membership in the intermediate ring is integrality over the target coordinate ring acting
through the pullback. The definition's body is not exposed across the module boundary, so this
is how downstream modules compute with it. -/
theorem mem_intermediateRing_iff (φ : Isogeny W₁ W₂) (z : W₁.FunctionField) :
    z ∈ φ.intermediateRing ↔
      @IsIntegral W₂.CoordinateRing W₁.FunctionField _ _ φ.pullback.toRingHom.toAlgebra z :=
  Iff.rfl

/-- **The source coordinate ring lands in the intermediate ring.** This is `mapsInfinity` read
as a statement about that ring: pointedness of the isogeny says exactly that the source
coordinates are integral over the pulled-back target coordinate ring. -/
theorem algebraMap_mem_intermediateRing (φ : Isogeny W₁ W₂) (x : W₁.CoordinateRing) :
    algebraMap W₁.CoordinateRing W₁.FunctionField x ∈ φ.intermediateRing :=
  (CoordinatePullback.mapsInfinity_iff φ.pullback).1 φ.mapsInfinity x

/-- **The target coordinate ring lands in the intermediate ring**, through the pullback: each
element of the image is integral over the ring it is the image of. -/
theorem pullback_mem_intermediateRing (φ : Isogeny W₁ W₂) (x : W₂.CoordinateRing) :
    φ.pullback x ∈ φ.intermediateRing :=
  letI := φ.pullback.toRingHom.toAlgebra
  isIntegral_algebraMap

/-- **The identity isogeny's intermediate ring is the coordinate ring itself**, embedded in its
own fraction field: the coordinate ring of an elliptic curve is integrally closed, so nothing in
the function field beyond it is integral over it. -/
theorem id_intermediateRing (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    (id W).intermediateRing = (algebraMap W.CoordinateRing W.FunctionField).range := by
  have := WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing W
  -- the identity pullback induces the coordinate ring's own algebra structure on the function
  -- field, so the integral closure below is the ordinary one
  have halg : (CoordinatePullback.id W).toRingHom.toAlgebra =
      (inferInstance : Algebra W.CoordinateRing W.FunctionField) := by
    apply Algebra.algebra_ext
    intro x
    rw [RingHom.algebraMap_toAlgebra]
    exact CoordinatePullback.id_apply W x
  ext z
  rw [mem_intermediateRing_iff, RingHom.mem_range, id_pullback, halg]
  constructor
  · intro hz
    have hbot : z ∈ integralClosure W.CoordinateRing W.FunctionField := hz
    rw [IsIntegrallyClosed.integralClosure_eq_bot] at hbot
    exact Algebra.mem_bot.1 hbot
  · rintro ⟨x, rfl⟩
    exact isIntegral_algebraMap

end Isogeny

end TauCeti
