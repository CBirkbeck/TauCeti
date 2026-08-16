/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import TauCeti.RingTheory.ClassGroup.ExtendedRelNorm

/-!
# The class-group map induced by an isogeny

For an isogeny `φ : Isogeny W₁ W₂`, extending an ideal of `W₁.CoordinateRing` into the
intermediate ring and taking the relative norm down to `W₂.CoordinateRing` gives a homomorphism
of class groups.

## Main definitions

* `TauCeti.Isogeny.pushClassMonoidHom`: the multiplicative form,
  `ClassGroup W₁.CoordinateRing →* ClassGroup W₂.CoordinateRing`.
* `TauCeti.Isogeny.pushClass`: the same map written additively, which is the form the point
  group consumes.

## Main results

* `TauCeti.Isogeny.pushClassMonoidHom_apply`: the composite unfolded, as extension followed by
  relative norm.

## Design

**The instance arguments are explicit, and deliberately so.** `Isogeny.intermediateRing` is a
`Subring W₁.FunctionField` carrying no `Algebra` instance over either coordinate ring —
`IntermediateRing/Basic.lean` records that an instance would reintroduce a diamond — so every
statement about it takes the algebra structures as arguments. This file follows the shape the
`IntermediateRing/` series already uses rather than inventing a second convention.

**Every hypothesis is an argument, and each has a supplier elsewhere.** Nothing here is derived,
so this file imports only what its *statements* mention — `IntermediateRing/Basic` for
`intermediateRing` itself, and `ClassGroup/ExtendedRelNorm` for the composite. The suppliers live
with the object they describe, in the one-property-per-file `IntermediateRing/` series, and this
file is independent of all of them: it neither imports nor calls any:

* `[IsDedekindDomain φ.intermediateRing]` — `Isogeny.isDedekindDomain_intermediateRing`, which
  additionally needs separability of the function-field extension. Taking the conclusion keeps
  that condition at the call site and leaves this statement true for any intermediate ring known
  to be Dedekind by another route, so the inseparable case is excluded by whichever lemma
  supplies the instance rather than silently here.
* `[Module.Finite W₂.CoordinateRing φ.intermediateRing]` — `Isogeny.moduleFinite_intermediateRing`.
* the two `[Module.IsTorsionFree …]` — `Isogeny.isTorsionFree_intermediateRing_source` and
  `_target`. Those are what make `ClassGroup.extendedRelNormHom` applicable at all: its variable
  block requires them, and until they existed the composite could be stated but never
  instantiated.

This file derives none of the three — each is an argument — so it compiles and is correct
independently of when the suppliers land, and becomes instantiable exactly when all three are
available together.

`ClassGroup.extendedRelNormHom` orders its rings `A M R` — source, middle, target — so the
instantiation is `A := W₁.CoordinateRing`, `M := φ.intermediateRing`, `R := W₂.CoordinateRing`.

## Provenance

⚠ *mathlib-track*. `TauCetiRoadmap/EllipticCurves/README.md:1092` lists `pushClass` "by ideal
extension and relative norm (`ClassGroup.extendedRelNormHom`)" among the components of
D. Angdinata's shared isogeny development, on the way to `toPointHom`.

Adapted from that development's `Isogeny.lean` (Apache-2.0, by David Kurniadi Angdinata),
declarations `pushClassMonoidHom` and `pushClass`. Two adaptations are forced by how this
repository states the surrounding API:

* the source writes `ClassGroup.extendedRelNormHom W₂.CoordinateRing W₁.CoordinateRing
  f.IntermediateRing`, ordering the rings target-source-middle; `TauCeti.ClassGroup`'s own
  `extendedRelNormHom` orders them source-middle-target, so the arguments are permuted here;
* the source obtains its algebra structures from a `letI := f.pullback.coordinateRingAlgebra`
  inside each proof, whereas `intermediateRing` here carries no such instance by design, so they
  are explicit arguments instead.

The source's `pushFractionalIdeal` and `pushClassMonoidHom_mk` are **not** ported. They are
stated through `ClassGroup.normIntegralUnitIdeal` and `ClassGroup.integralUnitIdealRep`, an
integral-representative API for fractional-ideal units that this repository does not have;
`ExtendedRelNorm.lean` instead characterises the composite by `extendedRelNormHom_apply` and, on
integral ideals, `extendedRelNormHom_mk0`. `pushClassMonoidHom_apply` below is the corresponding
characterisation, so nothing the two `_mk` lemmas were for is lost.
-/

public section

namespace TauCeti

namespace Isogeny

open scoped nonZeroDivisors

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

section PushClass

variable (φ : Isogeny W₁ W₂)
  [IsDomain W₁.CoordinateRing] [IsDedekindDomain W₂.CoordinateRing]
  [Algebra W₁.CoordinateRing φ.intermediateRing]
  [Algebra W₂.CoordinateRing φ.intermediateRing]
  [IsDedekindDomain φ.intermediateRing]
  [Module.Finite W₂.CoordinateRing φ.intermediateRing]
  [Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing]
  [Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing]

/-- **The class-group map induced by an isogeny**, multiplicatively: extend a class of
`W₁.CoordinateRing` into the intermediate ring, then norm it down to `W₂.CoordinateRing`.

The two coordinate rings carry no map between them; the intermediate ring is what connects
them, receiving `W₁.CoordinateRing` by inclusion and lying module-finite over
`W₂.CoordinateRing`. -/
noncomputable def pushClassMonoidHom :
    ClassGroup W₁.CoordinateRing →* ClassGroup W₂.CoordinateRing :=
  ClassGroup.extendedRelNormHom W₁.CoordinateRing φ.intermediateRing W₂.CoordinateRing

/-- **The composite, unfolded.** This is `ClassGroup.extendedRelNormHom_apply` transported to the
isogeny, and it is what characterises `pushClassMonoidHom` at its own generality. -/
theorem pushClassMonoidHom_apply (x : ClassGroup W₁.CoordinateRing) :
    φ.pushClassMonoidHom x =
      ClassGroup.relNorm (ClassGroup.extendedHom W₁.CoordinateRing φ.intermediateRing x) :=
  ClassGroup.extendedRelNormHom_apply W₁.CoordinateRing φ.intermediateRing W₂.CoordinateRing x

/-- **The additive form of `Isogeny.pushClassMonoidHom`.** The point group is described additively
by its class group, so this is the shape the induced map on points is built from. -/
noncomputable def pushClass :
    Additive (ClassGroup W₁.CoordinateRing) →+ Additive (ClassGroup W₂.CoordinateRing) :=
  MonoidHom.toAdditive φ.pushClassMonoidHom

end PushClass

end Isogeny

end TauCeti
