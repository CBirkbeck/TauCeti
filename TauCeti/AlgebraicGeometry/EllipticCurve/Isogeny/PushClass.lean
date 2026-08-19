/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Dedekind
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Finite
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

**Every hypothesis is an argument, and each has a supplier elsewhere.** Nothing among the
declarations below is derived: each takes its instances, so none of them depends on when a supplier
lands. The suppliers live with the object they describe, in the one-property-per-file
`IntermediateRing/` series:

* `[IsDedekindDomain φ.intermediateRing]` — `Isogeny.isDedekindDomain_intermediateRing`, which
  additionally needs separability of the function-field extension. Taking the conclusion keeps
  that condition at the call site and leaves this statement true for any intermediate ring known
  to be Dedekind by another route, so the inseparable case is excluded by whichever lemma
  supplies the instance rather than silently here.
* `[Module.Finite W₂.CoordinateRing φ.intermediateRing]` — `Isogeny.moduleFinite_intermediateRing`.
* the two `[Module.IsTorsionFree …]` — Mathlib's `Module.isTorsionFree_iff_algebraMap_injective`
  applied to the two embeddings `Isogeny.toIntermediateRing_injective` and
  `Isogeny.pullbackToIntermediateRing_injective`. A consumer whose algebra structures are the
  corestricted maps discharges them with
  `Module.isTorsionFree_iff_algebraMap_injective.mpr φ.toIntermediateRing_injective` on the source
  side and the `pullbackToIntermediateRing` analogue on the target side. These are what make
  `ClassGroup.extendedRelNormHom` applicable at all: its variable block requires them.

  **There is deliberately no `Isogeny.isTorsionFree_intermediateRing` to cite.** Named lemmas of
  that shape were written alongside the embeddings and removed there as one-step wrappers of the
  `iff` above: a `theorem` carrying an explicit pointwise hypothesis can never be selected by
  instance search, so it saves a consumer nothing over the one-liner.

This file derives none of these — each is an argument — so it compiles and is correct independently
of when the suppliers land, and the `example` below witnesses that the block is jointly
satisfiable rather than vacuous.

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
  [Algebra W₂.CoordinateRing W₁.FunctionField]
  [Algebra W₂.CoordinateRing φ.intermediateRing]
  [IsScalarTower W₁.CoordinateRing φ.intermediateRing W₁.FunctionField]
  [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
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

omit [Algebra W₂.CoordinateRing W₁.FunctionField]
  [IsScalarTower W₁.CoordinateRing φ.intermediateRing W₁.FunctionField]
  [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField] in
/-- **The composite, unfolded.** This is `ClassGroup.extendedRelNormHom_apply` transported to the
isogeny, and it is what characterises `pushClassMonoidHom` at its own generality.

The pinning hypotheses are `omit`ted: they fix *which* algebra structures the definitions are about,
and this identity holds for whatever structures are in scope, so requiring them here would be a
hypothesis the proof does not use. -/
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

section Instantiable

/-- **The variable block above is jointly satisfiable, and this witnesses it.**

Every instance argument of `pushClassMonoidHom` is an argument rather than a derived fact, which is
what keeps the definitions independent of supplier landing order — but it also means the block is
never checked. A definition whose instance arguments nothing can satisfy elaborates without
complaint and is found to be unusable only when a consumer first tries it.

So the eight are discharged here from declarations that exist. Beyond the block itself this costs
only separability of the function-field extension and the ambient tower on `W₁.FunctionField`: the
integral closedness that the Dedekind and finiteness suppliers ask for is already implied by
`[IsDedekindDomain W₂.CoordinateRing]`, and the two torsion-free halves need nothing but the
embeddings. Producing the map is the whole content — it typechecks only if all eight resolve.

Kept as an `example`: it is a satisfiability check with no downstream consumer, so it should not add
a name to the public namespace. The same device guards
`Analysis/Complex/Conformal/DiscInjection.lean` against a vacuously-true statement. -/
noncomputable example (φ : Isogeny W₁ W₂)
    [IsDomain W₁.CoordinateRing] [IsDedekindDomain W₂.CoordinateRing]
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra.IsSeparable W₂.FunctionField W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    ClassGroup W₁.CoordinateRing →* ClassGroup W₂.CoordinateRing :=
  letI : Algebra W₁.CoordinateRing φ.intermediateRing := φ.toIntermediateRing.toAlgebra
  letI : Algebra W₂.CoordinateRing φ.intermediateRing := φ.pullbackToIntermediateRing.toAlgebra
  haveI : IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField :=
    φ.isScalarTower_intermediateRing rfl h
  haveI := φ.isDedekindDomain_intermediateRing h
  haveI := φ.moduleFinite_intermediateRing h
  haveI : Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr φ.toIntermediateRing_injective
  haveI : Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr φ.pullbackToIntermediateRing_injective
  φ.pushClassMonoidHom

end Instantiable

end Isogeny

end TauCeti
