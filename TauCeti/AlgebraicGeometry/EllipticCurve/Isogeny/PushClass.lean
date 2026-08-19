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

**Open: the two `Algebra` arguments are not tied to `φ`.** Nothing forces them to be
`toIntermediateRing` and `pullbackToIntermediateRing`, so the declarations below are a family
indexed by the caller's choice of structure rather than *the* map induced by the isogeny. For
`φ = Isogeny.id W`, precomposing either structure with a nontrivial `F`-automorphism of
`W.CoordinateRing` satisfies every argument above — injectivity, finiteness and Dedekindness are
all automorphism-stable — and yields a different map, so `(Isogeny.id W).pushClass` need not be
the identity. Any functoriality statement, and `toPointHom`, will need this closed first.

The obvious repair does not work here: adding `[IsScalarTower …]` arguments to constrain the
structures makes them *unused* arguments of a definition whose body never mentions them, and
`lint-env`'s `unusedArguments` linter rejects that as a new violation — the escape hatches are a
`@[nolint]` plus an allowlist line under `scripts/`, which is not a fix. Closing this properly means
building the structures inside the definition from the corestricted maps rather than accepting them,
which changes what the declaration asks of a caller and is left for review to weigh.

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
integral ideals, `extendedRelNormHom_mk0`.

**No transported characterisation is offered here, deliberately.** The algebra structures are built
inside the definitions below rather than accepted from the caller, which is what makes them *the*
isogeny's maps; but it also means a characterisation lemma cannot name those structures — a `letI`
in a statement builds different terms, and `ClassGroup.relNorm` and `ClassGroup.extendedRelNormHom`
are
unexposed, so nothing reconciles them. The first real consumer (`toPointHom`) should decide what
characterisation it needs and in what form, rather than this file guessing.
-/

public section

namespace TauCeti

namespace Isogeny

open scoped nonZeroDivisors

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

section PushClass

variable (φ : Isogeny W₁ W₂)
  [IsDomain W₁.CoordinateRing] [IsDedekindDomain W₂.CoordinateRing]
  [Algebra W₂.CoordinateRing W₁.FunctionField]
  [Algebra W₂.FunctionField W₁.FunctionField]
  [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
  [Algebra.IsSeparable W₂.FunctionField W₁.FunctionField]

/-- **The class-group map induced by an isogeny**, multiplicatively: extend a class of
`W₁.CoordinateRing` into the intermediate ring, then norm it down to `W₂.CoordinateRing`.

The two coordinate rings carry no map between them; the intermediate ring is what connects
them, receiving `W₁.CoordinateRing` by inclusion and lying module-finite over
`W₂.CoordinateRing`. -/
noncomputable def pushClassMonoidHom
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
  ClassGroup.extendedRelNormHom W₁.CoordinateRing φ.intermediateRing W₂.CoordinateRing

/-- **The additive form of `Isogeny.pushClassMonoidHom`.** The point group is described additively
by its class group, so this is the shape the induced map on points is built from. -/
noncomputable def pushClass
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Additive (ClassGroup W₁.CoordinateRing) →+ Additive (ClassGroup W₂.CoordinateRing) :=
  MonoidHom.toAdditive (φ.pushClassMonoidHom h)

end PushClass

section Instantiable

/-- **The definitions' hypotheses are satisfiable.** The algebra structures are no longer a
caller's choice — `pushClassMonoidHom` builds them from `φ` — so what remains to witness is that
the pinning hypothesis `h` can be met at all. It is met by construction whenever the ambient
`W₂.CoordinateRing`-algebra structure on `W₁.FunctionField` is the pullback's own.

Kept as an `example`: a satisfiability check with no downstream consumer, as in
`Analysis/Complex/Conformal/DiscInjection.lean`. -/
example (φ : Isogeny W₁ W₂) :
    letI : Algebra W₂.CoordinateRing W₁.FunctionField := φ.pullback.toRingHom.toAlgebra
    ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x :=
  fun x ↦ RingHom.congr_fun (RingHom.algebraMap_toAlgebra _) x

end Instantiable

end Isogeny

end TauCeti
