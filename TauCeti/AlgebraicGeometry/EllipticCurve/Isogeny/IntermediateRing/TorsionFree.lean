/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic

/-!
# The intermediate ring is torsion-free over both coordinate rings

Both coordinate rings embed in `φ.intermediateRing`: the source because it sits inside its own
function field, the target because an isogeny's pullback is injective. So the intermediate ring
is torsion-free as a module over either of them.

## Main results

* `TauCeti.Isogeny.isTorsionFree_intermediateRing_source` and
  `TauCeti.Isogeny.isTorsionFree_intermediateRing_target`: the corresponding
  `Module.IsTorsionFree` facts.

## Why this exists

`ClassGroup.extendedRelNormHom` (`RingTheory/ClassGroup/ExtendedRelNorm.lean`) is stated over a
module-finite extension of Dedekind domains and asks for `Module.IsTorsionFree` in **each of the
two directions it composes** — over `A` for the extension into `M`, and over `R` for the norm back
down. They are hypotheses about two different extensions, not two hypotheses about the one being
normed. No existing declaration or instance discharged either for `φ.intermediateRing`, so every
consumer otherwise had to prove them locally from the injectivity facts; these two results supply
them once, reusably.

The planned consumer is `Isogeny.pushClass`, the class-group pushforward named at
`TauCetiRoadmap/EllipticCurves/README.md:1092`. It does **not** exist in this repository yet —
it is a roadmap target, not a declaration — so nothing here depends on it.

## Design

**Absolute lemmas before relative ones, and the split is not cosmetic.** Injectivity of
`toIntermediateRing` and `pullbackToIntermediateRing` mentions nothing but those two maps, so each
is stated outright — and, being absolute, each belongs beside its own map, so both now live in
`IntermediateRing/Basic.lean`. `Module.IsTorsionFree R M` names the base `R`, so it is *relative
to* an algebra structure a caller has chosen; there is no canonical one to install here, because
registering the pullback-induced structure globally is the diamond `IntermediateRing/Basic.lean`
exists to avoid. A relative statement therefore has to accept the structure, which is why the two
`isTorsionFree_*` results take one and a proof pinning its structure map — the same shape as
`isScalarTower_intermediateRing`, and the same distinction that keeps
`isIntegrallyClosed_intermediateRing` hypothesis-free while `moduleFinite_intermediateRing` is not.

Consumers that already have the injectivity can avoid the explicit hypothesis below by installing
the algebra structure locally and pairing the two `*_injective` lemmas with
`Module.isTorsionFree_iff_algebraMap_injective` directly — that criterion is itself stated under
`[Algebra R A] [IsDomain R] [IsDomain A]`, so the structure still has to be in scope; only the
explicit argument goes away.

**`theorem`, not `instance`.** Registering these would mean registering the algebra structures
they are stated over, which is the diamond again; callers supply them locally, as they already do
for `isScalarTower_intermediateRing`.

An alternative route exists for the target side: `IsIntegralClosure.isTorsionFree`
(`Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean`) descends torsion-freeness from
the ambient field to an integral closure, and `isIntegralClosure_intermediateRing` supplies its
hypothesis. It is not used because it needs `Module.IsTorsionFree W₂.CoordinateRing
W₁.FunctionField` first, which is the same injectivity obligation discharged below — so it would
add a step rather than remove one.

## Provenance

Original work. The AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`dev/hasse-weil @ 513e83879e2f`) proves the analogous facts for Mathlib's literal
`integralClosure` subalgebra — `Curves/RamificationAtInfinity.lean:309` via
`Subalgebra.instIsTorsionFree`, and `Curves/LocalizedDictionary.lean:884` via a named
`RamificationFinite.isTorsionFree` helper. Neither transfers directly: `intermediateRing` is a
`Subring` rather than a `Subalgebra`, precisely so that no algebra structure is baked into its
type, so the subalgebra instance does not apply and the injectivity route is used instead.

Closest of all is AINTLIB's `NormConormIntegralClosure.instTorsionFreeB` (proved in
`Curves/RamificationFinite.lean`, by Chris Birkbeck), which is torsion-freeness for
`B := integralClosure C₂.CoordinateRing C₁.FunctionField` — the same object this file is about.
`IntermediateRing/Basic.lean` already names it and records that, of AINTLIB's structural instances,
only module-finiteness is ported; this PR ports one of the rest. It does not transfer verbatim for
the same reason as above: `B` is a `Subalgebra` carrying an algebra structure in its type, while
`intermediateRing` is a `Subring` with none, so the statement has to take the structure as a
hypothesis rather than inherit it. Sibling `Dedekind.lean` credits `instDedekindB` in the identical
situation.

⚠ *mathlib-track*. The `IntermediateRing` and the `pushClass`-by-`ClassGroup.extendedRelNormHom`
route these two facts feed both come from D. Angdinata's shared isogeny development, named at
`TauCetiRoadmap/EllipticCurves/README.md:1092`, as the sibling files in this series record.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The intermediate ring is torsion-free over the source coordinate ring**, for the algebra
structure induced by `toIntermediateRing`. -/
theorem isTorsionFree_intermediateRing_source (φ : Isogeny W₁ W₂)
    [Algebra W₁.CoordinateRing φ.intermediateRing]
    (h : ∀ x, algebraMap W₁.CoordinateRing φ.intermediateRing x = φ.toIntermediateRing x) :
    Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (by simpa only [funext h] using φ.toIntermediateRing_injective)

/-- **The intermediate ring is torsion-free over the target coordinate ring**, for the algebra
structure induced by `pullbackToIntermediateRing`. This is the side the relative ideal norm of
`ClassGroup.extendedRelNormHom` is taken over. -/
theorem isTorsionFree_intermediateRing_target (φ : Isogeny W₁ W₂)
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    (h : ∀ x, algebraMap W₂.CoordinateRing φ.intermediateRing x = φ.pullbackToIntermediateRing x) :
    Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (by simpa only [funext h] using φ.pullbackToIntermediateRing_injective)

/-! ### Instantiation guards

These two `example`s check that each theorem above stays *applicable*: with the corresponding
`toAlgebra` structure in scope, its hypothesis is discharged by `fun _ ↦ rfl`. They say nothing
about `ClassGroup.extendedRelNormHom`, which they do not mention; what they protect is the shape of
the hypothesis. If a later change makes it undischargeable at the induced structure, this file
stops building rather than a downstream consumer. -/

example (φ : Isogeny W₁ W₂) : True := by
  let _ := φ.toIntermediateRing.toAlgebra
  have : Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing :=
    φ.isTorsionFree_intermediateRing_source fun _ ↦ rfl
  trivial

example (φ : Isogeny W₁ W₂) : True := by
  let _ := φ.pullbackToIntermediateRing.toAlgebra
  have : Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing :=
    φ.isTorsionFree_intermediateRing_target fun _ ↦ rfl
  trivial

end Isogeny

end TauCeti
