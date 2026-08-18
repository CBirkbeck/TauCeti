/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
-- Proof-only: `pullback_injective` is used inside a proof, not in any statement.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FunctionField

/-!
# The intermediate ring is torsion-free over both coordinate rings

Both coordinate rings embed in `φ.intermediateRing`: the source because it sits inside its own
function field, the target because an isogeny's pullback is injective. So the intermediate ring
is torsion-free as a module over either of them.

## Main results

* `TauCeti.Isogeny.pullbackToIntermediateRing_injective`: the corestricted pullback is injective.
  Its source-side companion `toIntermediateRing_injective` needs nothing from this module, so it
  lives in `IntermediateRing/Basic.lean` beside the map it is about.
* `TauCeti.Isogeny.isTorsionFree_intermediateRing_source` and
  `TauCeti.Isogeny.isTorsionFree_intermediateRing_target`: the corresponding
  `Module.IsTorsionFree` facts.

## Why this exists

`ClassGroup.extendedRelNormHom` (`RingTheory/ClassGroup/ExtendedRelNorm.lean`) is stated over a
module-finite extension of Dedekind domains and asks for `Module.IsTorsionFree` on **both** sides
of the extension it norms along. No existing declaration or instance discharged those two
obligations for `φ.intermediateRing`, so every consumer otherwise had to prove them locally from
the injectivity facts; these two results supply them once, reusably.

The planned consumer is `Isogeny.pushClass`, the class-group pushforward named at
`TauCetiRoadmap/EllipticCurves/README.md:1092`. It does **not** exist in this repository yet —
it is a roadmap target, not a declaration — so nothing here depends on it.

## Design

**Absolute lemmas before relative ones, and the split is not cosmetic.** Injectivity of
`toIntermediateRing` and `pullbackToIntermediateRing` mentions nothing but those two maps, so each
is stated outright — and, being absolute, each belongs beside its own map rather than here, which
is why only the pullback one is in this file: its proof is the only half needing
`Isogeny/FunctionField.lean`. `Module.IsTorsionFree R M` names the base `R`, so it is *relative
to* an algebra structure a caller has chosen; there is no canonical one to install here, because
registering the pullback-induced structure globally is the diamond `IntermediateRing/Basic.lean`
exists to avoid. A relative statement therefore has to accept the structure, which is why the two
`isTorsionFree_*` results take one and a proof pinning its structure map — the same shape as
`isScalarTower_intermediateRing`, and the same distinction that keeps
`isIntegrallyClosed_intermediateRing` hypothesis-free while `moduleFinite_intermediateRing` is not.

Consumers that already have the injectivity can skip the typeclass dance entirely and pair the two
`*_injective` lemmas with `Module.isTorsionFree_iff_algebraMap_injective` themselves.

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
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The target coordinate ring embeds in the intermediate ring**, through the pullback. This is
`pullback_injective` corestricted; the pullback of an isogeny is injective because `φ^*x₂` is
transcendental over the base field.

The source-side companion is `toIntermediateRing_injective`, in `IntermediateRing/Basic.lean`
beside the map it is about. -/
@[grind .]
theorem pullbackToIntermediateRing_injective (φ : Isogeny W₁ W₂) :
    Function.Injective φ.pullbackToIntermediateRing := fun x y hxy ↦
  -- Not `RingHom.injective_codRestrict.mpr`: that criterion must see `pullbackToIntermediateRing`
  -- as a `codRestrict`, and this module imports only the definition, whose body is unexposed. The
  -- elaborator then reports `Function.Injective ⇑(φ.pullback.codRestrict ?m ?m)` against the
  -- expected `Function.Injective ⇑φ.pullbackToIntermediateRing`. The exported `@[simp]` lemma
  -- `coe_pullbackToIntermediateRing` crosses that boundary, so injectivity transports along the
  -- coercion instead.
  φ.pullback_injective <| by
    simpa only [coe_pullbackToIntermediateRing] using congrArg Subtype.val hxy

/-- **The intermediate ring is torsion-free over the source coordinate ring**, for the algebra
structure induced by `toIntermediateRing`. -/
theorem isTorsionFree_intermediateRing_source (φ : Isogeny W₁ W₂)
    [inst : Algebra W₁.CoordinateRing φ.intermediateRing]
    (halg : inst = φ.toIntermediateRing.toAlgebra) :
    Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing := by
  -- rewrite first: `subst` would remove `inst` as a registered instance, and the criterion below
  -- is stated for the one in scope
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  subst halg
  simpa only [RingHom.algebraMap_toAlgebra] using φ.toIntermediateRing_injective

/-- **The intermediate ring is torsion-free over the target coordinate ring**, for the algebra
structure induced by `pullbackToIntermediateRing`. This is the side the relative ideal norm of
`ClassGroup.extendedRelNormHom` is taken over. -/
theorem isTorsionFree_intermediateRing_target (φ : Isogeny W₁ W₂)
    [inst : Algebra W₂.CoordinateRing φ.intermediateRing]
    (halg : inst = φ.pullbackToIntermediateRing.toAlgebra) :
    Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  subst halg
  simpa only [RingHom.algebraMap_toAlgebra] using φ.pullbackToIntermediateRing_injective

/-! ### Instantiation guards

The defect these results fix was an unsatisfiable instance block: `ClassGroup.extendedRelNormHom`
typechecked, passed every rubric and merged while no consumer could discharge its
`Module.IsTorsionFree` arguments. Nothing but *applying* a declaration detects that, so the two
applications are kept here rather than checked once and deleted. If a later change to the
hypotheses above makes them undischargeable, this file stops building instead of the consumer.

Mathlib keeps such `example`s for the same purpose — 157 of them are bare `inferInstance` guards. -/

example (φ : Isogeny W₁ W₂) : True := by
  let _ := φ.toIntermediateRing.toAlgebra
  have : Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing :=
    φ.isTorsionFree_intermediateRing_source rfl
  trivial

example (φ : Isogeny W₁ W₂) : True := by
  let _ := φ.pullbackToIntermediateRing.toAlgebra
  have : Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing :=
    φ.isTorsionFree_intermediateRing_target rfl
  trivial

end Isogeny

end TauCeti
