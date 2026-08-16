/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

* `TauCeti.Isogeny.toIntermediateRing_injective` and
  `TauCeti.Isogeny.pullbackToIntermediateRing_injective`: the two corestrictions of
  `IntermediateRing/Basic.lean` are injective.
* `TauCeti.Isogeny.isTorsionFree_intermediateRing_source` and
  `TauCeti.Isogeny.isTorsionFree_intermediateRing_target`: the corresponding
  `Module.IsTorsionFree` facts.

## Why this exists

`ClassGroup.extendedRelNormHom` (`RingTheory/ClassGroup/ExtendedRelNorm.lean`) is stated over a
module-finite extension of Dedekind domains and asks for `Module.IsTorsionFree` on **both** sides
of the extension it norms along. Instantiating it at an isogeny means supplying exactly these two
facts for `φ.intermediateRing`, which is what `Isogeny.pushClass` does.

## Design

**Two absolute lemmas, then two relative ones, and the split is not cosmetic.** Injectivity of
`toIntermediateRing` and `pullbackToIntermediateRing` mentions nothing but those two maps, so it
is stated outright. `Module.IsTorsionFree R M` names the base `R`, so it is a statement *relative
to* an algebra structure a caller has chosen; there is no canonical one to install here, because
registering the pullback-induced structure globally is the diamond `IntermediateRing/Basic.lean`
exists to avoid. A relative statement therefore has to accept the structure, which is why the two
`isTorsionFree_*` results take one and a proof pinning its structure map — the same shape as
`isScalarTower_intermediateRing`, and the same distinction that keeps
`isIntegrallyClosed_intermediateRing` hypothesis-free while `moduleFinite_intermediateRing` is not.

Consumers that already have the injectivity can skip the typeclass dance entirely and use the
first two lemmas with `Module.isTorsionFree_iff_algebraMap_injective` themselves.

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

/-- **The source coordinate ring embeds in the intermediate ring.** The corestriction is of
`algebraMap W₁.CoordinateRing W₁.FunctionField`, which is injective because the function field is
by definition the fraction field of the coordinate ring. -/
theorem toIntermediateRing_injective (φ : Isogeny W₁ W₂) :
    Function.Injective φ.toIntermediateRing := fun x y hxy ↦
  IsFractionRing.injective W₁.CoordinateRing W₁.FunctionField <| by
    simpa only [coe_toIntermediateRing] using congrArg Subtype.val hxy

/-- **The target coordinate ring embeds in the intermediate ring**, through the pullback. This is
`pullback_injective` corestricted; the pullback of an isogeny is injective because `φ^*x₂` is
transcendental over the base field. -/
theorem pullbackToIntermediateRing_injective (φ : Isogeny W₁ W₂) :
    Function.Injective φ.pullbackToIntermediateRing := fun x y hxy ↦
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

end Isogeny

end TauCeti
