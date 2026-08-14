/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated
public import TauCeti.Topology.Category.TopCommRingCat.Limits
public import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Products and equalizers of complete separated topological rings

Roadmap Layer 3.2's second half: the full subcategory
`TauCeti.CompleteSeparatedTopCommRingCat` has products and equalizers, created by the
inclusion into `TopCommRingCat` — Mathlib's
`CategoryTheory.ObjectProperty.createsLimitFullSubcategoryInclusionOfClosed` applied to the
closure instances proved here. The equalizer closure is where separatedness of the codomain
is used: the equalizing locus is closed in a Hausdorff codomain, and a closed subring of a
complete separated ring is complete separated.

## Main results

* The `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms` instance for
  `TauCeti.TopCommRingCat.isCompleteSeparated` : the property transfers along isomorphisms of
  topological rings.
* `TauCeti.TopCommRingCat.IsCompleteSeparated.of_isClosedEmbedding` : a closed subobject of
  a complete separated ring is complete separated.
* The `IsClosedUnderLimitsOfShape` instances for discrete shapes and parallel pairs, and the
  resulting products and equalizers in `TauCeti.CompleteSeparatedTopCommRingCat`, created by
  the inclusion.
-/

public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.TopCommRingCat

/-- The complete separated property transfers along isomorphisms of topological commutative
rings: an isomorphism is in particular a homeomorphism of the underlying additive groups,
and the group uniformity is functorial under it. -/
instance : (isCompleteSeparated.{u}).IsClosedUnderIsomorphisms where
  of_iso := by
    intro R S e hR
    let φ : S ≃ₜ R :=
      { toFun := e.inv
        invFun := e.hom
        left_inv := fun x ↦ congrArg (fun g : S ⟶ S ↦ (g : S → S) x) e.inv_hom_id
        right_inv := fun x ↦ congrArg (fun g : R ⟶ R ↦ (g : R → R) x) e.hom_inv_id
        continuous_toFun := e.inv.2
        continuous_invFun := e.hom.2 }
    have hR' := (isCompleteSeparated_iff _).mp hR
    have : T0Space R := hR'.t0Space
    refine (isCompleteSeparated_iff _).mpr ⟨?_, φ.isEmbedding.t0Space⟩
    let _ : UniformSpace S := IsTopologicalAddGroup.rightUniformSpace S
    let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
    have : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
    have : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
    have : CompleteSpace R := hR'.completeSpace
    exact ((AddMonoidHom.isUniformInducing_of_isInducing (f := e.inv.val)
      φ.isInducing).completeSpace_congr φ.surjective).mpr ‹_›

/-- A closed embedding of topological rings pulls the complete separated property back: the
image is a closed subring of a complete Hausdorff ring, hence complete, and separatedness is
inherited. This is where Hausdorffness of the codomain does its work. -/
theorem IsCompleteSeparated.of_isClosedEmbedding {R S : TopCommRingCat.{u}} (f : R ⟶ S)
    (hf : Topology.IsClosedEmbedding f) (hS : IsCompleteSeparated S) :
    IsCompleteSeparated R := by
  have : T0Space S := hS.t0Space
  refine ⟨?_, hf.toIsEmbedding.t0Space⟩
  let _ : UniformSpace S := IsTopologicalAddGroup.rightUniformSpace S
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  have : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace S := hS.completeSpace
  exact (AddMonoidHom.isUniformInducing_of_isInducing (f := f.val) hf.toIsInducing).completeSpace
    hf.isClosed_range.isComplete

/-- Complete separated objects are closed under products in `TopCommRingCat`. -/
instance {β : Type v} :
    (isCompleteSeparated.{max u v}).IsClosedUnderLimitsOfShape (Discrete β) :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    exact ObjectProperty.prop_of_iso _
      (IsLimit.conePointsIsoOfNatIso (piFanIsLimit fun b ↦ F.obj ⟨b⟩) (limit.isLimit F)
        Discrete.natIsoFunctor.symm)
      ((isCompleteSeparated_iff _).mpr (IsCompleteSeparated.pi (f := fun b ↦ F.obj ⟨b⟩)
        fun b ↦ (isCompleteSeparated_iff _).mp (hF ⟨b⟩))))

/-- Complete separated objects are closed under equalizers: the equalizing locus of two
morphisms into a Hausdorff codomain is a closed subring. -/
instance : (isCompleteSeparated.{u}).IsClosedUnderLimitsOfShape WalkingParallelPair :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    set f := F.map WalkingParallelPairHom.left
    set g := F.map WalkingParallelPairHom.right
    have : T2Space (F.obj .one) := ((isCompleteSeparated_iff _).mp (hF .one)).t2Space
    have hcl : IsClosed (RingHom.eqLocus f.val g.val : Set (F.obj .zero)) :=
      isClosed_eq f.2 g.2
    exact ObjectProperty.prop_of_iso _
      (IsLimit.conePointsIsoOfNatIso (equalizerForkIsLimit f g) (limit.isLimit F)
        (diagramIsoParallelPair F).symm)
      ((isCompleteSeparated_iff _).mpr (IsCompleteSeparated.of_isClosedEmbedding
        ⟨(RingHom.eqLocus f.val g.val).subtype, continuous_subtype_val⟩
        hcl.isClosedEmbedding_subtypeVal ((isCompleteSeparated_iff _).mp (hF .zero)))))

end TauCeti.TopCommRingCat

namespace TauCeti.CompleteSeparatedTopCommRingCat

/-- Products in the complete separated category, created by the inclusion. -/
noncomputable instance : HasProducts.{v} CompleteSeparatedTopCommRingCat.{max u v} :=
  fun _ ↦ inferInstance

/-- Equalizers in the complete separated category, created by the inclusion. -/
noncomputable instance : HasEqualizers CompleteSeparatedTopCommRingCat.{u} :=
  inferInstance

end TauCeti.CompleteSeparatedTopCommRingCat
