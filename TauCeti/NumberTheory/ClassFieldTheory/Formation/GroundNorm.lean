/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction

/-!
# The norm between the ground levels of a restriction

Let `T : LayerRestriction small big` be a restriction of finite normal layers, the layer `K/F`
restricted to `K/E` for an intermediate field `F ⊆ E ⊆ K`, with ground subgroups `U' ≤ U`. On
ground levels a restriction has the inclusion `A^U ⊆ A^{U'}` (`LayerRestriction.groundInclusion`)
and, in the other direction, the **norm** `N_{U/U'} : A^{U'} → A^U`, the sum of the translates of
an element by representatives of the cosets `U/U'`. It is the map the Artin–Tate functoriality
diagram `artinMap_groundNorm` is stated against.

The norm is not a new construction. The level `A^U` of an open subgroup is the degree-zero
cohomology `H⁰(U, A)` of `U` acting on the coefficient module (`Formation.levelEquivH0`), and the
norm is Tau Ceti's degree-zero corestriction `ContCohomology.explicitCor0` for the subgroup `U'` of
the group `U`, read on levels. Its normalization `N_{U/U'} ∘ incl = [U : U'] • id`
(`groundNorm_groundInclusion`) is `ContCohomology.explicitCor0_comp_res0`.

## Main definitions

* `TauCeti.ClassFieldTheory.Formation.levelEquivH0`: the level `A^U` as the degree-zero
  cohomology `H⁰(U, A)`.
* `TauCeti.ClassFieldTheory.Formation.levelEquivH0SubgroupOf`: the level `A^{U'}` as the
  degree-zero cohomology `H⁰(U', A)` of `U'` viewed as a subgroup of `U`.
* `TauCeti.ClassFieldTheory.LayerRestriction.groundNorm`: the norm `A^{U'} → A^U` between the
  ground levels of a restriction.

## Main statements

* `TauCeti.ClassFieldTheory.LayerRestriction.groundNorm_apply_coe`: the norm is the sum of the
  translates by coset representatives.
* `TauCeti.ClassFieldTheory.LayerRestriction.groundNorm_groundInclusion`: the norm of an element of
  the ground level `A^U` is its multiple by the relative degree.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1–2.
* J. S. Milne, *Class Field Theory*, Chapter II, 1.29–1.30 (the norm along a subgroup).
-/

-- The signature of `groundNorm` follows the blueprint `Suggested.lean` of the Tau Ceti
-- `ClassFieldTheory` roadmap (`namespace LayerRestriction`).

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

attribute [local instance] TopRep.distribMulAction

namespace Formation

variable (F : Formation G)

/-- **The level `A^U` of an open subgroup is the degree-zero cohomology `H⁰(U, A)`** of `U`
acting on the coefficient module: both are the elements of the ambient module fixed by `U`. -/
def levelEquivH0 (U : OpenSubgroup G) :
    F.level U ≃+ ContCohomology.H0 U.toSubgroup F.toRep.V where
  toFun x := ⟨x, (FixedPoints.mem_addSubgroup _ _ _).2 fun u ↦ F.mem_level.1 x.2 u u.2⟩
  invFun x := ⟨x, F.mem_level.2 fun u hu ↦ (FixedPoints.mem_addSubgroup _ _ _).1 x.2 ⟨u, hu⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_levelEquivH0 (U : OpenSubgroup G) (x : F.level U) :
    (F.levelEquivH0 U x : F.toRep.V) = x :=
  (rfl)

@[simp]
theorem coe_levelEquivH0_symm (U : OpenSubgroup G)
    (x : ContCohomology.H0 U.toSubgroup F.toRep.V) :
    ((F.levelEquivH0 U).symm x : F.toRep.V) = x :=
  (rfl)

/-- **The level `A^{U'}` of an open subgroup `U' ≤ U` is the degree-zero cohomology `H⁰(U', A)`**
of `U'` read as a subgroup of `U`, acting on the coefficient module through `U`. -/
def levelEquivH0SubgroupOf {U' U : OpenSubgroup G} (h : U' ≤ U) :
    F.level U' ≃+ ContCohomology.H0 (U'.toSubgroup.subgroupOf U.toSubgroup) F.toRep.V where
  toFun x := ⟨x, (FixedPoints.mem_addSubgroup _ _ _).2 fun u ↦
    F.mem_level.1 x.2 _ (Subgroup.mem_subgroupOf.1 u.2)⟩
  invFun x := ⟨x, F.mem_level.2 fun g hg ↦
    (FixedPoints.mem_addSubgroup _ _ _).1 x.2 ⟨⟨g, h hg⟩, Subgroup.mem_subgroupOf.2 hg⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_levelEquivH0SubgroupOf {U' U : OpenSubgroup G} (h : U' ≤ U) (x : F.level U') :
    (F.levelEquivH0SubgroupOf h x : F.toRep.V) = x :=
  (rfl)

end Formation

namespace LayerRestriction

variable {small big : NormalLayer G}

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The ground subgroup `U'` of the smaller layer of a restriction has finite index in the ground
subgroup `U` of the larger one: that index is the relative degree, which is positive. -/
theorem finiteIndex_ground_subgroupOf (T : LayerRestriction small big) :
    (small.ground.toSubgroup.subgroupOf big.ground.toSubgroup).FiniteIndex :=
  ⟨by simpa only [relativeDegree_def, Subgroup.relIndex] using T.relativeDegree_pos.ne'⟩

/-- The **norm** `N_{U/U'} : A^{U'} → A^U` along a restriction `U' ≤ U` of ground subgroups: the
degree-zero corestriction `ContCohomology.explicitCor0` for the subgroup `U'` of `U`, read on
levels. It sends an element to the sum of its translates by representatives of the cosets `U/U'`
(`groundNorm_apply_coe`). The subgroup `U'` need not be normal in `U`, so this is not the norm of
a layer. -/
def groundNorm (T : LayerRestriction small big) (F : Formation G) :
    F.level small.ground →+ F.level big.ground :=
  haveI := T.finiteIndex_ground_subgroupOf
  (F.levelEquivH0 big.ground).symm.toAddMonoidHom.comp <|
    (ContCohomology.explicitCor0 big.ground.toSubgroup F.toRep.V
      (small.ground.toSubgroup.subgroupOf big.ground.toSubgroup)).comp
      (F.levelEquivH0SubgroupOf T.ground_le).toAddMonoidHom

/-- The norm along a restriction is the sum of the translates by coset representatives, read in
the ambient module. -/
@[simp]
theorem groundNorm_apply_coe (T : LayerRestriction small big) (F : Formation G)
    (x : F.level small.ground) :
    ((T.groundNorm F x : F.level big.ground) : F.toRep.V) =
      ∑ᶠ q : big.ground.toSubgroup ⧸ small.ground.toSubgroup.subgroupOf big.ground.toSubgroup,
        F.toRep.ρ (q.out : G) x := by
  have := T.finiteIndex_ground_subgroupOf
  rw [groundNorm, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    Formation.coe_levelEquivH0_symm, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ContCohomology.coe_explicitCor0, finsum_eq_sum_of_fintype]
  -- Termwise, the action of a coset representative of `U/U'` on the level is the operator `ρ` of
  -- the formation at its underlying element of `G`.
  exact Finset.sum_congr rfl fun q _ ↦ by
    rw [Formation.coe_levelEquivH0SubgroupOf, Submonoid.smul_def, TopRep.distribMulAction_smul,
      Formation.toRep_ρ_apply]

/-- **The norm of an element of the ground level `A^U` is its multiple by the relative degree:**
the norm is degree-zero corestriction, the inclusion is degree-zero restriction, and
`cor⁰ ∘ res⁰ = [U : U'] • id`. -/
theorem groundNorm_groundInclusion (T : LayerRestriction small big) (F : Formation G)
    (x : F.level big.ground) :
    T.groundNorm F (T.groundInclusion F x) = T.relativeDegree • x := by
  have := T.finiteIndex_ground_subgroupOf
  -- Read on degree-zero cohomology, the inclusion of ground levels is degree-zero restriction.
  have hres : F.levelEquivH0SubgroupOf T.ground_le (T.groundInclusion F x) =
      ContCohomology.explicitRes0 big.ground.toSubgroup F.toRep.V
        (small.ground.toSubgroup.subgroupOf big.ground.toSubgroup) (F.levelEquivH0 big.ground x) :=
    Subtype.ext <| by
      rw [Formation.coe_levelEquivH0SubgroupOf, groundInclusion_apply_coe,
        ContCohomology.coe_explicitRes0, Formation.coe_levelEquivH0]
  rw [groundNorm, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, hres, ContCohomology.explicitCor0_comp_res0, map_nsmul,
    AddEquiv.symm_apply_apply, relativeDegree_def, Subgroup.relIndex]

end LayerRestriction

end TauCeti.ClassFieldTheory
