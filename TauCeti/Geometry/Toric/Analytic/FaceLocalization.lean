/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.FaceLocalization
public import TauCeti.Geometry.Toric.Analytic.AffinePoint

/-!
# Complex points of toric face localizations

A face inclusion `τ ≼ σ` restricts integral characters from the dual semigroup of `σ` to that
of `τ`.  Precomposition with the resulting coordinate-ring map sends a complex point of the
affine chart of `τ` to one of the affine chart of `σ`.  This is exactly the map on functor-of-points
carriers induced by the algebraic face morphism.

When `σ` is regular, every face is cut out by one character `m`.  The coordinate ring of the face
is the localization of the coordinate ring of `σ` away from the monomial of `m`; consequently its
complex points identify with the open locus where that monomial does not vanish.  This file makes
that identification topological for the generator-independent monomial-embedding topologies.  It
is the open-subspace input for gluing regular affine toric charts.

## Main declarations

* `TauCeti.Toric.faceAffineComplexPointMap`: the complex-point map of a face inclusion.
* `TauCeti.Toric.faceAffineComplexPointMap_apply`: its coordinate-ring characterization.
* `TauCeti.Toric.faceAffineComplexPointMap_id` and
  `TauCeti.Toric.faceAffineComplexPointMap_comp`: identity and composition laws.
* `TauCeti.Toric.IsRegularCone.exists_range_faceAffineComplexPointMap`: its image is the
  nonvanishing locus of a character cutting out the face.
* `TauCeti.Toric.IsRegularCone.isOpenEmbedding_faceAffineComplexPointMap`: a regular face chart
  is an open subspace of its ambient affine complex-point chart.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2--1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2--1.3 and §3.1.
-/

public section

open Multiplicative Set Topology

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {σ τ υ : PointedCone ℝ V} {r r' : ℕ}

/-- The map on affine complex points induced by a face inclusion.  It is precomposition with the
same coordinate-ring restriction whose spectrum is `faceAffineToricSchemeMap`. -/
noncomputable abbrev faceAffineComplexPointMap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) :
    AffineSemigroupComplexPoint (dualSemigroup hi τ) →
      AffineSemigroupComplexPoint (dualSemigroup hi σ) :=
  fun x ↦ x.comp (faceAffineCoordinateRingMap hi hτσ)

/-- Applying the complex-point face map is precomposition with the algebraic coordinate-ring map.
This is the carrier-level compatibility with `faceAffineToricSchemeMap`. -/
@[simp]
theorem faceAffineComplexPointMap_apply (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi τ))
    (a : affineCoordinateRing hi σ) :
    faceAffineComplexPointMap hi hτσ x a = x (faceAffineCoordinateRingMap hi hτσ a) :=
  by rfl

/-- The complex-point map of a cone viewed as its own face is the identity. -/
@[simp]
theorem faceAffineComplexPointMap_id (hi : IsIntegralLattice i) :
    faceAffineComplexPointMap hi (PointedCone.IsFaceOf.refl σ) = id := by
  funext x
  simp [faceAffineComplexPointMap]

/-- Successive face restrictions compose contravariantly on coordinate rings and covariantly on
complex points. -/
@[simp]
theorem faceAffineComplexPointMap_comp (hi : IsIntegralLattice i)
    (hυτ : υ.IsFaceOf τ) (hτσ : τ.IsFaceOf σ) :
    faceAffineComplexPointMap hi hτσ ∘ faceAffineComplexPointMap hi hυτ =
      faceAffineComplexPointMap hi (hυτ.trans hτσ) := by
  funext x
  apply AffineSemigroupComplexPoint.ext
  intro m
  simp only [Function.comp_apply, faceAffineComplexPointMap_apply,
    faceAffineCoordinateRingMap_single]

/-- The complex-point face map is the general pullback of affine semigroup points along the
inclusion of dual semigroups. -/
theorem faceAffineComplexPointMap_eq_comap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) :
    faceAffineComplexPointMap hi hτσ = AffineSemigroupComplexPoint.comap
      (dualSemigroupMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        fun _ hx ↦ hτσ.le hx) := by
  funext x
  apply AffineSemigroupComplexPoint.ext
  intro m
  rw [faceAffineComplexPointMap_apply, faceAffineCoordinateRingMap_single,
    AffineSemigroupComplexPoint.comap_apply_single]
  congr 2
  apply Subtype.ext
  exact (coe_dualSemigroupMap_id hi (fun _ hx ↦ hτσ.le hx) m).symm

/-- The complex-point map of a face inclusion is continuous for arbitrary finite generating
families on the two dual semigroups. -/
theorem continuous_faceAffineComplexPointMap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gτ : AddGeneratingFamily (dualSemigroup hi τ) r') :
    Continuous[affinePointTopology gτ, affinePointTopology gσ]
      (faceAffineComplexPointMap hi hτσ) := by
  rw [faceAffineComplexPointMap_eq_comap]
  exact AffineSemigroupComplexPoint.continuous_comap gσ gτ _

/-! ### A face cut out by one character -/

variable (hi : IsIntegralLattice i) (hσ : σ.FG) (m : dualSemigroup hi σ)

/-- A complex point on the nonvanishing locus of a character extends uniquely across the
localization defining the corresponding face. -/
noncomputable abbrev faceAffineComplexPointLift
    (x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}) :
    AffineSemigroupComplexPoint (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) := by
  let hface := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)
  let _ := (faceAffineCoordinateRingMap hi hface).toRingHom.toAlgebra
  have : IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
      (affineCoordinateRing hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) :=
    isLocalization_away_affineCoordinateRingMap_inf_ker hi hσ m
  exact IsLocalization.Away.liftAlgHom (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
    (isUnit_iff_ne_zero.mpr x.2)

/-- Pulling a lifted point back to the ambient chart recovers the original point. -/
@[simp]
theorem faceAffineComplexPointMap_lift
    (x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}) :
    faceAffineComplexPointMap hi
      (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2))
      (faceAffineComplexPointLift hi hσ m x) = x := by
  apply AlgHom.ext
  intro a
  let hface := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)
  let _ := (faceAffineCoordinateRingMap hi hface).toRingHom.toAlgebra
  have : IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
      (affineCoordinateRing hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) :=
    isLocalization_away_affineCoordinateRingMap_inf_ker hi hσ m
  exact IsLocalization.Away.lift_eq (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
    (isUnit_iff_ne_zero.mpr x.2) a

/-- Extending the restriction of a point of the face recovers that point. -/
@[simp]
theorem faceAffineComplexPointLift_map
    (x : AffineSemigroupComplexPoint (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))))) :
    faceAffineComplexPointLift hi hσ m
      ⟨faceAffineComplexPointMap hi
          (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)) x,
        by
          rw [faceAffineComplexPointMap_apply]
          let hface := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)
          let _ := (faceAffineCoordinateRingMap hi hface).toRingHom.toAlgebra
          have : IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
              (affineCoordinateRing hi
                (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) :=
            isLocalization_away_affineCoordinateRingMap_inf_ker hi hσ m
          exact IsUnit.ne_zero (IsLocalization.Away.algebraMap_isUnit
            (S := affineCoordinateRing hi
              (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))))
              (MonoidAlgebra.single (ofAdd m) (1 : ℂ)) |>.map x)
      ⟩ = x := by
  let hface := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)
  let _ := (faceAffineCoordinateRingMap hi hface).toRingHom.toAlgebra
  have : IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
      (affineCoordinateRing hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) :=
    isLocalization_away_affineCoordinateRingMap_inf_ker hi hσ m
  apply AlgHom.coe_ringHom_injective
  exact IsLocalization.lift_of_comp
    (M := Submonoid.powers (MonoidAlgebra.single (ofAdd m) (1 : ℂ))) x.toRingHom

include hσ

/-- The image of a point of the character face lies in the locus where the cutting character
does not vanish. -/
theorem faceAffineComplexPointMap_character_ne_zero
    (x : AffineSemigroupComplexPoint (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))))) :
    faceAffineComplexPointMap hi
        (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)) x
        (MonoidAlgebra.single (ofAdd m) 1) ≠ 0 := by
  rw [faceAffineComplexPointMap_apply]
  let hface := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)
  let _ := (faceAffineCoordinateRingMap hi hface).toRingHom.toAlgebra
  have : IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
      (affineCoordinateRing hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) :=
    isLocalization_away_affineCoordinateRingMap_inf_ker hi hσ m
  exact IsUnit.ne_zero (IsLocalization.Away.algebraMap_isUnit
    (S := affineCoordinateRing hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))))
      (MonoidAlgebra.single (ofAdd m) (1 : ℂ)) |>.map x)

/-- The complex points of the face cut out by `m` are in bijection with the locus of the ambient
chart where the monomial of `m` does not vanish. -/
noncomputable abbrev faceAffineComplexPointEquiv :
    AffineSemigroupComplexPoint (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) ≃
      {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} where
  toFun x := ⟨faceAffineComplexPointMap hi
    (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)) x,
      faceAffineComplexPointMap_character_ne_zero hi hσ m x⟩
  invFun := faceAffineComplexPointLift hi hσ m
  left_inv := faceAffineComplexPointLift_map hi hσ m
  right_inv x := Subtype.ext (faceAffineComplexPointMap_lift hi hσ m x)

@[simp]
theorem coe_faceAffineComplexPointEquiv :
    ⇑(faceAffineComplexPointEquiv hi hσ m) = fun x ↦
      ⟨faceAffineComplexPointMap hi
        (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)) x,
        faceAffineComplexPointMap_character_ne_zero hi hσ m x⟩ :=
  rfl

@[simp]
theorem faceAffineComplexPointEquiv_symm_apply
    (x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}) :
    (faceAffineComplexPointEquiv hi hσ m).symm x =
      faceAffineComplexPointLift hi hσ m x :=
  rfl

/-- Extending a complex point across a localization varies continuously on the nonvanishing
locus, for arbitrary finite generating families on the ambient cone and its face. -/
theorem continuous_faceAffineComplexPointLift
    (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gF : AddGeneratingFamily (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) r') :
    @Continuous
      {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}
      (AffineSemigroupComplexPoint (dualSemigroup hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))))
      (@instTopologicalSpaceSubtype _ _ (affinePointTopology gσ))
      (affinePointTopology gF) (faceAffineComplexPointLift hi hσ m) := by
  let _ := affinePointTopology gσ
  rw [affinePointTopology_eq_iInf gF, continuous_iInf_rng]
  intro t
  rw [continuous_induced_rng]
  -- The induced-topology criterion leaves this evaluation under `Function.comp`; expose it so
  -- the localization representation below can rewrite the element being evaluated.
  change Continuous (fun x ↦ faceAffineComplexPointLift hi hσ m x
    (MonoidAlgebra.single (ofAdd t) (1 : ℂ)))
  let hface := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)
  let _ := (faceAffineCoordinateRingMap hi hface).toRingHom.toAlgebra
  have : IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
      (affineCoordinateRing hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) :=
    isLocalization_away_affineCoordinateRingMap_inf_ker hi hσ m
  obtain ⟨⟨a, y⟩, hy⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (MonoidAlgebra.single (ofAdd m) (1 : ℂ)))
    (MonoidAlgebra.single (ofAdd t) (1 : ℂ))
  rw [← hy]
  have ha : Continuous fun x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} ↦ x.1 a :=
    (continuous_eval_const gσ a).comp continuous_subtype_val
  have hay : Continuous fun x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} ↦ x.1 y.1 :=
    (continuous_eval_const gσ y.1).comp continuous_subtype_val
  have hay0 : ∀ x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}, x.1 y.1 ≠ 0 := by
    rintro x
    obtain ⟨n, hn⟩ := y.2
    rw [← hn, map_pow]
    exact pow_ne_zero n x.2
  convert ha.mul (hay.inv₀ hay0) using 1
  funext x
  -- The lift is packaged as an algebra homomorphism; expose its underlying localization lift in
  -- order to apply the fraction characterization `IsLocalization.lift_mk'_spec`.
  change (IsLocalization.Away.lift (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
      (isUnit_iff_ne_zero.mpr x.2))
    (IsLocalization.mk' _ a y) = x.1 a * (x.1 y.1)⁻¹
  rw [IsLocalization.Away.lift]
  apply (IsLocalization.lift_mk'_spec _ a (x.1 a * (x.1 y.1)⁻¹) y).2
  -- The ring-hom and algebra-hom coercions obscure the elementary cancellation identity.
  change x.1 a = x.1 y.1 * (x.1 a * (x.1 y.1)⁻¹)
  rw [mul_left_comm, mul_inv_cancel₀ (hay0 x), mul_one]

/-- The algebraic bijection between the complex points of a character face and its nonvanishing
locus is a homeomorphism for arbitrary finite generating families. -/
noncomputable abbrev faceAffineComplexPointHomeomorph
    (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gF : AddGeneratingFamily (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) r') :
    @Homeomorph
      (AffineSemigroupComplexPoint (dualSemigroup hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))))
      {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}
      (affinePointTopology gF)
      (@instTopologicalSpaceSubtype _ _ (affinePointTopology gσ)) := by
  let _ := affinePointTopology gσ
  let _ := affinePointTopology gF
  exact
    { toEquiv := faceAffineComplexPointEquiv hi hσ m
      continuous_toFun := Continuous.subtype_mk
        (continuous_faceAffineComplexPointMap hi
          (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)) gσ gF) _
      continuous_invFun := continuous_faceAffineComplexPointLift hi hσ m gσ gF }

@[simp]
theorem coe_faceAffineComplexPointHomeomorph
    (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gF : AddGeneratingFamily (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) r') :
    ⇑(faceAffineComplexPointHomeomorph (hσ := hσ) hi m gσ gF) = fun x ↦
      ⟨faceAffineComplexPointMap hi
        (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)) x,
        faceAffineComplexPointMap_character_ne_zero hi hσ m x⟩ :=
  rfl

/-- The image of the complex-point map for the face cut out by `m` is exactly the locus where the
monomial of `m` does not vanish. -/
theorem range_faceAffineComplexPointMap_inf_ker :
    Set.range (faceAffineComplexPointMap hi
      (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2))) =
      {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) |
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact faceAffineComplexPointMap_character_ne_zero hi hσ m y
  · intro hx
    exact ⟨faceAffineComplexPointLift hi hσ m ⟨x, hx⟩,
      faceAffineComplexPointMap_lift hi hσ m ⟨x, hx⟩⟩

/-- The complex-point map for a face cut out by one character is an open embedding for arbitrary
finite generating families. -/
theorem isOpenEmbedding_faceAffineComplexPointMap_inf_ker
    (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gF : AddGeneratingFamily (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) r') :
    @IsOpenEmbedding
      (AffineSemigroupComplexPoint (dualSemigroup hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))))
      (AffineSemigroupComplexPoint (dualSemigroup hi σ))
      (affinePointTopology gF) (affinePointTopology gσ)
      (faceAffineComplexPointMap hi
        (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2))) := by
  let _ := affinePointTopology gσ
  let _ := affinePointTopology gF
  have hopen : @IsOpen (AffineSemigroupComplexPoint (dualSemigroup hi σ))
      (affinePointTopology gσ) {x |
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} :=
    isOpen_ne.preimage (continuous_eval_const gσ (MonoidAlgebra.single (ofAdd m) 1))
  have hsub : @IsOpenEmbedding
      {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}
      (AffineSemigroupComplexPoint (dualSemigroup hi σ))
      (@instTopologicalSpaceSubtype _ _ (affinePointTopology gσ)) (affinePointTopology gσ)
      ((↑) : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} →
          AffineSemigroupComplexPoint (dualSemigroup hi σ)) :=
    hopen.isOpenEmbedding_subtypeVal
  have hcomp := hsub.comp
    (faceAffineComplexPointHomeomorph (hσ := hσ) hi m gσ gF).isOpenEmbedding
  convert hcomp using 1
  funext x
  rfl

omit hσ

namespace IsRegularCone

variable {τ : PointedCone ℝ V}

/-- For a face of a regular cone, some character cutting out that face identifies the range of the
complex-point map with its nonvanishing locus. -/
theorem exists_range_faceAffineComplexPointMap (hreg : IsRegularCone i σ)
    (hτ : τ.IsFaceOf σ) :
    ∃ m : dualSemigroup hi σ,
      σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ ∧
      Set.range (faceAffineComplexPointMap hi hτ) =
        {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) |
          x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} := by
  obtain ⟨m, hm, hface⟩ := hreg.exists_mem_dualSemigroup_inf_ker_eq hi hτ
  refine ⟨⟨m, hm⟩, hface, ?_⟩
  subst τ
  have heq : hτ = PointedCone.isFaceOf_inf_ker
      ((mem_dualSemigroup hi (⟨m, hm⟩ : dualSemigroup hi σ)).1 hm) := Subsingleton.elim _ _
  subst hτ
  exact range_faceAffineComplexPointMap_inf_ker hi hreg.fg ⟨m, hm⟩

/-- The complex-point map of every face inclusion into a regular cone is an open embedding for
arbitrary finite generating families.  Thus face localization is an open subspace at the
topological level. -/
theorem isOpenEmbedding_faceAffineComplexPointMap (hreg : IsRegularCone i σ)
    (hτ : τ.IsFaceOf σ) (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gτ : AddGeneratingFamily (dualSemigroup hi τ) r') :
    @IsOpenEmbedding
      (AffineSemigroupComplexPoint (dualSemigroup hi τ))
      (AffineSemigroupComplexPoint (dualSemigroup hi σ))
      (affinePointTopology gτ) (affinePointTopology gσ)
      (faceAffineComplexPointMap hi hτ) := by
  obtain ⟨m, hm, hface⟩ := hreg.exists_mem_dualSemigroup_inf_ker_eq hi hτ
  subst τ
  have heq : hτ = PointedCone.isFaceOf_inf_ker
      ((mem_dualSemigroup hi (⟨m, hm⟩ : dualSemigroup hi σ)).1 hm) := Subsingleton.elim _ _
  subst hτ
  exact isOpenEmbedding_faceAffineComplexPointMap_inf_ker hi hreg.fg ⟨m, hm⟩ gσ gτ

end IsRegularCone


end TauCeti.Toric
