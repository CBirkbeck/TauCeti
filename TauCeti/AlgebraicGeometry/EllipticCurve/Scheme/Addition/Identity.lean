/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Morphism
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Comm
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Points
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Integral
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal

/-!
# The zero section is an identity for the Bosma–Lenstra addition morphism

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model over `S = Spec R`, with structure morphism `π : E ⟶ S` and zero section
`0 : S ⟶ E`, and let `E ×_S E ⟶ E` be the Bosma–Lenstra addition morphism
`WeierstrassCurve.additionMorphism`. This file shows that the zero section is a left and a right
identity for the addition morphism: the morphisms `E ⟶ E ×_S E` with components `(π ≫ 0, 𝟙)` and
`(𝟙, π ≫ 0)`, followed by the addition morphism, are the identity of `E`.

Over an integral domain `R`, the scheme `E` is integral, hence reduced, and it is separated, so
two morphisms `E ⟶ E` are equal as soon as they agree on the points of `E` with values in its
residue fields. Such a point has homogeneous coordinates `P` over a field, and the zero section
gives the point with homogeneous coordinates `(0, 1, 0)` over the same field. The addition
morphism sends the pair of these two points to the point with homogeneous coordinates the sum
`add ![0, 1, 0] P` of Mathlib's addition of point representatives, and `add ![0, 1, 0] P` and `P`
represent the same point (`WeierstrassCurve.Projective.zero_add_equiv`).

An elliptic Weierstrass curve over an arbitrary commutative ring is the base change of one over an
integral domain (`WeierstrassCurve.exists_map_eq_of_isElliptic`). The left identity law passes to
a base change `W.map f`, because `projModel (W.map f)` is the base change of `projModel W`
(`WeierstrassCurve.isPullback_projModelBaseChange`), and the addition morphism and the zero
section commute with base change (`WeierstrassCurve.additionMorphism_projModelBaseChange` and
`WeierstrassCurve.projModelZero_projModelBaseChange`). The right identity law follows from the
left one, because the addition morphism is commutative (`WeierstrassCurve.additionMorphism_comm`).

## Main results

* `WeierstrassCurve.lift_projModelZero_id_additionMorphism`: the zero section is a left identity
  for the addition morphism of an elliptic Weierstrass curve over a commutative ring.
* `WeierstrassCurve.lift_id_projModelZero_additionMorphism`: the zero section is a right identity
  for the addition morphism of an elliptic Weierstrass curve over a commutative ring.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.

## Provenance

`lift_id_projModelZero_additionMorphism` and `lift_projModelZero_id_additionMorphism` are adapted
from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/GroupLawAxioms.lean`, declarations
`mulOver_oneOver_atlas`, the right unit law over the universal base, `mulOver_oneOver_of_map`,
`mulOver_oneOver_of_eq` and `mulOver_oneOver`, its transport to every elliptic Weierstrass curve,
and `oneOver_mulOver`, the left unit law, deduced from the right one and commutativity. The other
files named below lie in the same directory.

The source states the two laws as equations of morphisms of `Over (Spec R)`, for its morphisms
`oneOver` and `mulOver` (file `GroupLawConstruction.lean`), with the whiskerings and the unitors
of the cartesian monoidal structure: the right unit law is
`(modelOver W ◁ oneOver W) ≫ mulOver W = (ρ_ (modelOver W)).hom`. Here they are equations of
morphisms of schemes `E ⟶ E`, for the morphisms `E ⟶ E ×_S E` with components `(𝟙, π ≫ 0)` and
`(π ≫ 0, 𝟙)`, built with `pullback.lift`. The source states the two laws in this form too, as its
private theorems `model_one_mul_lift` and `model_mul_one_lift` (file `GroupLawDescent.lean`),
deduced from its two laws in `Over (Spec R)`.

The source proves the right unit law over one ring, the copy `WeierstrassAtlasRingU` in `Type u`
of its universal ring (file `AdditionBaseChange.lean`), by its extensionality principle
`hom_ext_of_forall_specPoint` for field-valued points (file `PointsDictionary.lean`). It evaluates
the multiplication on a pair of points over a field with `mulModelHom_specPoints` (file
`AdditionSpecPoints.lean`), and concludes from `add_zero` in `WeierstrassCurve.Affine.Point`
through its dictionary `projModelPointsEquiv`, which sends the zero section to `0`
(`projModelPointsEquiv_zero`, file `PointsDictionary.lean`). Here the left identity law is proved
first, by the same argument carried out over every integral domain, with Mathlib's
`AlgebraicGeometry.ext_of_fromSpecResidueField_eq` in place of `hom_ext_of_forall_specPoint`, on
points given by homogeneous coordinates (`WeierstrassCurve.exists_ringHom_eq_projModelPoint`,
`WeierstrassCurve.SpecMap_projModelZero` and
`WeierstrassCurve.lift_projModelPoint_additionMorphism_eq_add`), and concludes from
`WeierstrassCurve.Projective.zero_add_equiv`, the form for point representatives of Mathlib's
`WeierstrassCurve.Projective.addMap_of_Z_eq_zero_left`, the left identity law for the addition of
projective point classes. The transport to every curve follows the source, with the reduction
`WeierstrassCurve.exists_map_eq_of_isElliptic` in place of the source's named universal curve
`universalWeierstrassLocU` over `WeierstrassAtlasRingU`, and with
`WeierstrassCurve.projModelZero_projModelBaseChange` in place of the source's
`projModelZero_baseChangeOf`. The right identity law is deduced from the left one and
commutativity, where the source deduces the left unit law from the right one.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Field

variable [W.IsElliptic] {K : Type u} [Field K]

open Projective in
-- Over a field, the addition morphism sends the pair of the zero section and the point with
-- homogeneous coordinates `P` to the point with homogeneous coordinates `P`.
private theorem lift_projModelZero_projModelPoint_additionMorphism {g : R →+* K} {P : Fin 3 → K}
    {hP : (W.toProjective.map g).Equation P} {i : Fin 3} (hi : IsUnit (P i)) :
    pullback.lift (Spec.map (CommRingCat.ofHom g) ≫ W.projModelZero) (W.projModelPoint g hP hi)
        (by rw [Category.assoc, projModelZero_projModelOver, Category.comp_id,
          projModelPoint_projModelOver]) ≫ W.additionMorphism = W.projModelPoint g hP hi := by
  -- a solution with a nonzero coordinate on an elliptic curve over a field is nonsingular
  have hP' := (equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨i, hi.ne_zero⟩)).mp hP
  -- the sum `add ![0, 1, 0] P` is nonsingular, so it has a nonzero coordinate
  obtain ⟨m, hm⟩ := Function.ne_iff.mp
    (ne_zero_of_nonsingular (nonsingular_add nonsingular_zero hP'))
  -- the zero section is the point with homogeneous coordinates `(0, 1, 0)`, so the pair goes to
  -- the point with homogeneous coordinates `add ![0, 1, 0] P`, a unit multiple of `P`
  obtain ⟨u, hu⟩ := zero_add_equiv hP'
  simp only [SpecMap_projModelZero]
  rw [W.lift_projModelPoint_additionMorphism_eq_add _ hi hm.isUnit,
    projModelPoint_eq_projModelPoint_iff]
  exact ⟨rfl, u, hu.symm⟩

-- The morphism `E ⟶ E ×_S E` with components `(π ≫ 0, 𝟙)`, followed by the addition morphism,
-- fixes every point of `E` with values in a field.
private theorem comp_lift_projModelZero_id_additionMorphism (p : Spec (.of K) ⟶ W.projModel) :
    p ≫ pullback.lift (W.projModelOver ≫ W.projModelZero) (𝟙 W.projModel)
        (by rw [Category.assoc, projModelZero_projModelOver, Category.comp_id, Category.id_comp]) ≫
      W.additionMorphism = p := by
  -- `p` is the point with homogeneous coordinates `P`, along a ring homomorphism `g`
  obtain ⟨g, P, hP, i, hi, rfl⟩ := W.exists_ringHom_eq_projModelPoint p
  conv_rhs => rw [← W.lift_projModelZero_projModelPoint_additionMorphism hi]
  rw [← Category.assoc]
  -- and it goes to the pair of the zero section along `g` and `p`
  refine congrArg (· ≫ W.additionMorphism) (pullback.hom_ext ?_ ?_)
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, projModelPoint_projModelOver_assoc]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]

end Field

-- The zero section is a left identity for the addition morphism whenever `E` is reduced, as it is
-- over an integral domain: `E` is a separated scheme, so it suffices that the two sides agree on
-- the points of `E` with values in its residue fields.
private theorem lift_projModelZero_id_additionMorphism_of_isReduced [W.IsElliptic]
    [IsReduced W.projModel] :
    pullback.lift (W.projModelOver ≫ W.projModelZero) (𝟙 W.projModel)
        (by rw [Category.assoc, projModelZero_projModelOver, Category.comp_id, Category.id_comp]) ≫
      W.additionMorphism = 𝟙 W.projModel :=
  ext_of_fromSpecResidueField_eq _ _ (terminal.from _) Set.univ dense_univ
    (fun x _ ↦ (W.comp_lift_projModelZero_id_additionMorphism
      (Scheme.fromSpecResidueField _ x)).trans (Category.comp_id _).symm)
    (terminal.hom_ext _ _)

variable {R' : Type u} [CommRing R'] (f : R →+* R')

-- If the zero section of `W` is a left identity for its addition morphism, then so is the zero
-- section of the base change `W.map f`.
private theorem lift_projModelZero_id_additionMorphism_map [W.IsElliptic]
    (h : pullback.lift (W.projModelOver ≫ W.projModelZero) (𝟙 W.projModel)
        (by rw [Category.assoc, projModelZero_projModelOver, Category.comp_id, Category.id_comp]) ≫
      W.additionMorphism = 𝟙 W.projModel) :
    pullback.lift ((W.map f).projModelOver ≫ (W.map f).projModelZero) (𝟙 (W.map f).projModel)
        (by rw [Category.assoc, projModelZero_projModelOver, Category.comp_id, Category.id_comp]) ≫
      (W.map f).additionMorphism = 𝟙 (W.map f).projModel := by
  -- a morphism to `projModel (W.map f)`, the base change of `projModel W` along `Spec f`, is
  -- determined by its composites with the base change morphism and with the structure morphism
  refine (W.isPullback_projModelBaseChange f).hom_ext ?_ ?_
  · rw [Category.assoc, additionMorphism_projModelBaseChange, ← Category.assoc]
    -- the zero section of `W` is a left identity
    conv_rhs =>
      rw [Category.id_comp, ← Category.comp_id (W.projModelBaseChange f), ← h, ← Category.assoc]
    -- and the base change morphism commutes with the zero sections and with the identities
    refine congrArg (· ≫ W.additionMorphism) (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        projModelZero_projModelBaseChange, projModelBaseChange_projModelOver_assoc]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp,
        Category.comp_id]
  · -- both sides lie over `Spec R'`
    rw [Category.assoc, additionMorphism_projModelOver, pullback.condition, pullback.lift_snd_assoc]

/-- **The zero section is a left identity for the addition morphism.** Let `W` be an elliptic
Weierstrass curve over a commutative ring `R`, and write `E = projModel W` and `S = Spec R`, with
structure morphism `π : E ⟶ S` and zero section `0 : S ⟶ E`. The morphism `E ⟶ E ×_S E` with
components `π ≫ 0` and the identity, followed by the Bosma–Lenstra addition morphism
`E ×_S E ⟶ E`, is the identity of `E`. This morphism `E ⟶ E ×_S E` is the underlying morphism of
the pair `CartesianMonoidalCategory.lift` of the corresponding morphisms of the cartesian monoidal
category `Over S` (`CategoryTheory.Over.lift_left`). -/
@[reassoc (attr := simp)]
theorem lift_projModelZero_id_additionMorphism [W.IsElliptic] :
    pullback.lift (W.projModelOver ≫ W.projModelZero) (𝟙 W.projModel)
        (by rw [Category.assoc, projModelZero_projModelOver, Category.comp_id, Category.id_comp]) ≫
      W.additionMorphism = 𝟙 W.projModel := by
  -- `W` is the base change of an elliptic Weierstrass curve `W₀` over an integral domain, over
  -- which `E` is reduced
  obtain ⟨R₀, _, _, _, W₀, _, f, rfl⟩ := W.exists_map_eq_of_isElliptic
  exact W₀.lift_projModelZero_id_additionMorphism_map f
    W₀.lift_projModelZero_id_additionMorphism_of_isReduced

/-- **The zero section is a right identity for the addition morphism.** Let `W` be an elliptic
Weierstrass curve over a commutative ring `R`, and write `E = projModel W` and `S = Spec R`, with
structure morphism `π : E ⟶ S` and zero section `0 : S ⟶ E`. The morphism `E ⟶ E ×_S E` with
components the identity and `π ≫ 0`, followed by the Bosma–Lenstra addition morphism
`E ×_S E ⟶ E`, is the identity of `E`. This morphism `E ⟶ E ×_S E` is the underlying morphism of
the pair `CartesianMonoidalCategory.lift` of the corresponding morphisms of the cartesian monoidal
category `Over S` (`CategoryTheory.Over.lift_left`). -/
@[reassoc (attr := simp)]
theorem lift_id_projModelZero_additionMorphism [W.IsElliptic] :
    pullback.lift (𝟙 W.projModel) (W.projModelOver ≫ W.projModelZero)
        (by rw [Category.id_comp, Category.assoc, projModelZero_projModelOver, Category.comp_id]) ≫
      W.additionMorphism = 𝟙 W.projModel := by
  -- the addition morphism is commutative, and the zero section is a left identity
  rw [← W.additionMorphism_comm, ← Category.assoc]
  conv_rhs => rw [← W.lift_projModelZero_id_additionMorphism]
  -- and the swap of the two factors exchanges the two components
  refine congrArg (· ≫ W.additionMorphism) (pullback.hom_ext ?_ ?_)
  · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd, pullback.lift_fst]
  · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst, pullback.lift_snd]

end WeierstrassCurve
