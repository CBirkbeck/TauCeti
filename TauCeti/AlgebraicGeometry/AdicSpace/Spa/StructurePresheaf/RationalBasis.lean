/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The structure presheaf is the limit of its values on rational opens

Wedhorn §8.1 defines `𝒪_X(V)`, for an open `V ⊆ Spa(A, A⁺)`, as the limit of `𝒪_X(W)` over the
rational opens `W ⊆ V`. This file proves that `presentationLimitPresheaf`, whose value at `V` is a
limit over presentations, has this property naturally in `V`: it is the pointwise right Kan
extension of its restriction to the rational opens. Since the rational opens form a basis, a right
Kan extension along their inclusion of a sheaf for the restricted topology is a sheaf, so the sheaf
condition on `Spa(A, A⁺)` reduces to the rational opens, as in the proof of Wedhorn's
Proposition A.4.

## Main definitions

* `TauCeti.ValuationSpectrum.rationalOpensFunctor` : the inclusion of the rational opens of
  `Spa(A, A⁺)` into all of its opens.
* `TauCeti.ValuationSpectrum.presentationLimitPresheafIsPointwiseRightKanExtension` :
  `presentationLimitPresheaf` is the pointwise right Kan extension of its restriction to the
  rational opens.

## Main results

* `(TauCeti.ValuationSpectrum.rationalOpensFunctor Aplus).IsCoverDense` : the rational opens are
  cover-dense, for a Huber ring `A`.
* `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_of_isSheaf_rational` :
  `presentationLimitPresheaf` is a sheaf once its restriction to the rational opens is a sheaf for
  the restricted topology.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Proposition A.4.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TauCeti.Huber

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A}

variable (Aplus) in
/-- The inclusion of the rational opens of `Spa(A, A⁺)` into all of its opens, as a functor out of
the full subcategory they span. As an abbreviation for `inducedFunctor`, it is full and faithful
(`InducedCategory.full`, `InducedCategory.faithful`; bundled as `fullyFaithfulInducedFunctor _`). -/
abbrev rationalOpensFunctor : InducedCategory (Opens ↥(spa Aplus))
    (Subtype.val : spaRationalOpens Aplus → _) ⥤ Opens ↥(spa Aplus) :=
  inducedFunctor _

/-! ### Indices as rational opens -/

section Lift

variable {V : Opens ↥(spa Aplus)}

/-- An index `i` of `V` as an object of the category of rational opens contained in `V`: the
rational open `R(i) = spaBasicOpen Aplus i.pres.num i.pres.den` together with its inclusion into
`V`. For `h : R(j) ≤ R(i)`, `StructuredArrow.homMk (InducedCategory.homMk h.hom).op` is a morphism
`i.toStructuredArrow ⟶ j.toStructuredArrow`. -/
-- `implicit_reducible`: unifying implicit arguments must see `i.toStructuredArrow.right` as `R(i)`
@[implicit_reducible]
def PresentationIndex.toStructuredArrow (i : PresentationIndex (P := P) Aplus V) :
    StructuredArrow (op V) (rationalOpensFunctor Aplus).op :=
  -- `StructuredArrow.mk` elaborates `Y` before `T`, so `C` is given for the anonymous constructor
  StructuredArrow.mk (C := (InducedCategory _ (Subtype.val : spaRationalOpens Aplus → _))ᵒᵖ)
    (Y := op ⟨_, spaBasicOpen_mem_spaRationalOpens i.isOpen_span⟩) i.le_open.hom.op

/-- **Each projection factors through a rational open**: the projection of `presentationLimit V`
at an index `i` is the restriction to the rational open
`R(i) = spaBasicOpen Aplus i.pres.num i.pres.den` followed by the projection at the presentation
of `i`, read as an index of `R(i)`. -/
-- Not `@[simp]`: `presentationLimitMap_comp_πToPresentation` rewrites the left-hand side, so the
-- left-hand side is not in simp-normal form.
theorem presentationLimitMap_le_open_comp_πToPresentation (i : PresentationIndex (P := P) Aplus V) :
    presentationLimitMap i.le_open ≫
        presentationLimitπToPresentation Aplus _ ⟨i.pres, i.isOpen_span, le_rfl⟩ =
      presentationLimitπToPresentation Aplus V i := by
  -- the index `i.pres` of `R(i)`, read as an index of `V`, is `i`, so the transport is trivial
  simp [PresentationIndex.ext_iff]

/-! ### Cones over the rational opens -/

variable (s : Cone (StructuredArrow.proj (op V) (rationalOpensFunctor Aplus).op ⋙
  (rationalOpensFunctor Aplus).op ⋙ presentationLimitPresheaf P Aplus))

/-- **The morphism induced by a cone over the rational opens in `V`**: its projection at an index
`i` is the leg of `s` at the rational open `R(i) = spaBasicOpen Aplus i.pres.num i.pres.den`
followed by the projection at the presentation of `i`
(`presentationLimitRationalLift_comp_πToPresentation`), and its restriction to a rational open
`W ⊆ V` is the leg of `s` at `W` (`presentationLimitRationalLift_comp_presentationLimitMap`). -/
noncomputable def presentationLimitRationalLift : s.pt ⟶ presentationLimit (P := P) Aplus V :=
  eqToHom (presentationIndexCone_pt Aplus V s.pt _ _).symm ≫
    presentationLimitLift Aplus V (presentationIndexCone Aplus V s.pt
      (fun i ↦ s.π.app i.toStructuredArrow ≫ eqToHom (presentationLimitPresheaf_obj P Aplus _) ≫
        presentationLimitπToPresentation Aplus _ ⟨i.pres, i.isOpen_span, le_rfl⟩)
      fun {i j} f ↦ by
        -- inside `presentationLimit R(i)`, the projection at `j` is the projection at `i`
        -- followed by restriction, and restricting `s` from `R(i)` to `R(j)` is naturality of `s`
        have h := spaBasicOpen_le_spaBasicOpen_iff.mpr <|
          rationalSubset_subset_rationalSubset_of_le Aplus f.le
        simp [presentationLimitπ_comp_restriction (j := ⟨j.pres, j.isOpen_span, h⟩),
          presentationLimitMap_le_open_comp_πToPresentation ⟨j.pres, j.isOpen_span, h⟩,
          ← s.w (StructuredArrow.homMk (InducedCategory.homMk h.hom).op :
            i.toStructuredArrow ⟶ j.toStructuredArrow)])

/-- The projection of `presentationLimitRationalLift s` at an index `i` is the leg of `s` at the
rational open `R(i) = spaBasicOpen Aplus i.pres.num i.pres.den`, followed by the projection at the
presentation of `i`, read as an index of `R(i)`. Together with
`presentationLimit_hom_ext_toPresentation`, this identifies `presentationLimitRationalLift s` as
the only morphism into `presentationLimit V` with these projections. -/
@[simp]
theorem presentationLimitRationalLift_comp_πToPresentation (i : PresentationIndex Aplus V) :
    presentationLimitRationalLift s ≫ presentationLimitπToPresentation Aplus V i =
      s.π.app i.toStructuredArrow ≫ eqToHom (presentationLimitPresheaf_obj P Aplus _) ≫
        presentationLimitπToPresentation Aplus _ ⟨i.pres, i.isOpen_span, le_rfl⟩ := by
  simp [presentationLimitRationalLift]

/-- **The induced morphism restricts to the legs of the cone**: for a rational open `W ⊆ V`, given
by `g` with `W = g.right.unop`, the lift `presentationLimitRationalLift s` followed by the
restriction map `presentationLimitMap` from `V` to `W` is the leg `s.π.app g`, read in
`presentationLimit W` along `presentationLimitPresheaf_obj`. -/
@[reassoc (attr := simp)]
theorem presentationLimitRationalLift_comp_presentationLimitMap
    (g : StructuredArrow (op V) (rationalOpensFunctor Aplus).op) :
    presentationLimitRationalLift s ≫ presentationLimitMap (leOfHom g.hom.unop) =
      s.π.app g ≫ eqToHom (presentationLimitPresheaf_obj P Aplus _) := by
  refine presentationLimit_hom_ext_toPresentation fun j ↦ ?_
  -- the index of `V` with the presentation of `j`
  let k : PresentationIndex Aplus V := ⟨j.pres, j.isOpen_span, j.le_open.trans g.hom.unop.le⟩
  -- on both sides, projecting at `j` is restricting to `R(j)` and projecting there; on the left
  -- the two restrictions compose, giving the projection at `k`
  rw [← presentationLimitMap_le_open_comp_πToPresentation j, Category.assoc,
    reassoc_of% presentationLimitMap_comp, presentationLimitMap_le_open_comp_πToPresentation k]
  -- the lift's projection at `k` is through the leg of `s` at `R(j)`; by naturality of `s`, its
  -- leg at `R(j)` is its leg at `W` followed by restriction
  simp [k, -presentationLimitMap_comp_πToPresentation,
    ← s.w (StructuredArrow.homMk (InducedCategory.homMk j.le_open.hom).op :
      g ⟶ k.toStructuredArrow)]

end Lift

/-! ### The Kan extension and the sheaf condition -/

/-- **`presentationLimitPresheaf` is the right Kan extension of its restriction to the rational
opens**, pointwise: at every open `V`, its value with the restriction maps to the rational opens
`W ⊆ V` is a limit cone over those `W`. This is Wedhorn §8.1's description of `𝒪_X(V)` as the
limit of `𝒪_X(W)` over the rational `W ⊆ V`. -/
noncomputable def presentationLimitPresheafIsPointwiseRightKanExtension : (Functor.RightExtension.mk
    (presentationLimitPresheaf P Aplus) (𝟙 ((rationalOpensFunctor Aplus).op ⋙
      presentationLimitPresheaf P Aplus))).IsPointwiseRightKanExtension := fun V ↦
  IsLimit.mk (fun s ↦ presentationLimitRationalLift s ≫
      eqToHom (presentationLimitPresheaf_obj P Aplus V).symm)
    -- restricted to a rational open `W ⊆ V`, the lift is the leg of `s` at `W`
    (fun s g ↦ by simp)
    -- a morphism into `presentationLimit V` is determined by its projections at the indices of `V`
    (fun s m hm ↦ (comp_eqToHom_iff (presentationLimitPresheaf_obj P Aplus V) m _).mp <|
      presentationLimit_hom_ext_toPresentation fun i ↦ by
        simp [← hm, presentationLimitMap_le_open_comp_πToPresentation])

/-- The rational opens are cover-dense in `Spa(A, A⁺)`: every open is covered by the rational opens
it contains. Mathlib's instances then make `rationalOpensFunctor Aplus` cocontinuous
(`Functor.IsCocontinuous`) and a dense subsite (`Functor.IsDenseSubsite`) for the restricted
topology `Functor.restrictedTopology` on the rational opens. -/
instance [IsHuberRing A] : (rationalOpensFunctor Aplus).IsCoverDense
    (Opens.grothendieckTopology ↥(spa Aplus)) :=
  -- the rational opens form a basis of the topology of `Spa(A, A⁺)`
  TopCat.Opens.coverDense_inducedFunctor (X := TopCat.of ↥(spa Aplus))
    (Subtype.range_coe ▸ isBasis_spaRationalOpens Aplus)

/-- **The sheaf condition on the rational opens suffices**: if the restriction of
`presentationLimitPresheaf` to the rational opens is a sheaf for the restricted topology, then
`presentationLimitPresheaf` is a sheaf on `Spa(A, A⁺)`. With the rational opens as the basis, this
is the step in the proof of Wedhorn's Proposition A.4 from a sheaf on the basis to a sheaf on the
whole space. A sieve on a rational open covers for the restricted topology exactly when its image
covers in `Spa(A, A⁺)` (`Functor.mem_restrictedTopology_iff`), so the hypothesis only involves
covers of rational opens by rational opens. -/
theorem isSheaf_presentationLimitPresheaf_of_isSheaf_rational [IsHuberRing A] (h : Presheaf.IsSheaf
      ((rationalOpensFunctor Aplus).restrictedTopology (Opens.grothendieckTopology ↥(spa Aplus)))
      ((rationalOpensFunctor Aplus).op ⋙ presentationLimitPresheaf P Aplus)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus) :=
  -- a pointwise right Kan extension of a sheaf along a cocontinuous functor is a sheaf; the
  -- rational opens are cover-dense, so `rationalOpensFunctor Aplus` is cocontinuous
  (Presheaf.isSheaf_iff_multifork _ _).mpr fun _ S ↦ ⟨RanIsSheafOfIsCocontinuous.isLimitMultifork h
    presentationLimitPresheafIsPointwiseRightKanExtension S⟩

end TauCeti.ValuationSpectrum
