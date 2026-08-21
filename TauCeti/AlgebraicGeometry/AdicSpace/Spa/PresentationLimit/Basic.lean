/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.LocalizationTopology.CompleteSeparated.RefinementCategory
public import Mathlib.CategoryTheory.Sites.Spaces
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Limits

/-!
# The presentation-indexed limit of completed rational localizations

Wedhorn §8.1 assigns `A⟨T/s⟩` to the rational subset `R(T/s)` and extends the assignment to an
arbitrary open `V ⊆ Spa(A,A⁺)` by a limit of completed rational localizations. This file builds
the limit **indexed by presentations** rather than by rational subsets. Identifying it with
Wedhorn's `𝒪_X` is an initiality statement about the indexing functor which is *not* proved
here, so the declarations are named for the construction rather than for the target — see
"Why the index is presentations and not subsets" below.

The index is `RationalIndex`: a presentation with open numerator ideal — the rational-basis
condition — whose rational subset is contained in `V`, ordered by refinement.
`CompleteSeparated/RefinementCategory.lean` already makes the assignment `p ↦ A⟨p.num / p.den⟩`
functorial on presentations, so the diagram is obtained by restricting that functor along the
forgetful map, and the value is its limit — which exists because
`CompleteSeparatedTopCommRingCat` has all small limits.

Everything here is stated for an arbitrary `Subring` of a topological ring carrying a pair of
definition. Wedhorn's standing hypotheses — a Huber ring, a ring of integral elements — are
likewise not imposed; the sibling `spa` and `rationalSubset` carry the same convention. Adding
them would not turn this into `𝒪_X`: what is missing is the initiality of the indexing functor,
not the hypotheses.

## Main definitions

* `TauCeti.ValuationSpectrum.RationalIndex` : the index category for an open.
* `TauCeti.ValuationSpectrum.rationalIndexDiagram` : the diagram it indexes.
* `TauCeti.ValuationSpectrum.presentationLimitObj` : the limit over the index, the candidate
  for `𝒪_X(V)`.
* `TauCeti.ValuationSpectrum.presentationLimitMap` : the restriction morphism of a containment.
* `TauCeti.ValuationSpectrum.presentationLimitPresheaf` : the presheaf itself.
* `TauCeti.Huber.PairOfDefinition.HasSheafyPresentationLimit` : the presentation-indexed
  presheaf is a sheaf. It is named for the presheaf it actually tests: until the initiality
  statement is proved, that presheaf is not known to be Wedhorn's `𝒪_X`, so this is not yet the
  roadmap's `Huber.IsSheafyPair` (`AdicSpaces/README.md:522`) — which the rename leaves free.

## Main results

* `TauCeti.Huber.PairOfDefinition.hasSheafyPresentationLimit_iff` : sheafiness unfolds to
  Mathlib's sheaf
  condition (`HasSheafyPresentationLimit` is not exposed; this is the route across).
* `presentationLimitPresheaf_obj`, `presentationLimitPresheaf_map` : its simp interface.
* `presentationLimitMap_π` : the characteristic equation of the restriction morphism, and
  `presentationLimitMap_refl` / `presentationLimitMap_comp` : its identity and composition laws,
  which is what the presheaf's functor laws are.
* `RationalIndex.directed` : the index is directed, so presentations of the same subset are
  constrained through a common refinement.

Both `presentationLimitObj` and `presentationLimitMap` are **sealed**, so a consumer never
depends on the object being Mathlib's chosen `limit`. The interface is the universal property,
named here: `presentationLimitπ` projects, `presentationLimitObj_hom_ext` proves two maps into it
equal, and `presentationLimitLift` builds one with `presentationLimitLift_π` as its characteristic
equation. `presentationLimitMap_π`, `_refl` and `_comp` state how restriction meets the
projections.

The two *reindexing* lemmas are the exception. `limit.pre_π` and `limit.pre_pre` are stated with
`E ⋙ F`, which is `rationalIndexInclusionOfLE ⋙ rationalIndexDiagram`; recognising that as
`rationalIndexDiagram` is definitional but beyond the transparency `rw` uses, which is why Mathlib
itself reaches those two with `erw`. Three `rfl` lemmas name the identities involved —
`rationalIndexInclusionOfLE_comp_diagram`, `rationalIndexInclusionOfLE_refl` and
`rationalIndexInclusionOfLE_comp` — and `presentationLimitMap_π`, `_refl` and `_comp` are proved
in term mode, where they are accepted. Each of those three docstrings names the identity its proof
consumes, so a consumer never meets the `erw`.

## Why the index is presentations and not subsets

`A⟨T/s⟩` is built from the data `(T, s)`, and two presentations of the *same* rational subset
give canonically isomorphic but not equal rings. Indexing the limit by presentations avoids
having to choose one. Any two indices map onwards to a common refinement
(`RationalIndex.directed`, via the product presentation), so presentations of the same subset
are constrained through a common refinement. That is weaker than identifying their components,
which would need the unproved initiality.

**The comparison with Wedhorn's limit over rational *subsets* is not proved here.** It is an
initiality (cofinality) statement about the forgetful functor from presentations to rational
opens: expected, but not formalized, and nothing in this file depends on it. Because it is
unproved, nothing here is named `structurePresheaf` or claimed to *be* `𝒪_X` — the declarations
say `presentationLimit`, and so does the directory holding them. The identification, once proved,
should be a theorem relating the two limits rather than a renaming of this one, and
`Spa/StructurePresheaf/` is left free for the file that proves it.

## Provenance

Adapted from AINTLIB's `StructurePresheafLimit.lean` (see References), including the name
`RationalIndex`. The model deliberately diverges: the source hand-builds the limit as a subring
`limitSections V` of a product carrying the subspace topology and proves closedness,
completeness, separatedness and functoriality one by one, while here the value is the
categorical `limit` in `CompleteSeparatedTopCommRingCat`, so all of that is supplied by the
category (#3735, #3736). The source's object is not an object of a category and so cannot be
handed to `CategoryTheory.Presheaf.IsSheaf`, which is what the sheafiness definition below
needs. Its `IsSheafy` is a typeclass on the ring; the `P`-relative Prop here is distinct.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/StructurePresheafLimit.lean`.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory CategoryTheory.Limits _root_.TopologicalSpace TauCeti.Huber

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **The index of the presentation-indexed limit**: presentations with open numerator ideal —
the rational-basis condition of `spaRationalFamily` — whose rational subset is contained in
`V`. Without the openness condition the index would range over presentations outside the
rational basis.

The openness condition is necessary but not evidently sufficient: `Presentation` also carries
`hasDenominatorPower`, which this repository nowhere derives from `IsOpen (Ideal.span num)`. So
the index may be a proper subfamily of the rational opens contained in `V`, and showing it covers
all of them is part of the outstanding comparison, not something recorded here. -/
@[ext]
structure RationalIndex (P : PairOfDefinition A) (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) where
  /-- The presentation. -/
  pres : P.Presentation
  /-- Its numerator ideal is open: the presentation presents a member of the rational basis. -/
  isOpen_span_num : IsOpen (Ideal.span (pres.num : Set A) : Set A)
  /-- Its rational subset is contained in `V`. -/
  spaRationalOpen_le : spaRationalOpen Aplus pres.num pres.den ≤ V

variable {P : PairOfDefinition A} {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

/-- Refinement of the underlying presentations orders the index. -/
instance : Preorder (RationalIndex P Aplus V) :=
  Preorder.lift RationalIndex.pres

omit [IsTopologicalRing A] in
/-- The order on the index is refinement of the underlying presentations. -/
theorem RationalIndex.le_def {i j : RationalIndex P Aplus V} : i ≤ j ↔ i.pres ≤ j.pres :=
  Iff.rfl

/-- **The index is directed**: the product presentation of two indices is again an index — its
numerator span is open by `isOpen_span_insert_mul_insert` (this is what the insert-augmented
numerators of `Presentation.commonRefinement` are for), and its rational open is the
intersection of the
factors' (`spaRationalOpen_inf`), hence contained in `V` through either factor.
Presentations
of the same rational subset are therefore constrained through a common refinement — weaker than
identifying their components, which needs the unproved initiality. -/
theorem RationalIndex.directed (i j : RationalIndex P Aplus V) :
    ∃ k : RationalIndex P Aplus V, i ≤ k ∧ j ≤ k := by
  classical
  refine ⟨⟨i.pres.commonRefinement j.pres, ?_, ?_⟩,
    i.pres.le_commonRefinement_left j.pres, i.pres.le_commonRefinement_right j.pres⟩
  · rw [PairOfDefinition.Presentation.commonRefinement_num]
    exact isOpen_span_insert_mul_insert P i.isOpen_span_num j.isOpen_span_num
  · rw [PairOfDefinition.Presentation.commonRefinement_num,
      PairOfDefinition.Presentation.commonRefinement_den,
      ← spaRationalOpen_inf]
    exact inf_le_left.trans i.spaRationalOpen_le

/-- The directedness instance. It is **not** what makes the limit exist —
`CompleteSeparatedTopCommRingCat` has all small limits
(`Topology/Category/TopCommRingCat/CompleteSeparated/Limits.lean`) — and nothing in this file
consumes it. It is recorded for the eventual cofinality/initiality argument. -/
instance : IsDirected (RationalIndex P Aplus V) (· ≤ ·) :=
  ⟨RationalIndex.directed⟩

variable (P) in
/-- Forgetting the containment is a functor to the category of all presentations.

`@[expose]`, like `presentationFunctor`: the equation `rationalIndexDiagram_map` below is
unstatable unless the functors composing the diagram unfold definitionally — its two sides
otherwise live in different hom-types. -/
@[expose]
def rationalIndexInclusion (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    RationalIndex P Aplus V ⥤ P.Presentation :=
  Monotone.functor (f := RationalIndex.pres) fun _ _ h ↦ h

variable (P) in
/-- **The diagram the limit is taken over**: each presentation with open numerator ideal and
rational subset inside `V` contributes `A⟨T/s⟩`, and a refinement contributes its restriction
morphism. -/
@[expose]
noncomputable def rationalIndexDiagram (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    RationalIndex P Aplus V ⥤ CompleteSeparatedTopCommRingCat.{v} :=
  rationalIndexInclusion P Aplus V ⋙ P.presentationFunctor

/-- The diagram's value at an index is the completed rational localization of its
presentation. -/
@[simp]
theorem rationalIndexDiagram_obj (i : RationalIndex P Aplus V) :
    (rationalIndexDiagram P Aplus V).obj i = i.pres.completionLocObj := (rfl)

/-- The diagram's value at a refinement is its restriction morphism. -/
@[simp]
theorem rationalIndexDiagram_map {i j : RationalIndex P Aplus V} (h : i ⟶ j) :
    (rationalIndexDiagram P Aplus V).map h =
      PairOfDefinition.Presentation.restrictionHom (leOfHom h) := (rfl)

variable (P) in
/-- **The value of the presentation-indexed presheaf on an open**: the limit of `A⟨T/s⟩` over the
presentations with open numerator ideal whose rational subset is contained in `V`
(Wedhorn §8.1). The limit exists because `CompleteSeparatedTopCommRingCat` has all small limits.

The body is sealed. A consumer works through the universal property below —
`presentationLimitπ` for a component, `presentationLimitObj_hom_ext` to prove two maps into it
equal, and `presentationLimitLift` with `presentationLimitLift_π` to build one — rather than
through the fact that this happens to be Mathlib's chosen `limit`. -/
noncomputable def presentationLimitObj (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    CompleteSeparatedTopCommRingCat.{v} :=
  limit (rationalIndexDiagram P Aplus V)

variable (P) in
/-- **The projection of the presentation-indexed limit at one index.** With
`presentationLimitObj`'s body sealed this is how a component is reached; `presentationLimitMap_π`
below states how it interacts with restriction. -/
noncomputable def presentationLimitπ (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (i : RationalIndex P Aplus V) :
    presentationLimitObj P Aplus V ⟶ (rationalIndexDiagram P Aplus V).obj i :=
  limit.π (rationalIndexDiagram P Aplus V) i

variable (P) in
/-- **The projections form a cone over the diagram**: composing a projection with a diagram map is
the projection at the target. This is `limit.w` for this diagram, stated through
`presentationLimitπ` so that a consumer can see the compatibility without unfolding
`presentationLimitObj`'s sealed body.

Deliberately **not** `@[simp]`, and neither is any restatement of it — both options were tried
against `lint-env` and rejected. As written, `rationalIndexDiagram_map` (itself `@[simp]`)
rewrites this left-hand side into `Presentation.restrictionHom` form, so it is not in simp-normal
form. Restating it *at* that normal form fails differently: `restrictionHom` takes the containment
as a proof argument, so simp has no matchable key and the rule "does not simplify when using the
simp lemma on itself", i.e. would never fire. The compatibility is therefore stated as a plain
theorem; a consumer needing it under `simp` converts with `rationalIndexDiagram_map`. -/
theorem presentationLimitπ_map {i j : RationalIndex P Aplus V} (f : i ⟶ j) :
    presentationLimitπ P Aplus V i ≫ (rationalIndexDiagram P Aplus V).map f =
      presentationLimitπ P Aplus V j :=
  limit.w (rationalIndexDiagram P Aplus V) f

/-- **Hom-extensionality for the presentation-indexed limit**: two morphisms into it are equal
once all their projections agree. `P`, `Aplus` and `V` are implicit here, being determined by the
morphisms. -/
theorem presentationLimitObj_hom_ext {W : CompleteSeparatedTopCommRingCat.{v}}
    {f g : W ⟶ presentationLimitObj P Aplus V}
    (h : ∀ i, f ≫ presentationLimitπ P Aplus V i = g ≫ presentationLimitπ P Aplus V i) :
    f = g :=
  limit.hom_ext h

variable (P) in
/-- **The morphism into the limit determined by a compatible family**: the universal property's
existence half, with `presentationLimitLift_π` as its characteristic equation and
`presentationLimitObj_hom_ext` giving uniqueness. -/
noncomputable def presentationLimitLift (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (c : Cone (rationalIndexDiagram P Aplus V)) :
    c.pt ⟶ presentationLimitObj P Aplus V :=
  limit.lift (rationalIndexDiagram P Aplus V) c

/-- **The characteristic equation of `presentationLimitLift`**: its projection at an index is the
cone's leg there. -/
@[simp]
theorem presentationLimitLift_π (c : Cone (rationalIndexDiagram P Aplus V))
    (i : RationalIndex P Aplus V) :
    presentationLimitLift P Aplus V c ≫ presentationLimitπ P Aplus V i = c.π.app i :=
  limit.lift_π c i

variable (P) in
/-- Enlarging the open along `W ≤ V` includes the smaller index into the larger: a presentation
whose rational subset is contained in `W` has it contained in `V`. -/
@[expose]
def rationalIndexInclusionOfLE {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    RationalIndex P Aplus W ⥤ RationalIndex P Aplus V :=
  Monotone.functor
    (f := fun i ↦ ⟨i.pres, i.isOpen_span_num, i.spaRationalOpen_le.trans h⟩) fun _ _ hle ↦ hle

omit [IsTopologicalRing A] in
/-- Including along `le_refl` is the identity on the index. -/
theorem rationalIndexInclusionOfLE_refl :
    rationalIndexInclusionOfLE P (le_refl V) = 𝟭 (RationalIndex P Aplus V) := (rfl)

omit [IsTopologicalRing A] in
/-- Including twice is including once. -/
theorem rationalIndexInclusionOfLE_comp {V W X : Opens ↥(spa Aplus)} (h₁ : X ≤ W) (h₂ : W ≤ V) :
    rationalIndexInclusionOfLE P h₁ ⋙ rationalIndexInclusionOfLE P h₂ =
      rationalIndexInclusionOfLE P (h₁.trans h₂) := (rfl)

/-- **Reindexing the larger diagram along the inclusion is the smaller diagram.** This is the
identity the limit's reindexing lemmas consume; naming it is what lets `limit.pre_π` be reached
by `rw` instead of `erw`. -/
theorem rationalIndexInclusionOfLE_comp_diagram {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    rationalIndexInclusionOfLE P h ⋙ rationalIndexDiagram P Aplus V =
      rationalIndexDiagram P Aplus W := (rfl)

variable (P) in
/-- **The restriction morphism of a containment `W ≤ V`**: the limit over
the presentations inside `V` (with open numerator ideal) maps to the limit over the smaller
index, by reindexing along `rationalIndexInclusionOfLE`. The body is sealed: everything a
consumer needs is `presentationLimitMap_π`, `_refl` and `_comp` below.

Mathlib's `limit.pre_π` does *not* match this syntactically: it is stated with
`limit.π (E ⋙ F)`, and seeing `rationalIndexInclusionOfLE _ _ ⋙ rationalIndexDiagram _ _ _` as
`rationalIndexDiagram _ _ _` needs `rationalIndexInclusionOfLE_comp_diagram`. The consumer-facing
equations are `presentationLimitMap_π`, `presentationLimitMap_refl` and
`presentationLimitMap_comp` below; none of them requires reproducing that step. -/
noncomputable def presentationLimitMap {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    presentationLimitObj P Aplus V ⟶ presentationLimitObj P Aplus W :=
  limit.pre (rationalIndexDiagram P Aplus V) (rationalIndexInclusionOfLE P h)

variable (P) in
/-- **The characteristic equation of `presentationLimitMap`**: composing with a projection of the
smaller limit is the projection of the larger one at the included index. This is `limit.pre_π`
for this diagram, stated at the shape consumers actually meet.

The term type-checks because `rationalIndexInclusionOfLE_comp_diagram` holds: `limit.pre_π`'s
`E ⋙ F` is `rationalIndexInclusionOfLE P h ⋙ rationalIndexDiagram P Aplus V`, definitionally the
smaller diagram.

`@[simp]` but deliberately not `@[reassoc (attr := simp)]`, unlike `presentationLimitMap_comp`
below: the generated `presentationLimitMap_π_assoc` is provable from this lemma by `simp` alone,
because the right-hand side is a bare projection, and `lint-env`'s simpNF pass rejects it. -/
@[simp]
theorem presentationLimitMap_π {V W : Opens ↥(spa Aplus)} (h : W ≤ V)
    (j : RationalIndex P Aplus W) :
    presentationLimitMap P h ≫ presentationLimitπ P Aplus W j =
      presentationLimitπ P Aplus V ((rationalIndexInclusionOfLE P h).obj j) :=
  limit.pre_π (F := rationalIndexDiagram P Aplus V) (E := rationalIndexInclusionOfLE P h) j

variable (P) in
/-- Restricting along `le_refl` is the identity. The defeq consumed is
`rationalIndexInclusionOfLE_refl`: the included index of `j` along `le_refl` is `j`. -/
@[simp]
theorem presentationLimitMap_refl (V : Opens ↥(spa Aplus)) :
    presentationLimitMap P (le_refl V) = 𝟙 (presentationLimitObj P Aplus V) :=
  presentationLimitObj_hom_ext fun j ↦
    (presentationLimitMap_π P (le_refl V) j).trans (Category.id_comp _).symm

variable (P) in
/-- Restricting twice is restricting once. This is `limit.pre_pre`, and the defeq consumed is
`rationalIndexInclusionOfLE_comp`: composing the two inclusions is the inclusion of the composite
containment. -/
@[reassoc (attr := simp)]
theorem presentationLimitMap_comp {V W X : Opens ↥(spa Aplus)} (h₁ : X ≤ W) (h₂ : W ≤ V) :
    presentationLimitMap P h₂ ≫ presentationLimitMap P h₁ =
      presentationLimitMap P (h₁.trans h₂) :=
  limit.pre_pre (rationalIndexDiagram P Aplus V) (rationalIndexInclusionOfLE P h₂)
    (rationalIndexInclusionOfLE P h₁)

/-- **The presentation-indexed presheaf** on the adic spectrum of `Aplus`, valued in
`CompleteSeparatedTopCommRingCat`: on each open the limit of the completed rational
localizations of the presentations with open numerator ideal inside it, restricting along
containments by reindexing.

This is the candidate for Wedhorn's `𝒪_X` (§8.1). It is not identified with it here: that needs
the initiality of the forgetful functor to rational opens, which is not proved — see the module
docstring. -/
@[expose]
noncomputable def presentationLimitPresheaf (P : PairOfDefinition A) (Aplus : Subring A) :
    (Opens ↥(spa Aplus))ᵒᵖ ⥤ CompleteSeparatedTopCommRingCat.{v} where
  obj V := presentationLimitObj P Aplus V.unop
  map h := presentationLimitMap P (leOfHom h.unop)
  -- Both laws are the corresponding equations for `presentationLimitMap`, which state the
  -- reindexing identities once rather than re-deriving them from `limit.pre_π` here. Those two
  -- lemmas, not these fields, are what a simp-normalised goal reaches for.
  map_id V := presentationLimitMap_refl P V.unop
  map_comp _ _ := (presentationLimitMap_comp P _ _).symm

/-- The presheaf's value on an open is `presentationLimitObj`. -/
@[simp]
theorem presentationLimitPresheaf_obj (P : PairOfDefinition A) (Aplus : Subring A)
    (V : (Opens ↥(spa Aplus))ᵒᵖ) :
    (presentationLimitPresheaf P Aplus).obj V = presentationLimitObj P Aplus V.unop := (rfl)

/-- The presheaf's action on a containment is `presentationLimitMap`. -/
@[simp]
theorem presentationLimitPresheaf_map (P : PairOfDefinition A) (Aplus : Subring A)
    {V W : (Opens ↥(spa Aplus))ᵒᵖ} (h : V ⟶ W) :
    (presentationLimitPresheaf P Aplus).map h = presentationLimitMap P (leOfHom h.unop) := (rfl)

/-- **The presentation-indexed presheaf of `P` over `Aplus` is a sheaf**: that presheaf
built from
`P`'s presentations is a sheaf, in the sense of Mathlib's `CategoryTheory.Presheaf.IsSheaf` for
the Grothendieck topology of the adic spectrum of `Aplus`.

The definition is deliberately Mathlib's and not Wedhorn's equalizer condition or a Čech
statement; those are theorems *about* this, to be proved as `iff` lemmas rather than taken as
the definition.

This is a property of the pair `(P, Aplus)`, not yet of a Huber pair `(A, A⁺)`: `Aplus` is an
arbitrary subring, and independence of the chosen pair of definition — that `locTopology` and
`completionLocObj` do not depend on `P` — is outstanding; nothing in the repo yet compares two
pairs of definition. The roadmap's names `IsSheafyPair A Aplus`, `IsSheafyRing A` and
`IsStablySheafyRing A` are all left free for the `P`-independent notions this one feeds once
that independence is available. -/
def _root_.TauCeti.Huber.PairOfDefinition.HasSheafyPresentationLimit (P : PairOfDefinition A)
    (Aplus : Subring A) : Prop :=
  CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
    (presentationLimitPresheaf P Aplus)

/-- `PairOfDefinition.HasSheafyPresentationLimit` unfolds to Mathlib's sheaf condition. The body
is not
exported, so this is how a consumer moves between the two. -/
theorem _root_.TauCeti.Huber.PairOfDefinition.hasSheafyPresentationLimit_iff
    (P : PairOfDefinition A) (Aplus : Subring A) :
    P.HasSheafyPresentationLimit Aplus ↔
      CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
        (presentationLimitPresheaf P Aplus) := Iff.rfl

end

end TauCeti.ValuationSpectrum
