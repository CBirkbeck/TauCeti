/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.LocalizationTopology.CompleteSeparated.RefinementCategory
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Limits

/-!
# The structure presheaf of an adic spectrum

Wedhorn §8.1 assigns `A⟨T/s⟩` to the rational subset `R(T/s)` and extends the assignment to an
arbitrary open `V ⊆ Spa(A,A⁺)` by a limit of completed rational localizations. This file
constructs that limit.

The index is `RationalIndex`: a presentation with open numerator ideal — the rational-basis
condition — whose rational subset is contained in `V`, ordered by refinement.
`CompleteSeparated/RefinementCategory.lean` already makes the assignment `p ↦ A⟨p.num / p.den⟩`
functorial on presentations, so the diagram is obtained by restricting that functor along the
forgetful map, and the value is its limit — which exists because
`CompleteSeparatedTopCommRingCat` has all small limits.

Everything here is stated for an arbitrary `Subring` of a topological ring carrying a pair of
definition. It is Wedhorn's structure presheaf only under his standing hypotheses — a Huber
ring, a ring of integral elements — none of which is imposed by the definitions; the sibling
`spa` and `rationalSubset` carry the same convention.

## Main definitions

* `TauCeti.ValuationSpectrum.RationalIndex` : the index category for an open.
* `TauCeti.ValuationSpectrum.rationalIndexDiagram` : the diagram it indexes.
* `TauCeti.ValuationSpectrum.structurePresheafObj` : the value `𝒪_X(V)`.
* `TauCeti.ValuationSpectrum.structurePresheafMap` : the restriction morphism of a containment.
* `TauCeti.ValuationSpectrum.structurePresheaf` : the presheaf itself.
* `TauCeti.Huber.PairOfDefinition.IsSheafy` : the chosen presentation data is sheafy over
  `Aplus`, i.e. that presheaf is a sheaf.

## Main results

* `TauCeti.Huber.PairOfDefinition.isSheafy_iff` : sheafiness unfolds to Mathlib's sheaf
  condition (`IsSheafy` is not exposed; this is the route across).
* `structurePresheaf_obj`, `structurePresheaf_map` : the simp interface of the presheaf.
* `RationalIndex.directed` : the index is directed, so presentations of the same subset never
  sit as independent factors in the limit.

The limit interface for `𝒪_X(V)` is Mathlib's own: `structurePresheafObj` and
`structurePresheafMap` are `@[expose]`d as `limit (rationalIndexDiagram P Aplus V)` and
`limit.pre …`, so `limit.π`, `limit.lift`, `limit.hom_ext`, `limit.pre_π` and `limit.pre_pre`
apply to them directly — no parallel projection API is introduced.

## Why the index is presentations and not subsets

`A⟨T/s⟩` is built from the data `(T, s)`, and two presentations of the *same* rational subset
give canonically isomorphic but not equal rings. Indexing the limit by presentations avoids
having to choose one. Any two indices map onwards to a common refinement
(`RationalIndex.directed`, via the product presentation), so presentations of the same subset
never sit as independent factors in the limit; the full comparison with Wedhorn's limit over
rational *subsets* is an initiality statement about the indexing functor and is not yet
formalized — it is expected, not proved, and nothing in this file depends on it.

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

/-- **The index of the limit defining `𝒪_X(V)`**: presentations with open numerator ideal —
the rational-basis condition of `spaRationalFamily` — whose rational subset is contained in
`V`. Without the openness condition the index would range over presentations outside the
rational basis, and the limit would not be over Wedhorn's rational opens. -/
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
numerators of `Presentation.prod` are for), and its rational open is the intersection of the
factors' (`spaRationalOpen_inf`), hence contained in `V` through either factor. Presentations
of the same rational subset therefore never sit as independent factors in the limit below. -/
theorem RationalIndex.directed (i j : RationalIndex P Aplus V) :
    ∃ k : RationalIndex P Aplus V, i ≤ k ∧ j ≤ k := by
  classical
  refine ⟨⟨i.pres.prod j.pres, ?_, ?_⟩,
    i.pres.le_prod_left j.pres, i.pres.le_prod_right j.pres⟩
  · rw [PairOfDefinition.Presentation.prod_num]
    exact isOpen_span_insert_mul_insert P i.isOpen_span_num j.isOpen_span_num
  · rw [PairOfDefinition.Presentation.prod_num, PairOfDefinition.Presentation.prod_den,
      spaRationalOpen_inf]
    exact inf_le_left.trans i.spaRationalOpen_le

/-- The directedness instance the limit over the index consumes. -/
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
/-- **The diagram `𝒪_X(V)` is the limit of**: each presentation with open numerator ideal and
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
/-- **The value of the structure presheaf on an open**: the limit of `A⟨T/s⟩` over the
presentations with open numerator ideal whose rational subset is contained in `V`
(Wedhorn §8.1). The limit exists because `CompleteSeparatedTopCommRingCat` has all small
limits; `@[expose]` publishes the body, so Mathlib's `limit.π`/`limit.lift`/`limit.hom_ext`
apply to it directly. -/
@[expose]
noncomputable def structurePresheafObj (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    CompleteSeparatedTopCommRingCat.{v} :=
  limit (rationalIndexDiagram P Aplus V)

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

variable (P) in
/-- **The restriction morphism `𝒪_X(V) ⟶ 𝒪_X(W)` of a containment `W ≤ V`**: the limit over
the presentations inside `V` (with open numerator ideal) maps to the limit over the smaller
index, by reindexing along `rationalIndexInclusionOfLE`. `@[expose]`d as `limit.pre …`, so
`limit.pre_π` and `limit.pre_pre` apply to it directly. -/
@[expose]
noncomputable def structurePresheafMap {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    structurePresheafObj P Aplus V ⟶ structurePresheafObj P Aplus W :=
  limit.pre (rationalIndexDiagram P Aplus V) (rationalIndexInclusionOfLE P h)

/-- **The structure presheaf** `V ↦ 𝒪_X(V)` on the adic spectrum of `Aplus`, valued in
`CompleteSeparatedTopCommRingCat` (Wedhorn §8.1): on each open the limit of the completed
rational localizations of the presentations with open numerator ideal inside it, restricting
along containments by reindexing. -/
@[expose]
noncomputable def structurePresheaf (P : PairOfDefinition A) (Aplus : Subring A) :
    (Opens ↥(spa Aplus))ᵒᵖ ⥤ CompleteSeparatedTopCommRingCat.{v} where
  obj V := structurePresheafObj P Aplus V.unop
  map h := structurePresheafMap P (leOfHom h.unop)
  -- Both functor laws are reindexing identities for the limit, through the named functor
  -- identities `rationalIndexInclusionOfLE_refl`/`_comp`.
  map_id V := by
    apply limit.hom_ext
    intro j
    -- `erw`, not `rw`: matching `limit.pre_π` needs
    -- `rationalIndexInclusionOfLE _ _ ⋙ rationalIndexDiagram _ _ _` to be seen as
    -- `rationalIndexDiagram _ _ _`; the sealed `Presentation.RefinedBy` (reached through the
    -- `Preorder` instance inside the index category's homs) blocks that identification at the
    -- transparency `rw` uses.
    erw [limit.pre_π, Category.id_comp]
    rfl
  map_comp {X Y Z} f g := by
    simp only [structurePresheafMap]
    exact (limit.pre_pre (rationalIndexDiagram P Aplus X.unop)
      (rationalIndexInclusionOfLE P (leOfHom f.unop))
      (rationalIndexInclusionOfLE P (leOfHom g.unop))).symm

/-- The presheaf's value on an open is `structurePresheafObj`. -/
@[simp]
theorem structurePresheaf_obj (P : PairOfDefinition A) (Aplus : Subring A)
    (V : (Opens ↥(spa Aplus))ᵒᵖ) :
    (structurePresheaf P Aplus).obj V = structurePresheafObj P Aplus V.unop := (rfl)

/-- The presheaf's action on a containment is `structurePresheafMap`. -/
@[simp]
theorem structurePresheaf_map (P : PairOfDefinition A) (Aplus : Subring A)
    {V W : (Opens ↥(spa Aplus))ᵒᵖ} (h : V ⟶ W) :
    (structurePresheaf P Aplus).map h = structurePresheafMap P (leOfHom h.unop) := (rfl)

/-- **The presentation data `P` is sheafy over `Aplus`**: the structure presheaf built from
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
def _root_.TauCeti.Huber.PairOfDefinition.IsSheafy (P : PairOfDefinition A)
    (Aplus : Subring A) : Prop :=
  CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
    (structurePresheaf P Aplus)

/-- `PairOfDefinition.IsSheafy` unfolds to Mathlib's sheaf condition. The body is not
exported, so this is how a consumer moves between the two. -/
theorem _root_.TauCeti.Huber.PairOfDefinition.isSheafy_iff (P : PairOfDefinition A)
    (Aplus : Subring A) :
    P.IsSheafy Aplus ↔
      CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
        (structurePresheaf P Aplus) := Iff.rfl

end

end TauCeti.ValuationSpectrum
