/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.RefinementCategory
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Limits

/-!
# The structure presheaf of an adic spectrum

Wedhorn §8.1 assigns `A⟨T/s⟩` to the rational subset `R(T/s)` and extends the assignment to an
arbitrary open `V ⊆ Spa(A,A⁺)` by a limit of completed rational localizations. This file
constructs that limit.

The index is `RationalIndex`: a presentation together with a proof that the rational subset it
presents is contained in `V`, ordered by refinement. `RefinementCategory` already makes the
assignment `p ↦ A⟨p.num / p.den⟩` functorial on presentations, so the diagram is obtained by
restricting that functor along the forgetful map, and the value is its limit — which exists
because `CompleteSeparatedTopCommRingCat` has all small limits.

Everything here is stated for an arbitrary `Subring` of a topological ring carrying a pair of
definition. It is Wedhorn's structure presheaf only under his standing hypotheses — a Huber
ring, a ring of integral elements, and presentations generating open ideals — none of which is
imposed by the definitions; the sibling `spa` and `rationalSubset` carry the same convention.

## Main definitions

* `TauCeti.ValuationSpectrum.RationalIndex` : the index category for an open.
* `TauCeti.ValuationSpectrum.rationalIndexDiagram` : the diagram it indexes.
* `TauCeti.ValuationSpectrum.structurePresheafObj` : the value `𝒪_X(V)`.
* `TauCeti.ValuationSpectrum.structurePresheafMap` : the restriction morphism of a containment.
* `TauCeti.ValuationSpectrum.structurePresheaf` : the presheaf itself.
* `TauCeti.Huber.PairOfDefinition.IsSheafyPair` : the chosen presentation data is sheafy over
  `Aplus`, i.e. that presheaf is a sheaf.

## Main results

* `TauCeti.Huber.PairOfDefinition.isSheafyPair_iff` : sheafiness unfolds to Mathlib's sheaf
  condition.
* `structurePresheafObj_def`, `structurePresheafMap_π`, `structurePresheaf_obj`,
  `structurePresheaf_map` : the limit interface of the sealed definitions.

## Why the index is presentations and not subsets

`A⟨T/s⟩` is built from the data `(T, s)`, and two presentations of the *same* rational subset
give canonically isomorphic but not equal rings. Indexing the limit by presentations avoids
having to choose one. Any two presentations map onwards to a common refinement
(`Presentation.directed`), so presentations of the same subset never sit as independent factors
in the limit; the full comparison with Wedhorn's limit over rational *subsets* is an initiality
statement about the indexing functor and is not yet formalized — it is expected, not proved,
and nothing in this file depends on it.

## Provenance

Adapted from AINTLIB's `StructurePresheafLimit.lean` (see References), including the name
`RationalIndex`. The model deliberately diverges: the source hand-builds the limit as a subring
`limitSections V` of a product carrying the subspace topology and proves closedness,
completeness, separatedness and functoriality one by one, while here the value is the
categorical `limit` in `CompleteSeparatedTopCommRingCat`, so all of that is supplied by the
category (#3735, #3736). The source's object is not an object of a category and so cannot be
handed to `CategoryTheory.Presheaf.IsSheaf`, which is what the sheafiness definition below
needs. Its `IsSheafy` names the *ring* notion, hence the distinct name here.

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

/-- **The index of the limit defining `𝒪_X(V)`**: presentations whose rational subset is
contained in `V`. -/
structure RationalIndex (P : PairOfDefinition A) (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) where
  /-- The presentation. -/
  pres : P.Presentation
  /-- Its rational subset is contained in `V`. -/
  le_open : spaRationalOpen Aplus pres.num pres.den ≤ V

variable {P : PairOfDefinition A} {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

/-- Refinement of the underlying presentations orders the index. -/
instance : Preorder (RationalIndex P Aplus V) :=
  Preorder.lift RationalIndex.pres

omit [IsTopologicalRing A] in
/-- The order on the index is refinement of the underlying presentations. -/
theorem RationalIndex.le_def {i j : RationalIndex P Aplus V} : i ≤ j ↔ i.pres ≤ j.pres :=
  Iff.rfl

variable (P) in
/-- Forgetting the containment is a functor to the category of all presentations.

`@[expose]`, like `presentationFunctor`: the equations `rationalIndexDiagram_map` and
`structurePresheafMap_π` below are unstatable unless the functors composing the diagram unfold
definitionally — their two sides otherwise live in different hom-types. -/
@[expose]
def rationalIndexInclusion (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    RationalIndex P Aplus V ⥤ P.Presentation :=
  Monotone.functor (f := RationalIndex.pres) fun _ _ h ↦ h

variable (P) in
/-- **The diagram `𝒪_X(V)` is the limit of**: each presentation with rational subset inside `V`
contributes `A⟨T/s⟩`, and a refinement contributes its restriction morphism. -/
@[expose]
noncomputable def rationalIndexDiagram (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    RationalIndex P Aplus V ⥤ CompleteSeparatedTopCommRingCat.{v} :=
  rationalIndexInclusion P Aplus V ⋙ P.presentationFunctor

/-- The diagram's value at an index is the completed rational localization of its
presentation. -/
@[simp]
theorem rationalIndexDiagram_obj (i : RationalIndex P Aplus V) :
    (rationalIndexDiagram P Aplus V).obj i = i.pres.obj := (rfl)

/-- The diagram's value at a refinement is its restriction morphism. -/
@[simp]
theorem rationalIndexDiagram_map {i j : RationalIndex P Aplus V} (h : i ⟶ j) :
    (rationalIndexDiagram P Aplus V).map h = PairOfDefinition.Presentation.hom (leOfHom h) := (rfl)

variable (P) in
/-- **The value of the structure presheaf on an open**: the limit of `A⟨T/s⟩` over the
presentations whose rational subset is contained in `V` (Wedhorn §8.1). The limit exists
because `CompleteSeparatedTopCommRingCat` has all small limits. -/
@[expose]
noncomputable def structurePresheafObj (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    CompleteSeparatedTopCommRingCat.{v} :=
  limit (rationalIndexDiagram P Aplus V)

/-- `structurePresheafObj` is the limit of the rational-index diagram. The body is not
exported, so this is how a consumer reaches the limit interface — `limit.π`, `limit.lift`,
`limit.hom_ext` — for `𝒪_X(V)`. -/
theorem structurePresheafObj_def (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    structurePresheafObj P Aplus V = limit (rationalIndexDiagram P Aplus V) := (rfl)

variable (P) in
/-- The projection of `𝒪_X(V)` onto the completed rational localization of an index. -/
@[expose]
noncomputable def structurePresheafπ (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (i : RationalIndex P Aplus V) :
    structurePresheafObj P Aplus V ⟶ (rationalIndexDiagram P Aplus V).obj i :=
  limit.π (rationalIndexDiagram P Aplus V) i

variable (P) in
/-- Enlarging the open along `W ≤ V` includes the smaller index into the larger: a presentation
whose rational subset is contained in `W` has it contained in `V`. -/
@[expose]
def rationalIndexOfLE {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    RationalIndex P Aplus W ⥤ RationalIndex P Aplus V :=
  Monotone.functor (f := fun i ↦ ⟨i.pres, i.le_open.trans h⟩) fun _ _ hle ↦ hle

variable (P) in
/-- **The restriction morphism `𝒪_X(V) ⟶ 𝒪_X(W)` of a containment `W ≤ V`**: the limit over
the presentations inside `V` maps to the limit over the smaller index, by reindexing along
`rationalIndexOfLE`. -/
@[expose]
noncomputable def structurePresheafMap {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    structurePresheafObj P Aplus V ⟶ structurePresheafObj P Aplus W :=
  limit.pre (rationalIndexDiagram P Aplus V) (rationalIndexOfLE P h)

/-- Restriction is computed on components: after restricting along `W ≤ V`, the projection onto
an index of `W` is the original projection onto that index viewed inside `V`. -/
@[simp]
theorem structurePresheafMap_π {V W : Opens ↥(spa Aplus)} (h : W ≤ V)
    (i : RationalIndex P Aplus W) :
    structurePresheafMap P h ≫ structurePresheafπ P Aplus W i =
      structurePresheafπ P Aplus V ⟨i.pres, i.le_open.trans h⟩ :=
  limit.pre_π (rationalIndexDiagram P Aplus V) (rationalIndexOfLE P h) i

/-- **The structure presheaf** `V ↦ 𝒪_X(V)` on the adic spectrum of `Aplus`, valued in
`CompleteSeparatedTopCommRingCat` (Wedhorn §8.1): on each open the limit of the completed
rational localizations of the presentations inside it, restricting along containments by
reindexing. -/
@[expose]
noncomputable def structurePresheaf (P : PairOfDefinition A) (Aplus : Subring A) :
    (Opens ↥(spa Aplus))ᵒᵖ ⥤ CompleteSeparatedTopCommRingCat.{v} where
  obj V := structurePresheafObj P Aplus V.unop
  map h := structurePresheafMap P (leOfHom h.unop)
  -- Both functor laws are reindexing identities for the limit: restricting along `le_refl` is
  -- the identity on the index, and restricting twice is restricting once.
  map_id V := by
    apply limit.hom_ext
    intro j
    -- `erw`, not `rw`: matching `limit.pre_π` asks for
    -- `rationalIndexOfLE _ _ ⋙ rationalIndexDiagram _ _ _` to be seen as
    -- `rationalIndexDiagram _ _ _`, and the sealed `Presentation.hom` blocks that at the
    -- transparency `rw` uses.
    erw [limit.pre_π, Category.id_comp]
    rfl
  map_comp {X Y Z} f g := by
    simp only [structurePresheafMap]
    exact (limit.pre_pre (rationalIndexDiagram P Aplus X.unop)
      (rationalIndexOfLE P (leOfHom f.unop))
      (rationalIndexOfLE P (leOfHom g.unop))).symm

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
pairs of definition. The bare name `IsSheafyPair` is reserved for the `(A, A⁺)`-only notion the
roadmap asks for, which this one becomes once that independence is available. Wedhorn
Definition 8.26 (the ring notion) and stable sheafiness are further separate definitions, and
neither is this one. -/
def _root_.TauCeti.Huber.PairOfDefinition.IsSheafyPair (P : PairOfDefinition A)
    (Aplus : Subring A) : Prop :=
  CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
    (structurePresheaf P Aplus)

/-- `PairOfDefinition.IsSheafyPair` unfolds to Mathlib's sheaf condition. The body is not
exported, so this is how a consumer moves between the two. -/
theorem _root_.TauCeti.Huber.PairOfDefinition.isSheafyPair_iff (P : PairOfDefinition A)
    (Aplus : Subring A) :
    P.IsSheafyPair Aplus ↔
      CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
        (structurePresheaf P Aplus) := Iff.rfl

end

end TauCeti.ValuationSpectrum
