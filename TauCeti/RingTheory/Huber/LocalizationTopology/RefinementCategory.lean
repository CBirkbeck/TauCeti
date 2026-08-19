/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import TauCeti.RingTheory.Huber.LocalizationTopology.CompleteSeparated.Restriction

/-!
# The refinement preorder on presentations, and the functor it indexes

A presentation of a rational localisation of `A` is a finite set of numerators, a denominator, and
the standing hypothesis `HasDenominatorPower` under which `A⟨T/s⟩` is built. `Presentation`
bundles the three, taking the localisation to be `Localization.Away s` so that the bundle is a
type rather than a family over types.

`Presentation.RefinedBy` is the refinement relation of `LocalizationTopology.Restriction`, with the
cofactor existentially quantified: `q` refines `p` when some `r` has `q.den = p.den * r` and carries
every numerator of `p` into a numerator of `q`. It is reflexive (`r = 1`) and transitive
(`r * r₂`), so it is a `Preorder`, and the associated category is what the structure presheaf is
indexed by.

`presentationFunctor` is then the assignment `p ↦ A⟨p.num / p.den⟩` as a functor into
`CompleteSeparatedTopCommRingCat`, with the restriction morphisms as its action on arrows.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.Presentation` : a presentation `(T, s, hden)`.
* `TauCeti.Huber.PairOfDefinition.Presentation.RefinedBy` : the refinement relation.
* `TauCeti.Huber.PairOfDefinition.presentationFunctor` : the functor into
  `CompleteSeparatedTopCommRingCat`.

## Why the cofactor must be quantified away

A category whose arrows carried the cofactor would not be a preorder, and the index of the
structure presheaf has to be a preorder: `𝒪_X(V)` is a limit over *the presentations refining `V`*,
a condition on presentations and not extra data. Quantifying `r` away is only legitimate because
the restriction morphism does not depend on it — `restrictionObjHom_congr` — which is what lets
`map` below be defined by an arbitrary choice of cofactor and still be functorial.

## Provenance

Adapted from AINTLIB's `StructurePresheafLimit.lean` (see References): the idea of indexing the
structure presheaf by presentation data rather than by rational subsets, and the refinement
relation between presentations, are that file's. The bundling differs deliberately: AINTLIB
threads `RationalLocData` records through explicit hypotheses, while here a `Presentation` packs
`(num, den, hden)` so that refinement is a `Preorder` and the assignment `p ↦ A⟨p.num / p.den⟩`
is a functor — the shape a categorical limit needs.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1–§8.2.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/StructurePresheafLimit.lean`.
-/

namespace TauCeti.Huber

open CategoryTheory TauCeti.TopCommRingCat

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

namespace PairOfDefinition

/-! ### Presentations and the refinement preorder -/

/-- **A presentation of a rational localisation of `A`**: numerators, a denominator, and the
standing hypothesis under which `A⟨T/s⟩` is built. The localisation is taken to be
`Localization.Away den`, so that presentations form a type. -/
structure Presentation (P : PairOfDefinition A) where
  /-- The numerators `t₁, …, tₙ`. -/
  num : Finset A
  /-- The denominator `s`. -/
  den : A
  /-- Some power of the ideal of definition already has all of its fractions in `A₀[T/s]`. -/
  hden : HasDenominatorPower P num den (Localization.Away den)

variable {P : PairOfDefinition A}

/-- **`p` is refined by `q`**: some cofactor `r` writes `q.den` as `p.den * r` and carries every
numerator of `p` to a numerator of `q`. This is the relation of
`PairOfDefinition.restrictionRingHom`, with the cofactor existentially quantified.

The receiver is the *coarser* presentation, matching `p ≤ q`. -/
def Presentation.RefinedBy (p q : Presentation P) : Prop :=
  ∃ r : A, q.den = p.den * r ∧ ∀ t ∈ p.num, t * r ∈ q.num

omit [IsTopologicalRing A] in
/-- The witness facts for the trivial refinement, with cofactor `1`. -/
theorem Presentation.refinedBy_one (p : Presentation P) :
    p.den = p.den * 1 ∧ ∀ t ∈ p.num, t * 1 ∈ p.num :=
  ⟨(mul_one _).symm, fun t ht ↦ by rwa [mul_one]⟩

omit [IsTopologicalRing A] in
/-- The witness facts for a composite refinement: the cofactors multiply. -/
theorem Presentation.refinedBy_mul {p q w : Presentation P} {r r₂ : A}
    (hr : q.den = p.den * r) (hT : ∀ t ∈ p.num, t * r ∈ q.num)
    (hr₂ : w.den = q.den * r₂) (hT₂ : ∀ t ∈ q.num, t * r₂ ∈ w.num) :
    w.den = p.den * (r * r₂) ∧ ∀ t ∈ p.num, t * (r * r₂) ∈ w.num :=
  ⟨by rw [hr₂, hr, mul_assoc],
    fun t ht ↦ by rw [← mul_assoc]; exact hT₂ _ (hT t ht)⟩

omit [IsTopologicalRing A] in
/-- Every presentation refines itself, with cofactor `1`. -/
theorem Presentation.refinedBy_self (p : Presentation P) : p.RefinedBy p :=
  ⟨1, p.refinedBy_one.1, p.refinedBy_one.2⟩

omit [IsTopologicalRing A] in
/-- Refinements compose: the cofactors multiply. -/
theorem Presentation.RefinedBy.trans {p q w : Presentation P} (hpq : p.RefinedBy q)
    (hqw : q.RefinedBy w) : p.RefinedBy w := by
  obtain ⟨r, hr, hT⟩ := hpq
  obtain ⟨r₂, hr₂, hT₂⟩ := hqw
  exact ⟨r * r₂, (Presentation.refinedBy_mul hr hT hr₂ hT₂).1,
    (Presentation.refinedBy_mul hr hT hr₂ hT₂).2⟩

/-- Refinement is a preorder, by `Presentation.refinedBy_self` and
`Presentation.RefinedBy.trans`. -/
instance : Preorder (Presentation P) where
  le := Presentation.RefinedBy
  le_refl := Presentation.refinedBy_self
  le_trans _ _ _ := Presentation.RefinedBy.trans

omit [IsTopologicalRing A] in
theorem Presentation.le_def {p q : Presentation P} : p ≤ q ↔ p.RefinedBy q := Iff.rfl

omit [IsTopologicalRing A] in
/-- **The refinement relation, unfolded.** The body of `RefinedBy` is not exported, so this is how
a consumer produces or consumes a refinement. -/
theorem Presentation.refinedBy_iff {p q : Presentation P} :
    p.RefinedBy q ↔ ∃ r : A, q.den = p.den * r ∧ ∀ t ∈ p.num, t * r ∈ q.num := Iff.rfl

omit [IsTopologicalRing A] in
/-- **The chosen cofactor of a refinement.** `Presentation.hom` and the lemmas about it cross
the `≤`-to-existential boundary through this accessor and its two spec lemmas, in one place. -/
noncomputable def Presentation.cofactor {p q : Presentation P} (h : p ≤ q) : A :=
  (Presentation.le_def.mp h).choose

omit [IsTopologicalRing A] in
/-- The denominator of a refinement is the coarser denominator times the cofactor. -/
theorem Presentation.den_eq_mul_cofactor {p q : Presentation P} (h : p ≤ q) :
    q.den = p.den * Presentation.cofactor h :=
  (Presentation.le_def.mp h).choose_spec.1

omit [IsTopologicalRing A] in
/-- The cofactor carries numerators of the coarser presentation into the finer one. -/
theorem Presentation.mul_cofactor_mem {p q : Presentation P} (h : p ≤ q) {t : A}
    (ht : t ∈ p.num) : t * Presentation.cofactor h ∈ q.num :=
  (Presentation.le_def.mp h).choose_spec.2 t ht

omit [IsTopologicalRing A] in
/-- **Any two presentations admit a common refinement**: the product presentation, whose
numerators are the cross-terms `t * q.den` and `t' * p.den` and whose denominator is the product.
Its denominator-power hypothesis is `hasDenominatorPower_mul`, whose docstring calls exactly this
numerator set "the intended instance". Directedness is what makes the refinement preorder a
codirected index for the structure presheaf's limit: presentations of the same rational subset
never sit as independent factors, because both map onwards to any common refinement. -/
theorem Presentation.directed (p q : Presentation P) :
    ∃ w : Presentation P, p ≤ w ∧ q ≤ w := by
  classical
  refine ⟨⟨p.num.image (· * q.den) ∪ q.num.image (· * p.den), p.den * q.den,
    hasDenominatorPower_mul P p.num q.num _ p.den q.den (Localization.Away p.den)
      (Localization.Away q.den) (Localization.Away (p.den * q.den))
      (fun t ht ↦ Finset.mem_union_left _ (Finset.mem_image_of_mem _ ht))
      (fun t ht ↦ Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht))
      p.hden q.hden⟩,
    ⟨q.den, rfl, fun t ht ↦ Finset.mem_union_left _ (Finset.mem_image_of_mem _ ht)⟩,
    ⟨p.den, mul_comm p.den q.den, fun t ht ↦
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht)⟩⟩

omit [IsTopologicalRing A] in
/-- The refinement preorder is directed. -/
instance : IsDirected (Presentation P) (· ≤ ·) :=
  ⟨Presentation.directed⟩

/-! ### The functor into `CompleteSeparatedTopCommRingCat` -/

/-- The object `A⟨T/s⟩` attached to a presentation. -/
noncomputable abbrev Presentation.obj (p : Presentation P) : CompleteSeparatedTopCommRingCat.{v} :=
  completionLocObj P p.num p.den (Localization.Away p.den) p.hden

/-- The restriction morphism attached to a refinement, taking an arbitrary cofactor. It does not
depend on that choice: see `Presentation.hom_eq`. -/
noncomputable def Presentation.hom {p q : Presentation P} (h : p ≤ q) : p.obj ⟶ q.obj :=
  restrictionObjHom P p.num p.den _ p.hden q.num q.den _ q.hden
    (Presentation.cofactor h) (Presentation.den_eq_mul_cofactor h)
    fun _ ↦ Presentation.mul_cofactor_mem h

/-- `Presentation.hom` is computed by *any* cofactor witnessing the refinement, not only the
chosen one. This is `restrictionObjHom_congr` transported to the preorder. -/
theorem Presentation.hom_eq {p q : Presentation P} (h : p ≤ q) (r : A) (hr : q.den = p.den * r)
    (hT : ∀ t ∈ p.num, t * r ∈ q.num) :
    Presentation.hom h =
      restrictionObjHom P p.num p.den _ p.hden q.num q.den _ q.hden r hr hT :=
  restrictionObjHom_congr P p.num p.den _ p.hden q.num q.den _ q.hden
    (Presentation.cofactor h) r (Presentation.den_eq_mul_cofactor h)
    (fun _ ↦ Presentation.mul_cofactor_mem h) hr hT

/-- **The structure presheaf's diagram.** `p ↦ A⟨p.num / p.den⟩`, with the restriction morphisms
as its action on refinements. Functoriality is exactly `restrictionObjHom_self` and
`restrictionObjHom_comp_restrictionObjHom`, reached through `Presentation.hom_eq`.

`@[expose]` is load-bearing, for a narrower reason than exposure usually carries: with the body
sealed, `presentationFunctor_map` below does not typecheck *as a statement*. Its two sides live in
`(presentationFunctor P).obj p ⟶ (presentationFunctor P).obj q` and in `p.obj ⟶ q.obj`, and only
unfolding the functor identifies those types. `presentationFunctor_obj` is statable either way; it
is the `map` equation, and the definitional reindexing a limit over this category needs, that the
exposure provides. -/
@[expose]
noncomputable def presentationFunctor (P : PairOfDefinition A) :
    Presentation P ⥤ CompleteSeparatedTopCommRingCat.{v} where
  obj p := p.obj
  map {_ _} h := Presentation.hom h.le
  map_id p := by
    rw [Presentation.hom_eq (r := 1) (hr := p.refinedBy_one.1) (hT := p.refinedBy_one.2)]
    exact restrictionObjHom_self P p.num p.den _ p.hden
  map_comp {p q w} f g := by
    obtain ⟨r, hr, hT⟩ := f.le
    obtain ⟨r₂, hr₂, hT₂⟩ := g.le
    rw [Presentation.hom_eq f.le r hr hT, Presentation.hom_eq g.le r₂ hr₂ hT₂,
      Presentation.hom_eq (f ≫ g).le (r * r₂) (Presentation.refinedBy_mul hr hT hr₂ hT₂).1
        (Presentation.refinedBy_mul hr hT hr₂ hT₂).2]
    exact (restrictionObjHom_comp_restrictionObjHom P p.num p.den _ p.hden q.num q.den _ q.hden
      r hr hT w.num w.den _ w.hden r₂ hr₂ hT₂).symm

/-- The functor takes a presentation to its own object. -/
@[simp]
theorem presentationFunctor_obj (P : PairOfDefinition A) (p : Presentation P) :
    (presentationFunctor P).obj p = p.obj := rfl

/-- The functor takes a refinement to its restriction morphism. -/
@[simp]
theorem presentationFunctor_map (P : PairOfDefinition A) {p q : Presentation P} (h : p ⟶ q) :
    (presentationFunctor P).map h = Presentation.hom h.le := rfl

end PairOfDefinition

end

end TauCeti.Huber
