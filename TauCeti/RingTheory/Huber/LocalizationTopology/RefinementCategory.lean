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

`Presentation.Refines` is the refinement relation of `LocalizationTopology.Restriction`, with the
cofactor existentially quantified: `q` refines `p` when some `r` has `q.den = p.den * r` and carries
every numerator of `p` into a numerator of `q`. It is reflexive (`r = 1`) and transitive
(`r * r₂`), so it is a `Preorder`, and the associated category is what the structure presheaf is
indexed by.

`presentationFunctor` is then the assignment `p ↦ A⟨p.num / p.den⟩` as a functor into
`CompleteSeparatedTopCommRingCat`, with the restriction morphisms as its action on arrows.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.Presentation` : a presentation `(T, s, hden)`.
* `TauCeti.Huber.PairOfDefinition.Presentation.Refines` : the refinement relation.
* `TauCeti.Huber.PairOfDefinition.presentationFunctor` : the functor into
  `CompleteSeparatedTopCommRingCat`.

## Why the cofactor must be quantified away

A category whose arrows carried the cofactor would not be a preorder, and the index of the
structure presheaf has to be a preorder: `𝒪_X(V)` is a limit over *the presentations refining `V`*,
a condition on presentations and not extra data. Quantifying `r` away is only legitimate because
the restriction morphism does not depend on it — `restrictionObjHom_congr` — which is what lets
`map` below be defined by an arbitrary choice of cofactor and still be functorial.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1–§8.2.
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

/-- **`q` refines `p`**: some cofactor `r` writes `q.den` as `p.den * r` and carries every
numerator of `p` to a numerator of `q`. This is the relation of
`PairOfDefinition.restrictionRingHom`, with the cofactor existentially quantified. -/
@[expose]
def Presentation.Refines (p q : Presentation P) : Prop :=
  ∃ r : A, q.den = p.den * r ∧ ∀ t ∈ p.num, t * r ∈ q.num

/-- Refinement is a preorder: a presentation refines itself with cofactor `1`, and refinements
compose with cofactor `r * r₂`. -/
instance : Preorder (Presentation P) where
  le := Presentation.Refines
  le_refl p := by exact ⟨1, (mul_one _).symm, fun t ht ↦ by rwa [mul_one]⟩
  le_trans _ _ _ hpq hqw := by
    obtain ⟨r, hr, hT⟩ := hpq
    obtain ⟨r₂, hr₂, hT₂⟩ := hqw
    exact ⟨r * r₂, by rw [hr₂, hr, mul_assoc],
      fun t ht ↦ by rw [← mul_assoc]; exact hT₂ _ (hT t ht)⟩

omit [IsTopologicalRing A] in
theorem Presentation.le_def {p q : Presentation P} : p ≤ q ↔ p.Refines q := Iff.rfl

/-! ### The functor into `CompleteSeparatedTopCommRingCat` -/

/-- The object `A⟨T/s⟩` attached to a presentation. -/
noncomputable abbrev Presentation.obj (p : Presentation P) : CompleteSeparatedTopCommRingCat.{v} :=
  completionLocObj P p.num p.den (Localization.Away p.den) p.hden

/-- The restriction morphism attached to a refinement, taking an arbitrary cofactor. It does not
depend on that choice: see `Presentation.hom_eq`. -/
@[expose]
noncomputable def Presentation.hom {p q : Presentation P} (h : p ≤ q) : p.obj ⟶ q.obj :=
  restrictionObjHom P p.num p.den _ p.hden q.num q.den _ q.hden
    h.choose h.choose_spec.1 h.choose_spec.2

/-- `Presentation.hom` is computed by *any* cofactor witnessing the refinement, not only the
chosen one. This is `restrictionObjHom_congr` transported to the preorder. -/
theorem Presentation.hom_eq {p q : Presentation P} (h : p ≤ q) (r : A) (hr : q.den = p.den * r)
    (hT : ∀ t ∈ p.num, t * r ∈ q.num) :
    Presentation.hom h =
      restrictionObjHom P p.num p.den _ p.hden q.num q.den _ q.hden r hr hT :=
  restrictionObjHom_congr P p.num p.den _ p.hden q.num q.den _ q.hden
    h.choose r h.choose_spec.1 h.choose_spec.2 hr hT

/-- **The structure presheaf's diagram.** `p ↦ A⟨p.num / p.den⟩`, with the restriction morphisms
as its action on refinements. Functoriality is exactly `restrictionObjHom_self` and
`restrictionObjHom_comp_restrictionObjHom`, reached through `Presentation.hom_eq`. -/
@[expose]
noncomputable def presentationFunctor (P : PairOfDefinition A) :
    Presentation P ⥤ CompleteSeparatedTopCommRingCat.{v} where
  obj p := p.obj
  map {_ _} h := Presentation.hom h.le
  map_id p := by
    rw [Presentation.hom_eq (r := 1) (hr := (mul_one _).symm)
      (hT := fun t ht ↦ by rwa [mul_one])]
    exact restrictionObjHom_self P p.num p.den _ p.hden
  map_comp {p q w} f g := by
    obtain ⟨r, hr, hT⟩ := f.le
    obtain ⟨r₂, hr₂, hT₂⟩ := g.le
    rw [Presentation.hom_eq f.le r hr hT, Presentation.hom_eq g.le r₂ hr₂ hT₂,
      Presentation.hom_eq (f ≫ g).le (r * r₂) (by rw [hr₂, hr, mul_assoc])
        (fun t ht ↦ by rw [← mul_assoc]; exact hT₂ _ (hT t ht))]
    exact (restrictionObjHom_comp_restrictionObjHom P p.num p.den _ p.hden q.num q.den _ q.hden
      r hr hT w.num w.den _ w.hden r₂ hr₂ hT₂).symm

end PairOfDefinition

end

end TauCeti.Huber
