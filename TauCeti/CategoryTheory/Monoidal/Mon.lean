/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Monoid and group objects

This file provides general-purpose facts about monoid and group objects.

## Main declarations

* `TauCeti.isCommMonObj_of_grp_iso`: commutativity of a group object is preserved by isomorphism.
* `TauCeti.isIso_hom_hom_left`: an isomorphism of group objects over `S` has an isomorphism as
  its underlying morphism in the ambient category.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

/-- Commutativity of a group object is preserved under isomorphism. -/
theorem isCommMonObj_of_grp_iso
    {C : Type u} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {G H : Grp C} (e : G ≅ H) (hG : IsCommMonObj G.X) : IsCommMonObj H.X := by
  let _ := hG
  constructor
  apply (cancel_mono e.inv.hom.hom).1
  simp only [Category.assoc, IsMonHom.mul_hom]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality]
  simp only [Category.assoc, IsCommMonObj.mul_comm]

/-- An isomorphism `f` of group objects over `S` has an isomorphism as its underlying morphism
in the ambient category: `f.hom.hom.left` strips the group-object, monoid-object and `Over`
layers in turn. -/
lemma isIso_hom_hom_left {C : Type u} [Category C] {S : C}
    [CartesianMonoidalCategory (Over S)] {G H : Grp (Over S)} (f : G ⟶ H) [IsIso f] :
    IsIso f.hom.hom.left :=
  (Grp.forget (Over S) ⋙ Over.forget S).map_isIso f

end TauCeti
