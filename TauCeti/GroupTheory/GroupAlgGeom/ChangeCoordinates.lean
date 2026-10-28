/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet

/-!
# Changes of coordinates in algebraic geometry over groups

An automorphism of the free `G`-group `G[X]` fixing the coefficients acts on points by
substitution. The inverse automorphism acts on equations. These actions identify the solution
sets and their radicals, and hence induce an isomorphism of coordinate groups, even when a
system has no solutions.

This is the change-of-coordinates principle for equations over groups in Baumslag, Myasnikov
and Remeslennikov, *Algebraic geometry over groups I*, §3.5.
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod

variable {G H X : Type*} [Group G] [Group H] (ι : G →* H)

/-- Evaluation of a tuple of words obtained from a coefficient-preserving automorphism. -/
private theorem eval_wordMap_equiv (e : GX G X ≃* GX G X)
    (he : ∀ g : G, e (inl g) = inl g) (v : X → H) :
    eval ι (wordMap ι (fun x => e (inr (FreeGroup.of x))) v) =
      (eval ι v).comp e.toMonoidHom := by
  calc
    eval ι (wordMap ι (fun x => e (inr (FreeGroup.of x))) v) =
        eval ι (fun x => ((eval ι v).comp e.toMonoidHom) (inr (FreeGroup.of x))) := by
          congr 1
          funext x
          simp
    _ = (eval ι v).comp e.toMonoidHom :=
      eval_eq_of_comp_inl (by ext g; simp [he])

/-- The action on points of an automorphism of `G[X]` fixing the coefficients. A variable is
evaluated at the word to which the automorphism sends it. -/
def changeCoordinates (e : GX G X ≃* GX G X)
    (he : ∀ g : G, e (inl g) = inl g) : (X → H) ≃ (X → H) where
  toFun v := wordMap ι (fun x => e (inr (FreeGroup.of x))) v
  invFun v := wordMap ι (fun x => e.symm (inr (FreeGroup.of x))) v
  left_inv v := by
    funext x
    have he' : ∀ g : G, e.symm (inl g) = inl g := by
      intro g
      apply e.injective
      simp [he]
    dsimp only
    rw [wordMap_apply, eval_wordMap_equiv ι e he]
    simp
  right_inv v := by
    funext x
    have he' : ∀ g : G, e.symm (inl g) = inl g := by
      intro g
      apply e.injective
      simp [he]
    dsimp only
    rw [wordMap_apply, eval_wordMap_equiv ι e.symm he']
    simp

/-- Evaluation after changing coordinates is evaluation before the change, precomposed with
the word automorphism. -/
theorem eval_changeCoordinates (e : GX G X ≃* GX G X)
    (he : ∀ g : G, e (inl g) = inl g) (v : X → H) :
    eval ι (changeCoordinates ι e he v) = (eval ι v).comp e.toMonoidHom := by
  exact eval_wordMap_equiv ι e he v

/-- Changing coordinates sends solutions of `S` to solutions of the inverse image of `S`.
This equivalence also applies to inconsistent systems. -/
def changeCoordinatesSolutions (e : GX G X ≃* GX G X)
    (he : ∀ g : G, e (inl g) = inl g) (S : Set (GX G X)) :
    V ι S ≃ V ι (e.symm '' S) where
  toFun v := ⟨changeCoordinates ι e he v, by
    rw [mem_V]
    rintro _ ⟨w, hw, rfl⟩
    rw [eval_changeCoordinates]
    simpa using mem_V.1 v.2 w hw⟩
  invFun v := ⟨(changeCoordinates ι e he).symm v, by
    rw [mem_V]
    intro w hw
    have hv := mem_V.1 v.2 (e.symm w) ⟨w, hw, rfl⟩
    have hcomp := eval_changeCoordinates ι e he ((changeCoordinates ι e he).symm v)
    rw [Equiv.apply_symm_apply] at hcomp
    rw [hcomp] at hv
    simpa using hv⟩
  left_inv v := Subtype.ext ((changeCoordinates ι e he).symm_apply_apply v.1)
  right_inv v := Subtype.ext ((changeCoordinates ι e he).apply_symm_apply v.1)

@[simp]
theorem changeCoordinatesSolutions_apply_coe (e : GX G X ≃* GX G X)
    (he : ∀ g : G, e (inl g) = inl g) (S : Set (GX G X)) (v : V ι S) :
    ((changeCoordinatesSolutions ι e he S) v).1 = changeCoordinates ι e he v.1 := by
  simp [changeCoordinatesSolutions]

/-- The radical of a transformed system is the image of the original radical under the
inverse word automorphism. -/
theorem map_Rad_changeCoordinates (e : GX G X ≃* GX G X)
    (he : ∀ g : G, e (inl g) = inl g) (S : Set (GX G X)) :
    (Rad ι S).map e.symm.toMonoidHom = Rad ι (e.symm '' S) := by
  ext w
  simp only [Subgroup.mem_map_equiv, mem_Rad]
  constructor
  · intro hw v hv
    obtain ⟨u, hu⟩ := (changeCoordinatesSolutions ι e he S).surjective ⟨v, hv⟩
    have hval := congrArg Subtype.val hu
    have hu := hw u.1 u.2
    calc
      eval ι v w = eval ι (changeCoordinates ι e he u.1) w := by
        simpa only [changeCoordinatesSolutions_apply_coe] using
          congrArg (fun p : X → H => eval ι p w) hval.symm
      _ = eval ι u.1 (e w) := by rw [eval_changeCoordinates]; rfl
      _ = 1 := by simpa using hu
  · intro hw v hv
    have hh := hw ((changeCoordinatesSolutions ι e he S) ⟨v, hv⟩).1
      ((changeCoordinatesSolutions ι e he S) ⟨v, hv⟩).2
    rw [changeCoordinatesSolutions_apply_coe, eval_changeCoordinates] at hh
    simpa using hh

/-- A change of coordinates induces an isomorphism of coordinate groups. The isomorphism
sends the class of `w` to the class of `e⁻¹(w)`. -/
def coordGroupChangeCoordinates (e : GX G X ≃* GX G X)
    (he : ∀ g : G, e (inl g) = inl g) (S : Set (GX G X)) :
    CoordGroup ι S ≃* CoordGroup ι (e.symm '' S) :=
  QuotientGroup.congr (Rad ι S) (Rad ι (e.symm '' S)) e.symm
    (map_Rad_changeCoordinates ι e he S)

@[simp]
theorem coordGroupChangeCoordinates_mk (e : GX G X ≃* GX G X)
    (he : ∀ g : G, e (inl g) = inl g) (S : Set (GX G X)) (w : GX G X) :
    coordGroupChangeCoordinates ι e he S (w : CoordGroup ι S) =
      (e.symm w : CoordGroup ι (e.symm '' S)) :=
  QuotientGroup.congr_mk _ _ _ _ _

/-- The inverse word automorphism fixes coefficients in the transformed coordinate group. -/
@[simp]
theorem coordGroupChangeCoordinates_symm_inl (e : GX G X ≃* GX G X)
    (he : ∀ g : G, e (inl g) = inl g) (S : Set (GX G X)) (g : G) :
    (e.symm (inl g) : CoordGroup ι (e.symm '' S)) =
      CoordGroup.coeff ι (e.symm '' S) g := by
  rw [CoordGroup.coeff_apply]
  congr 1
  apply e.injective
  simp [he]

/-- The change-of-coordinates isomorphism fixes coefficients. -/
theorem coordGroupChangeCoordinates_coeff (e : GX G X ≃* GX G X)
    (he : ∀ g : G, e (inl g) = inl g) (S : Set (GX G X)) (g : G) :
    coordGroupChangeCoordinates ι e he S (CoordGroup.coeff ι S g) =
      CoordGroup.coeff ι (e.symm '' S) g := by
  simpa only [CoordGroup.coeff_apply, coordGroupChangeCoordinates_mk] using
    coordGroupChangeCoordinates_symm_inl ι e he S g

end TauCeti.GroupAlgGeom
