/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet

/-!
# Word maps and coordinate-group homomorphisms

A tuple of coefficient words that maps one algebraic set into another induces a
coefficient-preserving homomorphism in the opposite direction between their coordinate groups.
Conversely, every such homomorphism is represented by a tuple of words. Two tuples represent the
same homomorphism precisely when their word maps agree at every point of the source algebraic
set. This describes polynomial maps without choosing presentations of coordinate functions.

The correspondence follows Baumslag, Myasnikov and Remeslennikov, *Algebraic geometry over
groups I*, Section 3.5, Theorem 4 and Corollary 9.
-/

public section

namespace TauCeti.GroupAlgGeom
namespace CoordGroup

open Monoid.Coprod

variable {G H X Y : Type*} [Group G] [Group H]
variable (ι : G →* H) (S : Set (GX G X)) (T : Set (GX G Y))

/-- A map from a coordinate group is determined by the images of its variables, even when
its codomain is not the original solution group. -/
@[ext]
theorem gHom_ext' {K : Type*} [Group K] {κ : G →* K}
    {φ ψ : GHom (coeff ι T) κ}
    (h : ∀ y, φ ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T) =
      ψ ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T)) : φ = ψ := by
  apply GHom.ext
  intro q
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
  have hφc : (φ.toMonoidHom.comp (QuotientGroup.mk' (Rad ι T))).comp inl = κ := by
    ext g
    simpa [coeff_apply] using φ.map_coeff g
  have hψc : (ψ.toMonoidHom.comp (QuotientGroup.mk' (Rad ι T))).comp inl = κ := by
    ext g
    simpa [coeff_apply] using ψ.map_coeff g
  have hφ := eval_eq_of_comp_inl hφc
  have hψ := eval_eq_of_comp_inl hψc
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    GHom.toMonoidHom_eq_coe] at hφ hψ
  have hv : (fun y => (φ : CoordGroup ι T →* K)
      ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T)) =
      (fun y => (ψ : CoordGroup ι T →* K)
      ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T)) := funext h
  rw [hv] at hφ
  exact DFunLike.congr_fun (hφ.symm.trans hψ) t

/-- A tuple of words maps the solution set of `S` into the solution set of `T`. -/
def MapsToWordMap (w : Y → GX G X) : Prop :=
  Set.MapsTo (wordMap ι w) (V ι S) (V ι T)

/-- A word map between algebraic sets pulls equations vanishing on the target back to
equations vanishing on the source. -/
theorem Rad_le_comap_of_mapsToWordMap (w : Y → GX G X) (hw : MapsToWordMap ι S T w) :
    Rad ι T ≤ (Rad ι S).comap (eval (inl : G →* GX G X) w) := by
  intro t ht
  rw [Subgroup.mem_comap, mem_Rad]
  intro v hv
  rw [← MonoidHom.comp_apply, eval_comp_eval]
  exact (mem_Rad.mp ht) _ (hw hv)

/-- A word map between algebraic sets induces a coefficient-preserving homomorphism of
coordinate groups in the opposite direction. -/
def homOfMapsToWordMap (w : Y → GX G X) (hw : MapsToWordMap ι S T w) :
    GHom (coeff ι T) (coeff ι S) where
  toMonoidHom := QuotientGroup.map _ _ (eval (inl : G →* GX G X) w)
    (Rad_le_comap_of_mapsToWordMap ι S T w hw)
  map_coeff' g := by simp [coeff_apply]

@[simp]
theorem homOfMapsToWordMap_mk (w : Y → GX G X) (hw : MapsToWordMap ι S T w)
    (t : GX G Y) :
    homOfMapsToWordMap ι S T w hw (t : CoordGroup ι T) =
      (eval (inl : G →* GX G X) w t : CoordGroup ι S) := by
  simp [homOfMapsToWordMap]

/-- Evaluating the induced coordinate-group homomorphism at a point is the original word
map of that point. -/
theorem homEquiv_comp_homOfMapsToWordMap (w : Y → GX G X)
    (hw : MapsToWordMap ι S T w) (v : V ι S) :
    (homEquiv ι T ((evalGHom v.1 v.2).comp
      (homOfMapsToWordMap ι S T w hw)) : Y → H) = wordMap ι w v.1 := by
  funext y
  simp only [homEquiv_apply_coe, GHom.coe_comp, Function.comp_apply,
    homOfMapsToWordMap_mk, evalGHom_mk, wordMap_apply, eval_inr_of]

/-- Every coefficient-preserving coordinate-group homomorphism is represented by a tuple of
coefficient words, whose word map carries source solutions to target solutions. -/
theorem exists_wordMap_representation (φ : GHom (coeff ι T) (coeff ι S)) :
    ∃ w : Y → GX G X, ∃ hw : MapsToWordMap ι S T w,
      homOfMapsToWordMap ι S T w hw = φ := by
  classical
  have hsurj : ∀ y : Y, ∃ w : GX G X,
      (w : CoordGroup ι S) = φ ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T) := by
    intro y
    exact QuotientGroup.mk_surjective _
  choose w hw using hsurj
  have hmap : MapsToWordMap ι S T w := by
    intro v hv
    let ψ : GHom (coeff ι T) ι := (evalGHom v hv).comp φ
    have hcoords : wordMap ι w v = (homEquiv ι T ψ : Y → H) := by
      funext y
      simp only [wordMap_apply, homEquiv_apply_coe]
      rw [← evalGHom_mk (ι := ι) (S := S) hv (w y), hw y]
      exact (congrFun (GHom.coe_comp (evalGHom v hv) φ)
        ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T)).symm
    rw [hcoords]
    exact (homEquiv ι T ψ).property
  refine ⟨w, hmap, ?_⟩
  apply gHom_ext' ι T
  intro y
  rw [homOfMapsToWordMap_mk, eval_inr_of, hw y]

/-- Two representing tuples induce the same coordinate-group homomorphism exactly when they
give the same function on the source algebraic set. -/
theorem homOfMapsToWordMap_eq_iff (w w' : Y → GX G X)
    (hw : MapsToWordMap ι S T w) (hw' : MapsToWordMap ι S T w') :
    homOfMapsToWordMap ι S T w hw = homOfMapsToWordMap ι S T w' hw' ↔
      ∀ v ∈ V ι S, wordMap ι w v = wordMap ι w' v := by
  constructor
  · intro h v hv
    have h' := congrArg (fun f : GHom (coeff ι T) (coeff ι S) =>
      (homEquiv ι T ((evalGHom v hv).comp f) : Y → H)) h
    exact (homEquiv_comp_homOfMapsToWordMap ι S T w hw ⟨v, hv⟩).symm.trans
      (h'.trans (homEquiv_comp_homOfMapsToWordMap ι S T w' hw' ⟨v, hv⟩))
  · intro h
    apply gHom_ext' ι T
    intro y
    simp only [homOfMapsToWordMap_mk, eval_inr_of]
    apply QuotientGroup.eq.mpr
    rw [mem_Rad]
    intro v hv
    have := congrFun (h v hv) y
    simpa only [wordMap_apply, map_mul, map_inv, inv_mul_eq_one] using this

end CoordGroup
end TauCeti.GroupAlgGeom
