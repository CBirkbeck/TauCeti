/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet

/-!
# Changes of coordinates in equations over groups

A coefficient-preserving word homomorphism acts on tuples by evaluation. When it is bijective,
this action transports solution sets and radicals, and induces an isomorphism of coordinate
groups. The results apply to inconsistent systems and arbitrary coefficient homomorphisms.

The construction is the invertible case of the word-map correspondence of Baumslag, Myasnikov
and Remeslennikov, *Algebraic geometry over groups I*, §3.5.
-/

public section

namespace TauCeti
namespace GroupAlgGeom

open Monoid.Coprod

variable {G H X Y Z : Type*} [Group G] [Group H] (ι : G →* H)

/-- Substitute the images of the variables under a coefficient-preserving word homomorphism. -/
def wordMap (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X)) (v : X → H) : Y → H :=
  homEquiv ι ((evalGHom ι v).comp σ)

/-- A word map evaluates the image of each variable. -/
@[simp] theorem wordMap_apply (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X))
    (v : X → H) (y : Y) :
    wordMap ι σ v y = eval ι v (σ (inr (FreeGroup.of y))) := by
  simp [wordMap]

/-- Evaluation after a word map is composition with the word homomorphism. -/
theorem eval_wordMap (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X)) (v : X → H) :
    eval ι (wordMap ι σ v) = (eval ι v).comp σ.toMonoidHom := by
  apply MonoidHom.ext
  intro w
  have h := congrArg (fun f : GHom (inl : G →* GX G Y) ι => f w)
    ((homEquiv ι).symm_apply_apply ((evalGHom ι v).comp σ))
  simpa only [wordMap, homEquiv_symm_apply, coe_evalGHom, GHom.coe_comp,
    Function.comp_apply, MonoidHom.comp_apply,
    show σ.toMonoidHom w = σ w from rfl] using h

/-- The identity word homomorphism leaves tuples unchanged. -/
@[simp] theorem wordMap_id (v : X → H) :
    wordMap ι (GHom.id (inl : G →* GX G X)) v = v := by
  funext x
  simp

/-- Word maps compose in the opposite order to word homomorphisms. -/
theorem wordMap_comp (σ : GHom (inl : G →* GX G Z) (inl : G →* GX G Y))
    (τ : GHom (inl : G →* GX G Y) (inl : G →* GX G X)) (v : X → H) :
    wordMap ι (τ.comp σ) v = wordMap ι σ (wordMap ι τ v) := by
  funext z
  rw [wordMap_apply, wordMap_apply, eval_wordMap]
  simp only [GHom.coe_comp, Function.comp_apply, MonoidHom.comp_apply,
    show τ.toMonoidHom (σ (inr (FreeGroup.of z))) =
      τ (σ (inr (FreeGroup.of z))) from rfl]

/-- A word map sends solutions to solutions of the inverse-image system. -/
theorem wordMap_mem_V (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X))
    (S : Set (GX G X)) (v : X → H) (hv : v ∈ V ι S) :
    wordMap ι σ v ∈ V ι (σ ⁻¹' S) := by
  rw [mem_V] at hv ⊢
  intro s hs
  rw [eval_wordMap ι σ v]
  exact hv (σ s) hs

variable (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X))
    (hσ : Function.Bijective σ)

include σ hσ

/-- The inverse of a bijective coefficient-preserving word homomorphism also preserves
coefficients. -/
noncomputable def GHom.symmOfBijective : GHom (inl : G →* GX G X) (inl : G →* GX G Y) where
  toMonoidHom := (MulEquiv.ofBijective σ.toMonoidHom hσ).symm.toMonoidHom
  map_coeff' g := by
    apply hσ.1
    rw [σ.map_coeff g]
    have hc : σ ((MulEquiv.ofBijective σ.toMonoidHom hσ).symm.toMonoidHom
        (inl g)) = σ.toMonoidHom ((MulEquiv.ofBijective σ.toMonoidHom hσ).symm
        (inl g)) := rfl
    exact hc.trans (MulEquiv.ofBijective_apply_symm_apply σ.toMonoidHom hσ)

include ι

/-- A bijective coefficient-preserving word map gives an equivalence of tuples. -/
noncomputable def coordinateChangeEquiv : (X → H) ≃ (Y → H) where
  toFun := wordMap ι σ
  invFun := wordMap ι (σ.symmOfBijective hσ)
  left_inv v := by
    funext x
    rw [wordMap_apply, eval_wordMap]
    rw [MonoidHom.comp_apply]
    change eval ι v (σ ((MulEquiv.ofBijective σ.toMonoidHom hσ).symm
      (inr (FreeGroup.of x)))) = v x
    have he := MulEquiv.ofBijective_apply_symm_apply σ.toMonoidHom hσ
      (n := inr (FreeGroup.of x))
    have hc : σ ((MulEquiv.ofBijective σ.toMonoidHom hσ).symm
        (inr (FreeGroup.of x))) = inr (FreeGroup.of x) := he
    rw [hc]
    exact eval_inr_of ι v x
  right_inv v := by
    funext y
    rw [wordMap_apply, eval_wordMap, MonoidHom.comp_apply]
    change eval ι v ((MulEquiv.ofBijective σ.toMonoidHom hσ).symm
      (σ (inr (FreeGroup.of y)))) = v y
    have he : (MulEquiv.ofBijective σ.toMonoidHom hσ).symm
        (σ (inr (FreeGroup.of y))) = inr (FreeGroup.of y) := by
      simpa only [show σ (inr (FreeGroup.of y)) =
          (MulEquiv.ofBijective σ.toMonoidHom hσ) (inr (FreeGroup.of y)) from rfl]
        using (MulEquiv.ofBijective σ.toMonoidHom hσ).symm_apply_apply
          (inr (FreeGroup.of y))
    rw [he]
    exact eval_inr_of ι v y

/-- The tuple equivalence applies the word map. -/
@[simp] theorem coordinateChangeEquiv_apply (v : X → H) :
    coordinateChangeEquiv ι σ hσ v = wordMap ι σ v := by
  simp [coordinateChangeEquiv]

/-- The inverse tuple equivalence applies the inverse word map. -/
@[simp] theorem coordinateChangeEquiv_symm_apply (v : Y → H) :
    (coordinateChangeEquiv ι σ hσ).symm v = wordMap ι (σ.symmOfBijective hσ) v := by
  simp [coordinateChangeEquiv]

/-- A tuple solves `S` exactly when its word map solves the inverse-image system. -/
theorem wordMap_mem_V_iff (S : Set (GX G X)) (v : X → H) :
    wordMap ι σ v ∈ V ι (σ ⁻¹' S) ↔ v ∈ V ι S := by
  rw [mem_V, mem_V]
  constructor
  · intro hv s hs
    obtain ⟨t, rfl⟩ := hσ.2 s
    have h := hv t hs
    rw [eval_wordMap ι σ v] at h
    exact h
  · intro hv
    exact (mem_V).1 (wordMap_mem_V ι σ S v ((mem_V).2 hv))

/-- A bijective word map restricts to an equivalence of solution sets. -/
noncomputable def coordinateChangeSolutions (S : Set (GX G X)) :
    V ι S ≃ V ι (σ ⁻¹' S) :=
  (coordinateChangeEquiv ι σ hσ).subtypeEquiv
    (fun v => (wordMap_mem_V_iff ι σ hσ S v).symm)

/-- On tuples, the solution equivalence applies the word map. -/
@[simp] theorem coordinateChangeSolutions_apply_coe (S : Set (GX G X)) (v : V ι S) :
    ((coordinateChangeSolutions ι σ hσ S v : V ι (σ ⁻¹' S)) : Y → H) =
      wordMap ι σ v := by
  simp [coordinateChangeSolutions, Equiv.subtypeEquiv]

/-- On tuples, the inverse solution equivalence applies the inverse word map. -/
@[simp] theorem coordinateChangeSolutions_symm_apply_coe
    (S : Set (GX G X)) (v : V ι (σ ⁻¹' S)) :
    (((coordinateChangeSolutions ι σ hσ S).symm v : V ι S) : X → H) =
      wordMap ι (σ.symmOfBijective hσ) v := by
  simp [coordinateChangeSolutions, Equiv.subtypeEquiv]

/-- Radicals transform by inverse image under a bijective coefficient-preserving word map. -/
theorem Rad_preimage (S : Set (GX G X)) :
    Rad ι (σ ⁻¹' S) = (Rad ι S).comap σ.toMonoidHom := by
  ext w
  simp only [Rad_def, mem_I, Subgroup.mem_comap]
  constructor
  · intro hw v hv
    have hp : wordMap ι σ v ∈ V ι (σ ⁻¹' S) :=
      (wordMap_mem_V_iff ι σ hσ S v).2 hv
    have h := hw _ hp
    rw [eval_wordMap ι σ v] at h
    exact h
  · intro hw v hv
    obtain ⟨u, rfl⟩ := (coordinateChangeEquiv ι σ hσ).surjective v
    have hu : u ∈ V ι S := by
      apply (wordMap_mem_V_iff ι σ hσ S u).1
      simpa using hv
    have h := hw u hu
    rw [coordinateChangeEquiv_apply, eval_wordMap ι σ u]
    exact h

namespace CoordGroup

/-- A change of coordinates induces an isomorphism from the coordinate group of the
transformed system to that of the original system. -/
noncomputable def equivOfCoordinateChange (S : Set (GX G X)) :
    CoordGroup ι (σ ⁻¹' S) ≃* CoordGroup ι S :=
  QuotientGroup.congr _ _ (MulEquiv.ofBijective σ.toMonoidHom hσ) (by
    rw [Rad_preimage ι σ hσ S]
    exact Subgroup.map_comap_eq_self_of_surjective hσ.2 _)

@[simp]
theorem equivOfCoordinateChange_mk (S : Set (GX G X)) (w : GX G Y) :
    equivOfCoordinateChange ι σ hσ S (w : CoordGroup ι (σ ⁻¹' S)) =
      (σ w : CoordGroup ι S) :=
  QuotientGroup.congr_mk ..

/-- The inverse coordinate-group isomorphism applies the inverse word homomorphism. -/
@[simp]
theorem equivOfCoordinateChange_symm_mk (S : Set (GX G X)) (w : GX G X) :
    (equivOfCoordinateChange ι σ hσ S).symm (w : CoordGroup ι S) =
      ((σ.symmOfBijective hσ) w : CoordGroup ι (σ ⁻¹' S)) := by
  apply (equivOfCoordinateChange ι σ hσ S).injective
  rw [MulEquiv.apply_symm_apply]
  rw [equivOfCoordinateChange_mk]
  exact (congrArg (fun x : GX G X => (x : CoordGroup ι S))
    (MulEquiv.ofBijective_apply_symm_apply σ.toMonoidHom hσ (n := w))).symm

/-- The induced coordinate-group isomorphism commutes with the coefficient maps. -/
theorem equivOfCoordinateChange_comp_coeff (S : Set (GX G X)) :
    (equivOfCoordinateChange ι σ hσ S).toMonoidHom.comp (coeff ι (σ ⁻¹' S)) =
      coeff ι S := by
  ext g
  simp

/-- Precomposition with the coordinate-group isomorphism corresponds to the word map on
solutions under the point–homomorphism equivalence. -/
theorem homEquiv_comp_equivOfCoordinateChange (S : Set (GX G X))
    (φ : GHom (coeff ι S) ι) :
    homEquiv ι (σ ⁻¹' S)
      (φ.comp ⟨(equivOfCoordinateChange ι σ hσ S).toMonoidHom,
        fun g => by
          change equivOfCoordinateChange ι σ hσ S (coeff ι (σ ⁻¹' S) g) = _
          exact DFunLike.congr_fun (equivOfCoordinateChange_comp_coeff ι σ hσ S) g⟩) =
      coordinateChangeSolutions ι σ hσ S (homEquiv ι S φ) := by
  apply SetCoe.ext
  funext y
  simp only [homEquiv_apply_coe, GHom.coe_comp, Function.comp_apply,
    coordinateChangeSolutions_apply_coe, wordMap_apply]
  change φ (equivOfCoordinateChange ι σ hσ S
    ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι (σ ⁻¹' S))) = _
  rw [equivOfCoordinateChange_mk]
  have he := congrArg (fun f : GHom (coeff ι S) ι =>
      f (σ (inr (FreeGroup.of y)) : CoordGroup ι S))
    ((homEquiv ι S).symm_apply_apply φ)
  simpa only [homEquiv_symm_apply, evalGHom_mk] using he.symm

end CoordGroup

end GroupAlgGeom
end TauCeti
