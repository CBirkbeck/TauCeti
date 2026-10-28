/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
import TauCeti.GroupTheory.QuotientGroup.Map

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

/-- Evaluation after a word map is composition with the word homomorphism. -/
theorem eval_wordMap (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X)) (v : X → H) :
    eval ι (wordMap ι (fun y => σ (inr (FreeGroup.of y))) v) =
      (eval ι v).comp σ.toMonoidHom := by
  rw [← eval_comp_eval]
  congr 1
  exact eval_eq_of_comp_inl σ.comp_coeff

/-- The identity word homomorphism leaves tuples unchanged. -/
@[simp] theorem wordMap_id (v : X → H) :
    wordMap ι (fun x => inr (FreeGroup.of x)) v = v := by
  funext x
  simp

/-- Word maps compose in the opposite order to word homomorphisms. -/
theorem wordMap_comp (σ : GHom (inl : G →* GX G Z) (inl : G →* GX G Y))
    (τ : GHom (inl : G →* GX G Y) (inl : G →* GX G X)) (v : X → H) :
    wordMap ι (fun z => (τ.comp σ) (inr (FreeGroup.of z))) v =
      wordMap ι (fun y => σ (inr (FreeGroup.of y)))
        (wordMap ι (fun x => τ (inr (FreeGroup.of x))) v) := by
  rw [wordMap_wordMap]
  congr 1
  funext z
  simp only [GHom.coe_comp, Function.comp_apply]
  exact (DFunLike.congr_fun (eval_eq_of_comp_inl τ.comp_coeff)
    (σ (inr (FreeGroup.of z)))).symm

/-- A word map sends solutions to solutions of the inverse-image system. -/
theorem wordMap_mem_V (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X))
    (S : Set (GX G X)) (v : X → H) (hv : v ∈ V ι S) :
    wordMap ι (fun y => σ (inr (FreeGroup.of y))) v ∈ V ι (σ ⁻¹' S) := by
  have h := (Set.ext_iff.mp
    (preimage_wordMap_V (ι := ι) (fun y => σ (inr (FreeGroup.of y))) (σ ⁻¹' S))) v
  have heval : eval (inl : G →* GX G X) (fun y => σ (inr (FreeGroup.of y))) =
      σ.toMonoidHom := eval_eq_of_comp_inl σ.comp_coeff
  rw [heval] at h
  exact h.mpr (V_antitone ι (Set.image_preimage_subset σ S) hv)

/-- A tuple solves `S` exactly when its word map solves the inverse-image system. -/
theorem wordMap_mem_V_iff (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X))
    (hσ : Function.Surjective σ) (S : Set (GX G X)) (v : X → H) :
    wordMap ι (fun y => σ (inr (FreeGroup.of y))) v ∈ V ι (σ ⁻¹' S) ↔ v ∈ V ι S := by
  have h := (Set.ext_iff.mp
    (preimage_wordMap_V (ι := ι) (fun y => σ (inr (FreeGroup.of y))) (σ ⁻¹' S))) v
  have heval : eval (inl : G →* GX G X) (fun y => σ (inr (FreeGroup.of y))) =
      σ.toMonoidHom := eval_eq_of_comp_inl σ.comp_coeff
  rw [heval] at h
  change _ ↔ v ∈ V ι (σ '' (σ ⁻¹' S)) at h
  rw [Set.image_preimage_eq S hσ] at h
  exact h

/-- A word map sends the radical of the inverse-image system into the radical of the
original system. -/
theorem Rad_preimage_le_comap
    (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X)) (S : Set (GX G X)) :
    Rad ι (σ ⁻¹' S) ≤ (Rad ι S).comap σ.toMonoidHom := by
  intro w hw
  rw [Subgroup.mem_comap, mem_Rad]
  intro v hv
  have h := (mem_Rad).1 hw
    (wordMap ι (fun y => σ (inr (FreeGroup.of y))) v) (wordMap_mem_V ι σ S v hv)
  rwa [eval_wordMap] at h

namespace CoordGroup

/-- A coefficient-preserving word map induces a homomorphism between coordinate groups. -/
def homOfWordMap (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X))
    (S : Set (GX G X)) : GHom (coeff ι (σ ⁻¹' S)) (coeff ι S) where
  toMonoidHom := QuotientGroup.map _ _ σ.toMonoidHom (Rad_preimage_le_comap ι σ S)
  map_coeff' g := by
    simp [coeff_apply]

@[simp]
theorem homOfWordMap_mk
    (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X))
    (S : Set (GX G X)) (w : GX G Y) :
    homOfWordMap ι σ S (w : CoordGroup ι (σ ⁻¹' S)) =
      (σ w : CoordGroup ι S) := by
  simp [homOfWordMap]

end CoordGroup

variable (σ : GHom (inl : G →* GX G Y) (inl : G →* GX G X))
    (hσ : Function.Bijective σ)

include σ hσ

include ι

/-- A bijective coefficient-preserving word map gives an equivalence of tuples. -/
noncomputable def coordinateChangeEquiv : (X → H) ≃ (Y → H) where
  toFun := wordMap ι (fun y => σ (inr (FreeGroup.of y)))
  invFun := wordMap ι (fun x => (σ.symmOfBijective hσ) (inr (FreeGroup.of x)))
  left_inv v := by
    rw [← wordMap_comp, GHom.comp_symmOfBijective]
    simpa only [GHom.coe_id, id_eq] using wordMap_id (ι := ι) v
  right_inv v := by
    rw [← wordMap_comp, GHom.symmOfBijective_comp]
    simpa only [GHom.coe_id, id_eq] using wordMap_id (ι := ι) v

/-- The tuple equivalence applies the word map. -/
@[simp] theorem coordinateChangeEquiv_apply (v : X → H) :
    coordinateChangeEquiv ι σ hσ v =
      wordMap ι (fun y => σ (inr (FreeGroup.of y))) v := by
  simp [coordinateChangeEquiv]

/-- The inverse tuple equivalence applies the inverse word map. -/
@[simp] theorem coordinateChangeEquiv_symm_apply (v : Y → H) :
    (coordinateChangeEquiv ι σ hσ).symm v =
      wordMap ι (fun x => (σ.symmOfBijective hσ) (inr (FreeGroup.of x))) v := by
  simp [coordinateChangeEquiv]

/-- A bijective word map restricts to an equivalence of solution sets. -/
noncomputable def coordinateChangeSolutions (S : Set (GX G X)) :
    V ι S ≃ V ι (σ ⁻¹' S) :=
  (coordinateChangeEquiv ι σ hσ).subtypeEquiv
    (fun v => (wordMap_mem_V_iff ι σ hσ.2 S v).symm)

/-- On tuples, the solution equivalence applies the word map. -/
@[simp] theorem coordinateChangeSolutions_apply_coe (S : Set (GX G X)) (v : V ι S) :
    ((coordinateChangeSolutions ι σ hσ S v : V ι (σ ⁻¹' S)) : Y → H) =
      wordMap ι (fun y => σ (inr (FreeGroup.of y))) v := by
  simp [coordinateChangeSolutions, Equiv.subtypeEquiv]

/-- On tuples, the inverse solution equivalence applies the inverse word map. -/
@[simp] theorem coordinateChangeSolutions_symm_apply_coe
    (S : Set (GX G X)) (v : V ι (σ ⁻¹' S)) :
    (((coordinateChangeSolutions ι σ hσ S).symm v : V ι S) : X → H) =
      wordMap ι (fun x => (σ.symmOfBijective hσ) (inr (FreeGroup.of x))) v := by
  simp [coordinateChangeSolutions, Equiv.subtypeEquiv]

/-- Radicals transform by inverse image under a bijective coefficient-preserving word map. -/
theorem Rad_preimage (S : Set (GX G X)) :
    Rad ι (σ ⁻¹' S) = (Rad ι S).comap σ.toMonoidHom := by
  refine le_antisymm (Rad_preimage_le_comap ι σ S) ?_
  intro w hw
  rw [mem_Rad]
  intro v hv
  obtain ⟨u, rfl⟩ := (coordinateChangeEquiv ι σ hσ).surjective v
  have hu : u ∈ V ι S := by
    apply (wordMap_mem_V_iff ι σ hσ.2 S u).1
    simpa using hv
  have h := (mem_Rad).1 hw u hu
  rw [coordinateChangeEquiv_apply, eval_wordMap]
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
      (σ w : CoordGroup ι S) := by
  simp [equivOfCoordinateChange]

/-- The inverse coordinate-group isomorphism applies the inverse word homomorphism. -/
@[simp]
theorem equivOfCoordinateChange_symm_mk (S : Set (GX G X)) (w : GX G X) :
    (equivOfCoordinateChange ι σ hσ S).symm (w : CoordGroup ι S) =
      ((σ.symmOfBijective hσ) w : CoordGroup ι (σ ⁻¹' S)) := by
  apply (equivOfCoordinateChange ι σ hσ S).injective
  simp

/-- Precomposition with the coordinate-group isomorphism corresponds to the word map on
solutions under the point–homomorphism equivalence. -/
theorem homEquiv_comp_equivOfCoordinateChange (S : Set (GX G X))
    (φ : GHom (coeff ι S) ι) :
    homEquiv ι (σ ⁻¹' S)
      (φ.comp (homOfWordMap ι σ S)) =
      coordinateChangeSolutions ι σ hσ S (homEquiv ι S φ) := by
  apply SetCoe.ext
  funext y
  simp only [homEquiv_apply_coe, GHom.coe_comp, Function.comp_apply,
    coordinateChangeSolutions_apply_coe, wordMap_apply]
  rw [homOfWordMap_mk]
  simp

end CoordGroup

end GroupAlgGeom
end TauCeti
