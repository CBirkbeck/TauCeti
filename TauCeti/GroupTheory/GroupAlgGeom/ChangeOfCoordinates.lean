/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Changes of coordinates in equations over groups

An automorphism of the free group with coefficients `G[X]` that fixes `G` acts on tuples in
`H^X` by word evaluation. The action transports solution sets and radicals, and therefore
induces an isomorphism of their coordinate groups. It also applies to inconsistent systems,
whose coordinate maps need not embed the coefficients.

The construction is the invertible case of the word-map correspondence of Baumslag, Myasnikov
and Remeslennikov, *Algebraic geometry over groups I*, §3.5.
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod

variable {G H X : Type*} [Group G] [Group H] (ι : G →* H)

/-- An automorphism of `G[X]` fixes the coefficients when it is the identity on the left
free-product summand. -/
def FixesCoefficients (σ : GX G X ≃* GX G X) : Prop :=
  ∀ g : G, σ (inl g) = inl g

namespace FixesCoefficients

variable {σ : GX G X ≃* GX G X}

/-- The inverse of a coefficient-preserving automorphism also fixes the coefficients. -/
theorem symm (hσ : FixesCoefficients σ) : FixesCoefficients σ.symm := by
  intro g
  apply σ.injective
  simpa only [σ.apply_symm_apply] using (hσ g).symm

end FixesCoefficients

/-- Substitute the images of the variables under `σ` into a point of `H^X`. -/
def coordinateChange (σ : GX G X ≃* GX G X) (v : X → H) : X → H :=
  fun x => eval ι v (σ (inr (FreeGroup.of x)))

/-- Substitution at a point is precomposition of evaluation by the word automorphism. -/
theorem eval_coordinateChange (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ) (v : X → H) :
    eval ι (coordinateChange ι σ v) = (eval ι v).comp σ.toMonoidHom := by
  apply hom_ext
  · ext g
    simp only [eval_comp_inl, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hσ g,
      eval_inl]
  · apply FreeGroup.ext_hom
    intro x
    simp [coordinateChange]

/-- A coefficient-preserving word automorphism acts bijectively on tuples in `H^X`. -/
def coordinateChangeEquiv (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ) : (X → H) ≃ (X → H) where
  toFun := coordinateChange ι σ
  invFun := coordinateChange ι σ.symm
  left_inv v := by
    funext x
    simp [coordinateChange, eval_coordinateChange ι σ hσ v]
  right_inv v := by
    funext x
    simp [coordinateChange, eval_coordinateChange ι σ.symm hσ.symm v]

/-- A solution of `S` becomes a solution of the inverse image of `S` under a change of
coordinates, and every solution of the latter arises this way. -/
theorem coordinateChange_mem_V_iff (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ) (S : Set (GX G X)) (v : X → H) :
    coordinateChange ι σ v ∈ V ι (σ ⁻¹' S) ↔ v ∈ V ι S := by
  rw [mem_V, mem_V]
  constructor
  · intro hv s hs
    have h := hv (σ.symm s) (by simp [hs])
    simpa [eval_coordinateChange ι σ hσ v] using h
  · intro hv s hs
    rw [eval_coordinateChange ι σ hσ v]
    exact hv (σ s) hs

/-- The change of coordinates restricts to an equivalence of solution sets. -/
def coordinateChangeSolutions (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ) (S : Set (GX G X)) :
    V ι S ≃ V ι (σ ⁻¹' S) :=
  (coordinateChangeEquiv ι σ hσ).subtypeEquiv
    (fun v => (coordinateChange_mem_V_iff ι σ hσ S v).symm)

/-- Radicals transform by inverse image under a coefficient-preserving word automorphism. -/
theorem Rad_preimage (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ) (S : Set (GX G X)) :
    Rad ι (σ ⁻¹' S) = (Rad ι S).comap σ.toMonoidHom := by
  ext w
  simp only [Rad_def, mem_I, Subgroup.mem_comap]
  constructor
  · intro hw v hv
    have hp : coordinateChange ι σ v ∈ V ι (σ ⁻¹' S) :=
      (coordinateChange_mem_V_iff ι σ hσ S v).2 hv
    simpa [eval_coordinateChange ι σ hσ v] using hw _ hp
  · intro hw v hv
    let u := (coordinateChangeEquiv ι σ hσ).symm v
    have he : coordinateChange ι σ u = v := by
      simpa [u, coordinateChangeEquiv] using
        (coordinateChangeEquiv ι σ hσ).apply_symm_apply v
    have hu : u ∈ V ι S := by
      apply (coordinateChange_mem_V_iff ι σ hσ S u).1
      rw [he]
      exact hv
    have hev := DFunLike.congr_fun (eval_coordinateChange ι σ hσ u) w
    rw [he] at hev
    exact hev.trans (hw u hu)

/-- A change of coordinates induces an isomorphism from the coordinate group of the
transformed system to that of the original system. -/
def coordinateGroupEquiv (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ) (S : Set (GX G X)) :
    CoordGroup ι (σ ⁻¹' S) ≃* CoordGroup ι S :=
  QuotientGroup.congr _ _ σ (by
    ext w
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (Rad_preimage ι σ hσ S).le hu
    · intro hw
      refine ⟨σ.symm w, ?_, by simp⟩
      exact (Rad_preimage ι σ hσ S).ge (by simpa using hw))

@[simp]
theorem coordinateGroupEquiv_mk (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ) (S : Set (GX G X)) (w : GX G X) :
    coordinateGroupEquiv ι σ hσ S (w : CoordGroup ι (σ ⁻¹' S)) =
      (σ w : CoordGroup ι S) :=
  QuotientGroup.congr_mk ..

@[simp]
theorem coordinateGroupEquiv_coeff (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ) (S : Set (GX G X)) (g : G) :
    coordinateGroupEquiv ι σ hσ S (CoordGroup.coeff ι (σ ⁻¹' S) g) =
      CoordGroup.coeff ι S g := by
  rw [CoordGroup.coeff_apply, coordinateGroupEquiv_mk, hσ g, ← CoordGroup.coeff_apply]

end TauCeti.GroupAlgGeom
