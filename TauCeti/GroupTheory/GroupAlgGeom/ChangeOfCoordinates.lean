/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet

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

variable {G H X Y : Type*} [Group G] [Group H] (ι : G →* H)

/-- A word homomorphism fixes the coefficients when it is the identity on the left
free-product summand. -/
def FixesCoefficients (σ : GX G Y →* GX G X) : Prop :=
  ∀ g : G, σ (inl g) = inl g

namespace FixesCoefficients

variable {σ : GX G X ≃* GX G X}

/-- A coefficient-preserving word homomorphism fixes each coefficient. -/
theorem apply_inl {σ : GX G Y →* GX G X} (hσ : FixesCoefficients σ)
    (g : G) : σ (inl g) = inl g := hσ g

/-- A word homomorphism fixing every coefficient satisfies `FixesCoefficients`. -/
theorem of_apply_inl {σ : GX G Y →* GX G X}
    (hσ : ∀ g : G, σ (inl g) = inl g) : FixesCoefficients σ := hσ

/-- The identity word automorphism fixes the coefficients. -/
theorem refl : FixesCoefficients (MulEquiv.refl (GX G X)).toMonoidHom := by
  intro g
  rfl

/-- A composite of coefficient-preserving automorphisms fixes the coefficients. -/
theorem trans {τ : GX G X ≃* GX G X} (hσ : FixesCoefficients σ.toMonoidHom)
    (hτ : FixesCoefficients τ.toMonoidHom) :
    FixesCoefficients (σ.trans τ).toMonoidHom := by
  intro g
  change τ (σ (inl g)) = inl g
  have hs := hσ g
  have ht := hτ g
  change σ (inl g) = inl g at hs
  change τ (inl g) = inl g at ht
  rw [hs, ht]

/-- The inverse of a coefficient-preserving automorphism also fixes the coefficients. -/
theorem symm (hσ : FixesCoefficients σ.toMonoidHom) :
    FixesCoefficients σ.symm.toMonoidHom := by
  intro g
  change σ.symm (inl g) = inl g
  apply σ.injective
  have hs := hσ g
  change σ (inl g) = inl g at hs
  simpa only [σ.apply_symm_apply] using hs.symm

end FixesCoefficients

/-- Substitute the images of the variables under `σ` into a point of `H^X`. -/
def coordinateChange (σ : GX G Y →* GX G X) (v : X → H) : Y → H :=
  fun x => eval ι v (σ (inr (FreeGroup.of x)))

/-- The coordinate change evaluates the image of each variable. -/
@[simp] theorem coordinateChange_apply (σ : GX G Y →* GX G X) (v : X → H) (y : Y) :
    coordinateChange ι σ v y = eval ι v (σ (inr (FreeGroup.of y))) := by
  simp [coordinateChange]

/-- Substitution at a point is precomposition of evaluation by the word homomorphism. -/
theorem eval_coordinateChange (σ : GX G Y →* GX G X)
    (hσ : FixesCoefficients σ) (v : X → H) :
    eval ι (coordinateChange ι σ v) = (eval ι v).comp σ := by
  rw [show coordinateChange ι σ v =
      (fun y => ((eval ι v).comp σ) (inr (FreeGroup.of y))) from
    funext (fun y => coordinateChange_apply ι σ v y)]
  exact eval_eq_of_comp_inl (f := (eval ι v).comp σ) (by
    apply MonoidHom.ext
    intro g
    simp [hσ g])

/-- The identity word automorphism leaves tuples unchanged. -/
theorem coordinateChange_refl (v : X → H) :
    coordinateChange ι (MulEquiv.refl (GX G X)).toMonoidHom v = v := by
  funext x
  simp [coordinateChange]

/-- Coordinate changes compose in the opposite order to word automorphisms. -/
theorem coordinateChange_trans (σ τ : GX G X ≃* GX G X)
    (hτ : FixesCoefficients τ.toMonoidHom) (v : X → H) :
    coordinateChange ι (σ.trans τ).toMonoidHom v =
      coordinateChange ι σ.toMonoidHom (coordinateChange ι τ.toMonoidHom v) := by
  funext x
  rw [coordinateChange_apply, coordinateChange_apply,
    eval_coordinateChange ι τ.toMonoidHom hτ v]
  rfl

/-- A word map sends solutions to solutions of the inverse-image system. -/
theorem coordinateChange_mem_V (σ : GX G Y →* GX G X)
    (hσ : FixesCoefficients σ) (S : Set (GX G X)) (v : X → H)
    (hv : v ∈ V ι S) : coordinateChange ι σ v ∈ V ι (σ ⁻¹' S) := by
  rw [mem_V] at hv ⊢
  intro s hs
  rw [eval_coordinateChange ι σ hσ v]
  exact hv (σ s) hs

/-- A coefficient-preserving word automorphism acts bijectively on tuples in `H^X`. -/
def coordinateChangeEquiv (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ.toMonoidHom) : (X → H) ≃ (X → H) where
  toFun := coordinateChange ι σ.toMonoidHom
  invFun := coordinateChange ι σ.symm.toMonoidHom
  left_inv v := by
    funext x
    rw [coordinateChange_apply, eval_coordinateChange ι σ.toMonoidHom hσ]
    simp
  right_inv v := by
    funext x
    rw [coordinateChange_apply, eval_coordinateChange ι σ.symm.toMonoidHom hσ.symm]
    simp

/-- The tuple equivalence applies the coordinate substitution. -/
@[simp] theorem coordinateChangeEquiv_apply (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ.toMonoidHom) (v : X → H) :
    coordinateChangeEquiv ι σ hσ v = coordinateChange ι σ.toMonoidHom v := by
  simp [coordinateChangeEquiv]

/-- The inverse tuple equivalence substitutes through the inverse automorphism. -/
@[simp] theorem coordinateChangeEquiv_symm_apply (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ.toMonoidHom) (v : X → H) :
    (coordinateChangeEquiv ι σ hσ).symm v = coordinateChange ι σ.symm.toMonoidHom v := by
  simp [coordinateChangeEquiv]

/-- A tuple solves `S` exactly when its coordinate change solves the inverse-image system.
The equivalence of solution sets is `coordinateChangeSolutions`. -/
theorem coordinateChange_mem_V_iff (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ.toMonoidHom) (S : Set (GX G X)) (v : X → H) :
    coordinateChange ι σ.toMonoidHom v ∈ V ι (σ ⁻¹' S) ↔ v ∈ V ι S := by
  rw [mem_V, mem_V]
  constructor
  · intro hv s hs
    have h := hv (σ.symm s) (by simp [hs])
    rw [eval_coordinateChange ι σ.toMonoidHom hσ v] at h
    simpa using h
  · intro hv
    exact (mem_V).1 (coordinateChange_mem_V ι σ.toMonoidHom hσ S v ((mem_V).2 hv))

/-- The change of coordinates restricts to an equivalence of solution sets. -/
def coordinateChangeSolutions (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ.toMonoidHom) (S : Set (GX G X)) :
    V ι S ≃ V ι (σ ⁻¹' S) :=
  (coordinateChangeEquiv ι σ hσ).subtypeEquiv
    (fun v => (coordinateChange_mem_V_iff ι σ hσ S v).symm)

/-- On tuples, the solution equivalence applies the coordinate substitution. -/
@[simp] theorem coordinateChangeSolutions_apply_coe (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ.toMonoidHom) (S : Set (GX G X)) (v : V ι S) :
    ((coordinateChangeSolutions ι σ hσ S v : V ι (σ ⁻¹' S)) : X → H) =
      coordinateChange ι σ.toMonoidHom v := by
  simp [coordinateChangeSolutions, Equiv.subtypeEquiv]

/-- On tuples, the inverse solution equivalence substitutes through the inverse automorphism. -/
@[simp] theorem coordinateChangeSolutions_symm_apply_coe (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ.toMonoidHom) (S : Set (GX G X)) (v : V ι (σ ⁻¹' S)) :
    (((coordinateChangeSolutions ι σ hσ S).symm v : V ι S) : X → H) =
      coordinateChange ι σ.symm.toMonoidHom v := by
  simp [coordinateChangeSolutions, Equiv.subtypeEquiv]

/-- Radicals transform by inverse image under a coefficient-preserving word automorphism. -/
theorem Rad_preimage (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ.toMonoidHom) (S : Set (GX G X)) :
    Rad ι (σ ⁻¹' S) = (Rad ι S).comap σ.toMonoidHom := by
  ext w
  simp only [Rad_def, mem_I, Subgroup.mem_comap]
  constructor
  · intro hw v hv
    have hp : coordinateChange ι σ.toMonoidHom v ∈ V ι (σ ⁻¹' S) :=
      (coordinateChange_mem_V_iff ι σ hσ S v).2 hv
    have h := hw _ hp
    rw [eval_coordinateChange ι σ.toMonoidHom hσ v] at h
    exact h
  · intro hw v hv
    obtain ⟨u, rfl⟩ := (coordinateChangeEquiv ι σ hσ).surjective v
    have hu : u ∈ V ι S := by
      apply (coordinateChange_mem_V_iff ι σ hσ S u).1
      simpa using hv
    have h := hw u hu
    rw [coordinateChangeEquiv_apply,
      eval_coordinateChange ι σ.toMonoidHom hσ u]
    exact h

/-- A change of coordinates induces an isomorphism from the coordinate group of the
transformed system to that of the original system. -/
def coordinateGroupEquiv (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ.toMonoidHom) (S : Set (GX G X)) :
    CoordGroup ι (σ ⁻¹' S) ≃* CoordGroup ι S :=
  QuotientGroup.congr _ _ σ (by
    rw [Rad_preimage ι σ hσ S]
    exact Subgroup.map_comap_eq_self_of_surjective σ.surjective _)

@[simp]
theorem coordinateGroupEquiv_mk (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ.toMonoidHom) (S : Set (GX G X)) (w : GX G X) :
    coordinateGroupEquiv ι σ hσ S (w : CoordGroup ι (σ ⁻¹' S)) =
      (σ w : CoordGroup ι S) :=
  QuotientGroup.congr_mk ..

/-- The inverse coordinate-group isomorphism applies the inverse word automorphism. -/
@[simp]
theorem coordinateGroupEquiv_symm_mk (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ.toMonoidHom) (S : Set (GX G X)) (w : GX G X) :
    (coordinateGroupEquiv ι σ hσ S).symm (w : CoordGroup ι S) =
      (σ.symm w : CoordGroup ι (σ ⁻¹' S)) := by
  apply (coordinateGroupEquiv ι σ hσ S).injective
  simp

/-- The induced coordinate-group isomorphism commutes with the coefficient homomorphisms. -/
theorem coordinateGroupEquiv_comp_coeff (σ : GX G X ≃* GX G X)
    (hσ : FixesCoefficients σ.toMonoidHom) (S : Set (GX G X)) :
    (coordinateGroupEquiv ι σ hσ S).toMonoidHom.comp (CoordGroup.coeff ι (σ ⁻¹' S)) =
      CoordGroup.coeff ι S := by
  ext g
  simpa [coordinateGroupEquiv_mk] using congrArg
    (fun w : GX G X => (w : CoordGroup ι S)) (hσ g)

end TauCeti.GroupAlgGeom
