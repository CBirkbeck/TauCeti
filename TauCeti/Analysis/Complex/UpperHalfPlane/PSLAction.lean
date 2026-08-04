/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# The `PSL(2)` actions on the upper half-plane

The projective special linear groups `PSL(2, ℤ)` and `PSL(2, ℝ)` (quotients of `SL(2, ·)`
by their centers `{±I}`) act faithfully on the upper half-plane `ℍ`. The `PSL(2, ℝ)`-action
is the restriction of Mathlib's `PGL(2, ℝ)`-action along
`Matrix.ProjectiveSpecialLinearGroup.toPGL`, and the `PSL(2, ℤ)`-action is its further
restriction along the injective descent `psl2zToPSL2R` from
`TauCeti/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean`. Both actions are
measurable and preserve the invariant measure `volume : Measure ℍ` (inherited from
Mathlib's `GL(2, ℝ)`-invariance).

## Main results

* `UpperHalfPlane.center_SL2Z_smul_eq` — the center of `SL(2, ℤ)` acts trivially.
* `UpperHalfPlane.instMulActionPSL2Z`, `instMulActionPSL2R` — the restricted actions, with
  the representative compatibilities `PSL_smul_coe`, `PSL_R_smul_coe`.
* `SMulInvariantMeasure` instances for `SL(2, ℤ)`, `PSL(2, ℤ)` and `PSL(2, ℝ)` on
  `(ℍ, volume)`.
* `UpperHalfPlane.GL_smul_eq_of_coe_eq_smul` — matrices differing by a nonzero scalar act
  identically on `ℍ`.
* `UpperHalfPlane.glPosToPSL2R_smul` — the det-normalized projective representative of a
  `GL(2, ℝ)⁺` element (multiplicative by `Real.sqrt_mul` together with the centrality of
  positive scalars) acts on `ℍ` exactly as the original element.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/PSL2Action.lean`); the AINTLIB Jacobian computation of
`SL(2, ℤ)`-invariance of the hyperbolic measure is **not** ported — Mathlib's
`SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume` subsumes it, and all invariance instances
here descend from it.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.4
* [Shi] Shimura, *Arithmetic Theory of Automorphic Functions*, §1.5
* The AINTLIB `LeanModularForms` project,
  <https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>
  (`Modularforms/PSL2Action.lean`)
-/

public section

noncomputable section

open scoped MatrixGroups Pointwise

open ModularGroup UpperHalfPlane Matrix.SpecialLinearGroup MeasureTheory

namespace UpperHalfPlane

/-- The center of `SL(2, ℤ)` consists of `{I, -I}`. Every center element
acts trivially on `ℍ` because it is a scalar matrix `ζI` with `ζ = ±1`,
and `(ζτ + 0)/(0τ + ζ) = τ`. -/
theorem center_SL2Z_smul_eq (c : SL(2, ℤ)) (hc : c ∈ Subgroup.center SL(2, ℤ)) (τ : ℍ) :
    c • τ = τ := by
  rw [mem_center_iff] at hc
  obtain ⟨ζ, hζ, hζ_eq⟩ := hc
  simp only [Fintype.card_fin] at hζ
  have hζ_cases : ζ = 1 ∨ ζ = -1 := by
    rcases mul_eq_zero.mp (by nlinarith [hζ] : (ζ - 1) * (ζ + 1) = 0) with h | h <;> lia
  rcases hζ_cases with rfl | rfl
  · have hc_one : c = 1 := by
      ext i j
      simpa [Matrix.scalar] using (congr_fun (congr_fun hζ_eq i) j).symm
    rw [hc_one, one_smul]
  · have hc_neg : c = -1 := by
      ext i j
      simpa [Matrix.scalar, coe_neg] using (congr_fun (congr_fun hζ_eq i) j).symm
    rw [hc_neg]
    simp

instance : Countable SL(2, ℤ) :=
  Function.Injective.countable
    (f := fun (g : SL(2, ℤ)) (i j : Fin 2) ↦ g i j) fun _ _ h ↦
      Subtype.coe_injective (Matrix.ext fun i j ↦ congr_fun (congr_fun h i) j)

instance : Countable PSL(2, ℤ) := Quotient.countable

instance : MeasurableConstSMul SL(2, ℤ) ℍ where
  measurable_const_smul g := by
    -- the `SL(2, ℤ)`-action on `ℍ` is definitionally the `GL(2, ℝ)`-action of `mapGL ℝ g`;
    -- no rewriting lemma crosses this definitional boundary
    change Measurable (fun τ ↦ (mapGL ℝ g) • τ)
    exact (continuous_const_smul (mapGL ℝ g)).measurable

/-- `SL(2, ℤ)` preserves the invariant measure on `ℍ`; the action factors through
`GL(2, ℝ)`, whose invariance is Mathlib's. -/
instance : SMulInvariantMeasure SL(2, ℤ) ℍ volume where
  measure_preimage_smul g s hs := by
    -- as above, expose the definitional `mapGL ℝ` factorization of the action
    change volume ((fun τ ↦ (mapGL ℝ g) • τ) ⁻¹' s) = volume s
    exact (measurePreserving_smul (mapGL ℝ g) volume).measure_preimage hs.nullMeasurableSet

/-- The `PSL(2, ℝ)`-action on `ℍ`, through the injection into `PGL(2, ℝ)` and Mathlib's
`MulAction PGL(2, ℝ) ℍ`. -/
noncomputable instance instMulActionPSL2R : MulAction PSL(2, ℝ) ℍ :=
  MulAction.compHom ℍ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ℝ))

/-- Compatibility: the `PSL(2, ℝ)` action of a representative coincides with
the underlying `SL(2, ℝ)` action. -/
@[simp]
theorem PSL_R_smul_coe (g : SL(2, ℝ)) (τ : ℍ) :
    (↑g : PSL(2, ℝ)) • τ = g • τ := by
  -- the `compHom` action is definitionally the `PGL(2, ℝ)`-action of the `toPGL`-image
  change Matrix.ProjectiveSpecialLinearGroup.toPGL (↑g : PSL(2, ℝ)) • τ = g • τ
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, pglMk_smul]
  rfl

/-- The `PSL(2, ℤ)`-action on `ℍ`: the restriction of the `PSL(2, ℝ)`-action along the
injective descent `psl2zToPSL2R`. -/
noncomputable instance instMulActionPSL2Z : MulAction PSL(2, ℤ) ℍ :=
  MulAction.compHom ℍ psl2zToPSL2R

/-- Action compatibility for `psl2zToPSL2R`: the image of `p : PSL(2, ℤ)` acts on `ℍ`
exactly as `p` does — definitionally, since the `PSL(2, ℤ)`-action is the restriction
along `psl2zToPSL2R`. -/
@[simp]
theorem psl2zToPSL2R_smul_eq (p : PSL(2, ℤ)) (τ : ℍ) :
    psl2zToPSL2R p • τ = p • τ :=
  (rfl)

/-- The `PSL(2, ℤ)` action is compatible with the `SL(2, ℤ)` action:
`(↑g) • τ = g • τ` for `g : SL(2, ℤ)`. -/
@[simp]
theorem PSL_smul_coe (g : SL(2, ℤ)) (τ : ℍ) :
    (↑g : PSL(2, ℤ)) • τ = g • τ := by
  -- expose the restriction along `psl2zToPSL2R`, then descend to representatives
  change psl2zToPSL2R (↑g : PSL(2, ℤ)) • τ = g • τ
  rw [psl2zToPSL2R_mk, sl2zToPSL2R_apply, PSL_R_smul_coe]
  -- the `SL(2, ℤ)`-action and the cast `SL(2, ℝ)`-action are definitionally the
  -- `GL(2, ℝ)`-action of the common `mapGL ℝ` image
  rfl

/-- Action compatibility for `psl2zToPSL2R` (representative form). -/
theorem psl2zToPSL2R_smul (g : SL(2, ℤ)) (τ : ℍ) :
    psl2zToPSL2R (↑g : PSL(2, ℤ)) • τ = g • τ := by
  rw [psl2zToPSL2R_smul_eq, PSL_smul_coe]

instance : MeasurableConstSMul PSL(2, ℤ) ℍ where
  measurable_const_smul g := by
    induction g using Quotient.inductionOn with | h a => ?_
    -- reduce to the representative, then to the definitional `mapGL ℝ` factorization
    change Measurable (fun τ ↦ (↑a : PSL(2, ℤ)) • τ)
    simp only [PSL_smul_coe]
    change Measurable (fun τ ↦ (mapGL ℝ a) • τ)
    exact (continuous_const_smul (mapGL ℝ a)).measurable

/-- `PSL(2, ℤ)` preserves the invariant measure on `ℍ`. -/
instance : SMulInvariantMeasure PSL(2, ℤ) ℍ volume where
  measure_preimage_smul g s hs := by
    induction g using Quotient.inductionOn with | h a => ?_
    -- reduce to the representative `SL(2, ℤ)`-action, whose invariance descends from
    -- Mathlib's `GL(2, ℝ)`-invariance
    change volume ((fun τ ↦ (↑a : PSL(2, ℤ)) • τ) ⁻¹' s) = volume s
    simpa only [PSL_smul_coe] using
      (measurePreserving_smul a (volume : Measure ℍ)).measure_preimage hs.nullMeasurableSet

instance : MeasurableConstSMul PSL(2, ℝ) ℍ where
  measurable_const_smul g := by
    obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective
      (Matrix.ProjectiveSpecialLinearGroup.toPGL g)
    have h_act : ∀ τ : ℍ, g • τ = G • τ := fun τ ↦ by
      -- the `compHom` action is definitionally the `PGL(2, ℝ)`-action of the image
      change Matrix.ProjectiveSpecialLinearGroup.toPGL g • τ = G • τ
      rw [← hG, pglMk_smul]
    simp only [h_act]
    exact (continuous_const_smul G).measurable

/-- `PSL(2, ℝ)` preserves the invariant measure on `ℍ`. -/
instance : SMulInvariantMeasure PSL(2, ℝ) ℍ volume where
  measure_preimage_smul g s hs := by
    obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective
      (Matrix.ProjectiveSpecialLinearGroup.toPGL g)
    have h_act : ∀ τ : ℍ, g • τ = G • τ := fun τ ↦ by
      -- as above, expose the definitional `PGL(2, ℝ)`-factorization
      change Matrix.ProjectiveSpecialLinearGroup.toPGL g • τ = G • τ
      rw [← hG, pglMk_smul]
    simp only [h_act]
    exact (measurePreserving_smul G (volume : Measure ℍ)).measure_preimage
      hs.nullMeasurableSet

/-- Nonzero-scalar action invariance for `GL (Fin 2) ℝ`: matrices differing by a
nonzero scalar define the same class in `PGL(2, ℝ)`, hence act identically on `ℍ`. -/
lemma GL_smul_eq_of_coe_eq_smul {g h : GL (Fin 2) ℝ} {c : ℝ} (hc : c ≠ 0)
    (h_eq : ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      c • ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    (τ : ℍ) :
    h • τ = g • τ := by
  have h_mk : Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk h := by
    rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 c hc, Units.ext ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    have h_scalar : (Matrix.scalar (Fin 2)) ((Units.mk0 c hc : ℝˣ) : ℝ) =
        c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      simp [Matrix.scalar, Matrix.smul_one_eq_diagonal]
    rw [h_scalar]
    rw [mul_smul_comm, mul_one]
    exact h_eq.symm
  calc h • τ = Matrix.ProjGenLinGroup.mk h • τ := (pglMk_smul h τ).symm
    _ = Matrix.ProjGenLinGroup.mk g • τ := by rw [← h_mk]
    _ = g • τ := pglMk_smul g τ

/-- Action equivariance: the projective representative `glPosToPSL2R g` acts on
`ℍ` exactly as `g` does, even though `det g` need not be `1`. Not `@[simp]`:
`glPosToPSL2R_apply` rewrites the left-hand side out of simp normal form first
(simp-NF lint). -/
theorem glPosToPSL2R_smul (g : GL(2, ℝ)⁺) (τ : ℍ) :
    glPosToPSL2R g • τ = g • τ := by
  have hg_pos : 0 < ((g : GL (Fin 2) ℝ).det.val : ℝ) := g.property
  have h_sqrt_ne : (Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_ne_zero'.mpr hg_pos)
  rw [glPosToPSL2R_apply, PSL_R_smul_coe]
  -- the `SL(2, ℝ)`-action is definitionally the `GL(2, ℝ)`-action of the `mapGL ℝ` image
  change (mapGL ℝ (glPosToSL2R g) : GL (Fin 2) ℝ) • τ = (g : GL (Fin 2) ℝ) • τ
  refine GL_smul_eq_of_coe_eq_smul h_sqrt_ne ?_ τ
  -- read off the matrix of the normalized representative through `mapGL`
  change ((mapGL ℝ (glPosToSL2R g) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    (Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
      ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  -- `algebraMap ℝ ℝ` is the identity, so the `map` leaves the matrix unchanged
  have hmap : (((Matrix.SpecialLinearGroup.map (algebraMap ℝ ℝ)) (glPosToSL2R g) :
      SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((glPosToSL2R g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    simp [Algebra.algebraMap_self]
  rw [hmap]
  exact glPosToSL2R_coe_matrix g

end UpperHalfPlane
