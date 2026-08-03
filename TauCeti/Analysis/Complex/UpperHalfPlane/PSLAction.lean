/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# The `PSL(2)` actions on the upper half-plane

The projective special linear groups `PSL(2, ℤ)` and `PSL(2, ℝ)` (quotients of `SL(2, ·)`
by their centers `{±I}`) act faithfully on the upper half-plane `ℍ`: the center acts
trivially through the Möbius formula, so the `SL(2, ·)`-actions descend to the quotients.
Both actions are measurable and preserve the invariant measure `volume : Measure ℍ`
(inherited from Mathlib's `GL(2, ℝ)`-invariance).

This file also provides the maps connecting the groups:

* `UpperHalfPlane.sl2zToPSL2R : SL(2, ℤ) →* PSL(2, ℝ)` (cast entries, then project),
  with kernel the center of `SL(2, ℤ)`;
* `UpperHalfPlane.psl2zToPSL2R : PSL(2, ℤ) →* PSL(2, ℝ)`, the injective descent;
* `UpperHalfPlane.glPosToPSL2R : GL(2, ℝ)⁺ →* PSL(2, ℝ)`, the det-normalized
  projective representative — a monoid homomorphism, since positive scalars are central —
  acting on `ℍ` exactly as the original element.

## Main results

* `UpperHalfPlane.center_SL2Z_smul_eq` — the center of `SL(2, ℤ)` acts trivially.
* `UpperHalfPlane.instMulActionPSL2Z`, `instMulActionPSL2R` — the descended actions.
* `SMulInvariantMeasure` instances for `SL(2, ℤ)`, `PSL(2, ℤ)` and `PSL(2, ℝ)` on
  `(ℍ, volume)`.
* `UpperHalfPlane.psl2zToPSL2R_injective` and the action compatibilities
  `psl2zToPSL2R_smul_eq`, `glPosToPSL2R_smul`.

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

/-- The underlying function of the `PSL(2, ℤ)`-action on `ℍ`: act by any representative. -/
def pslSmul : PSL(2, ℤ) → ℍ → ℍ :=
  Quotient.lift (fun (a : SL(2, ℤ)) (τ : ℍ) ↦ a • τ) (by
    intro a b hab
    funext τ
    rw [show b = a * (a⁻¹ * b) by group, mul_smul,
      center_SL2Z_smul_eq _ (QuotientGroup.leftRel_apply.mp hab)])

@[simp] theorem pslSmul_coe (a : SL(2, ℤ)) (τ : ℍ) :
    pslSmul (↑a) τ = a • τ := (rfl)

/-- The action of `PSL(2, ℤ) = SL(2, ℤ)/{±I}` on `ℍ`, descending from the
`SL(2, ℤ)` action since the center acts trivially. -/
instance instMulActionPSL2Z : MulAction PSL(2, ℤ) ℍ where
  smul g τ := pslSmul g τ
  one_smul τ := by
    change pslSmul (↑(1 : SL(2, ℤ))) τ = τ
    rw [pslSmul_coe, one_smul]
  mul_smul g₁ g₂ τ := by
    induction g₁ using Quotient.inductionOn with | h a => ?_
    induction g₂ using Quotient.inductionOn with | h b => ?_
    change pslSmul ((↑a : PSL(2, ℤ)) * ↑b) τ = pslSmul ↑a (pslSmul ↑b τ)
    rw [← QuotientGroup.mk_mul, pslSmul_coe, pslSmul_coe, pslSmul_coe, mul_smul]

/-- The `PSL(2, ℤ)` action is compatible with the `SL(2, ℤ)` action:
`(↑g) • τ = g • τ` for `g : SL(2, ℤ)`. -/
@[simp]
theorem PSL_smul_coe (g : SL(2, ℤ)) (τ : ℍ) :
    (↑g : PSL(2, ℤ)) • τ = g • τ := (rfl)

instance : Countable SL(2, ℤ) :=
  Function.Injective.countable
    (f := fun (g : SL(2, ℤ)) (i j : Fin 2) ↦ g i j) fun _ _ h ↦
      Subtype.coe_injective (Matrix.ext fun i j ↦ congr_fun (congr_fun h i) j)

instance : Countable PSL(2, ℤ) := Quotient.countable

instance : MeasurableConstSMul SL(2, ℤ) ℍ where
  measurable_const_smul g := by
    change Measurable (fun τ ↦ (mapGL ℝ g) • τ)
    exact (continuous_const_smul (mapGL ℝ g)).measurable

instance : MeasurableConstSMul PSL(2, ℤ) ℍ where
  measurable_const_smul g := by
    induction g using Quotient.inductionOn with | h a => ?_
    change Measurable (fun τ ↦ (↑a : PSL(2, ℤ)) • τ)
    simp only [PSL_smul_coe]
    change Measurable (fun τ ↦ (mapGL ℝ a) • τ)
    exact (continuous_const_smul (mapGL ℝ a)).measurable

/-- `SL(2, ℤ)` preserves the invariant measure on `ℍ`; the action factors through
`GL(2, ℝ)`, whose invariance is Mathlib's. -/
instance : SMulInvariantMeasure SL(2, ℤ) ℍ volume where
  measure_preimage_smul g s hs := by
    change volume ((fun τ ↦ (mapGL ℝ g) • τ) ⁻¹' s) = volume s
    exact (measurePreserving_smul (mapGL ℝ g) volume).measure_preimage hs.nullMeasurableSet

/-- `PSL(2, ℤ)` preserves the invariant measure on `ℍ`. -/
instance : SMulInvariantMeasure PSL(2, ℤ) ℍ volume where
  measure_preimage_smul g s hs := by
    induction g using Quotient.inductionOn with | h a => ?_
    change volume ((fun τ ↦ (↑a : PSL(2, ℤ)) • τ) ⁻¹' s) = volume s
    simpa only [PSL_smul_coe] using
      (measurePreserving_smul a (volume : Measure ℍ)).measure_preimage hs.nullMeasurableSet

/-- The `PSL(2, ℝ)`-action on `ℍ`, through the injection into `PGL(2, ℝ)` and Mathlib's
`MulAction PGL(2, ℝ) ℍ`. -/
noncomputable instance instMulActionPSL2R : MulAction PSL(2, ℝ) ℍ :=
  MulAction.compHom ℍ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ℝ))

/-- Compatibility: the `PSL(2, ℝ)` action of a representative coincides with
the underlying `SL(2, ℝ)` action. Mirror of `PSL_smul_coe` for `PSL(2, ℤ)`. -/
@[simp]
theorem PSL_R_smul_coe (g : SL(2, ℝ)) (τ : ℍ) :
    (↑g : PSL(2, ℝ)) • τ = g • τ := by
  change Matrix.ProjectiveSpecialLinearGroup.toPGL (↑g : PSL(2, ℝ)) • τ = g • τ
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, pglMk_smul]
  rfl

instance : MeasurableConstSMul PSL(2, ℝ) ℍ where
  measurable_const_smul g := by
    obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective
      (Matrix.ProjectiveSpecialLinearGroup.toPGL g)
    have h_act : ∀ τ : ℍ, g • τ = G • τ := fun τ ↦ by
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
      change Matrix.ProjectiveSpecialLinearGroup.toPGL g • τ = G • τ
      rw [← hG, pglMk_smul]
    simp only [h_act]
    exact (measurePreserving_smul G (volume : Measure ℍ)).measure_preimage
      hs.nullMeasurableSet

/-- The lift `SL(2, ℤ) →* PSL(2, ℝ)`: cast `SL(2, ℤ)` entries to `ℝ` via
`SpecialLinearGroup.map (Int.castRingHom ℝ)`, then project to the `±I`-quotient. -/
def sl2zToPSL2R : SL(2, ℤ) →* PSL(2, ℝ) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))

@[simp] theorem sl2zToPSL2R_apply (g : SL(2, ℤ)) :
    sl2zToPSL2R g =
      (↑(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) : PSL(2, ℝ)) := (rfl)

private lemma map_intCast_entry (g : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ) i j =
    (((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℝ) := rfl

private lemma g_mem_center_of_map_intCast_mem_center (g : SL(2, ℤ))
    (hmem : (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g : SL(2, ℝ)) ∈
      Subgroup.center SL(2, ℝ)) : g ∈ Subgroup.center SL(2, ℤ) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hmem ⊢
  obtain ⟨r, hr_pow, hr_scalar⟩ := hmem
  have h_entry_R : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) =
      (Matrix.scalar (Fin 2) r) i j := fun i j ↦ by
    have h_ij := congr_fun (congr_fun hr_scalar i) j
    rw [map_intCast_entry] at h_ij
    exact h_ij.symm
  set z : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  have hr_z : (z : ℝ) = r := by
    have h00 := h_entry_R 0 0
    rwa [show (Matrix.scalar (Fin 2) r) 0 0 = r by simp [Matrix.scalar_apply]] at h00
  have h_diag : ∀ i, (g : Matrix (Fin 2) (Fin 2) ℤ) i i = z := fun i ↦ by
    have h_iR : (((g : Matrix _ _ ℤ) i i : ℤ) : ℝ) = (z : ℝ) := by
      have hii := h_entry_R i i
      rw [show (Matrix.scalar (Fin 2) r) i i = r by simp [Matrix.scalar_apply]] at hii
      rw [hii, ← hr_z]
    exact_mod_cast h_iR
  have h_off : ∀ i j, i ≠ j → (g : Matrix (Fin 2) (Fin 2) ℤ) i j = 0 := fun i j hij ↦ by
    have h_R : (((g : Matrix _ _ ℤ) i j : ℤ) : ℝ) = 0 := by
      have hij' := h_entry_R i j
      rwa [show (Matrix.scalar (Fin 2) r) i j = 0 by
        simp [Matrix.scalar_apply, hij]] at hij'
    exact_mod_cast h_R
  have hz_sq : z ^ 2 = 1 := by
    have hz_sq_R : (z : ℝ) ^ 2 = 1 := by
      rw [hr_z]
      simpa [Fintype.card_fin] using hr_pow
    exact_mod_cast hz_sq_R
  refine ⟨z, by simpa [Fintype.card_fin] using hz_sq, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, h_diag]
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, h_off i j hij]

private lemma map_intCast_mem_center_of_g_mem_center (g : SL(2, ℤ))
    (hmem : g ∈ Subgroup.center SL(2, ℤ)) :
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g : SL(2, ℝ)) ∈
      Subgroup.center SL(2, ℝ) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hmem ⊢
  obtain ⟨z, hz_pow, hz_scalar⟩ := hmem
  refine ⟨(z : ℝ), by exact_mod_cast hz_pow, ?_⟩
  ext i j
  have h_ij := congr_fun (congr_fun hz_scalar i) j
  rw [map_intCast_entry]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h_ij ⊢
    exact_mod_cast h_ij
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] at h_ij ⊢
    exact_mod_cast h_ij

/-- The kernel of `sl2zToPSL2R` is the center of `SL(2, ℤ)`: an integer matrix
casts to a real scalar matrix iff it is itself a scalar matrix. -/
theorem sl2zToPSL2R_ker : sl2zToPSL2R.ker = Subgroup.center SL(2, ℤ) := by
  ext g
  simp only [MonoidHom.mem_ker, sl2zToPSL2R_apply, QuotientGroup.eq_one_iff]
  exact ⟨g_mem_center_of_map_intCast_mem_center g, map_intCast_mem_center_of_g_mem_center g⟩

/-- The descended hom `PSL(2, ℤ) →* PSL(2, ℝ)`. `sl2zToPSL2R` factors through
`PSL(2, ℤ) = SL(2, ℤ) ⧸ center SL(2, ℤ)` since integer scalar matrices map into
`center SL(2, ℝ)`. -/
def psl2zToPSL2R : PSL(2, ℤ) →* PSL(2, ℝ) :=
  QuotientGroup.lift (Subgroup.center SL(2, ℤ)) sl2zToPSL2R fun x hx ↦ by
    rwa [sl2zToPSL2R_ker]

@[simp] theorem psl2zToPSL2R_mk (g : SL(2, ℤ)) :
    psl2zToPSL2R (↑g : PSL(2, ℤ)) = sl2zToPSL2R g :=
  QuotientGroup.lift_mk' _ _ g

/-- Action compatibility for `psl2zToPSL2R` (representative form): the descended
hom sends `[g] : PSL(2, ℤ)` to a `PSL(2, ℝ)`-element acting on `ℍ` exactly as the
underlying `SL(2, ℤ)`-action does. Not `@[simp]`: the left-hand side is not in simp
normal form (`psl2zToPSL2R_mk` fires first); `psl2zToPSL2R_smul_eq` is the simp form. -/
theorem psl2zToPSL2R_smul (g : SL(2, ℤ)) (τ : ℍ) :
    psl2zToPSL2R (↑g : PSL(2, ℤ)) • τ = g • τ :=
  (rfl)

/-- Action compatibility for `psl2zToPSL2R` (generic form): for any
`p : PSL(2, ℤ)`, the descended hom's image acts on `ℍ` exactly as `p` does. -/
@[simp]
theorem psl2zToPSL2R_smul_eq (p : PSL(2, ℤ)) (τ : ℍ) :
    psl2zToPSL2R p • τ = p • τ := by
  induction p using Quotient.inductionOn with | h g => ?_
  exact (psl2zToPSL2R_smul g τ).trans (PSL_smul_coe g τ).symm

/-- `psl2zToPSL2R` is injective: its kernel is the image of
`sl2zToPSL2R.ker = center SL(2, ℤ)` under the `PSL(2, ℤ)`-projection, which is `⊥`. -/
theorem psl2zToPSL2R_injective : Function.Injective psl2zToPSL2R := by
  rw [← MonoidHom.ker_eq_bot_iff]
  change (QuotientGroup.lift (Subgroup.center SL(2, ℤ)) sl2zToPSL2R _).ker = ⊥
  rw [QuotientGroup.ker_lift, sl2zToPSL2R_ker, QuotientGroup.map_mk'_self]

/-- Positive-scalar action invariance for `GL (Fin 2) ℝ`: matrices differing by a
nonzero scalar define the same class in `PGL(2, ℝ)`, hence act identically on `ℍ`. -/
lemma GL_smul_pos_eq {g h : GL (Fin 2) ℝ} {c : ℝ} (hc : c ≠ 0)
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

/-- The det-normalized `SL(2, ℝ)` representative of a `GL(2, ℝ)⁺` element, as a monoid
homomorphism: the matrix `(√ det g)⁻¹ • g` has determinant `1`, and normalization is
multiplicative because positive scalars are central and `√` is multiplicative on them. -/
def glPosToSL2R : GL(2, ℝ)⁺ →* SL(2, ℝ) where
  toFun g :=
    ⟨(Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
        ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), by
      have hg_pos : 0 < ((g : GL (Fin 2) ℝ).det.val : ℝ) := g.property
      change ((Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
          ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).det = 1
      rw [Matrix.det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt hg_pos.le]
      exact inv_mul_cancel₀ (ne_of_gt hg_pos)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    have hg_pos : 0 < ((g : GL (Fin 2) ℝ).det.val : ℝ) := g.property
    have hh_pos : 0 < ((h : GL (Fin 2) ℝ).det.val : ℝ) := h.property
    have h_det : ((g * h : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val =
        (g : GL (Fin 2) ℝ).det.val * (h : GL (Fin 2) ℝ).det.val := by
      simp [Units.val_mul]
    have h_mat : (((g * h : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
          ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := rfl
    change (Real.sqrt (((g * h : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val))⁻¹ •
        (((g * h : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [h_det, h_mat, Real.sqrt_mul hg_pos.le, mul_inv]
    rw [show ((Real.sqrt (g : GL (Fin 2) ℝ).det.val)⁻¹ *
        (Real.sqrt (h : GL (Fin 2) ℝ).det.val)⁻¹) •
        (((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
          ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
        ((Real.sqrt (g : GL (Fin 2) ℝ).det.val)⁻¹ •
          ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) *
        ((Real.sqrt (h : GL (Fin 2) ℝ).det.val)⁻¹ •
          ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) from
      (smul_mul_smul_comm _ _ _ _).symm]
    rfl

/-- The projective representative of a `GL(2, ℝ)⁺` element: the composition of
`glPosToSL2R` with the projection to `PSL(2, ℝ)`, a monoid homomorphism. -/
def glPosToPSL2R : GL(2, ℝ)⁺ →* PSL(2, ℝ) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp glPosToSL2R

/-- Action equivariance: the projective representative `glPosToPSL2R g` acts on
`ℍ` exactly as `g` does, even though `det g` need not be `1`. -/
theorem glPosToPSL2R_smul (g : GL(2, ℝ)⁺) (τ : ℍ) :
    glPosToPSL2R g • τ = g • τ := by
  have hg_pos : 0 < ((g : GL (Fin 2) ℝ).det.val : ℝ) := g.property
  have h_sqrt_ne : (Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_ne_zero'.mpr hg_pos)
  change ((glPosToSL2R g : SL(2, ℝ)) : PSL(2, ℝ)) • τ = g • τ
  rw [PSL_R_smul_coe]
  change (mapGL ℝ (glPosToSL2R g) : GL (Fin 2) ℝ) • τ = (g : GL (Fin 2) ℝ) • τ
  refine GL_smul_pos_eq h_sqrt_ne ?_ τ
  change ((mapGL ℝ (glPosToSL2R g) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    (Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
      ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  rfl

end UpperHalfPlane
