/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic
public import TauCeti.NumberTheory.HeckeRing.GLn.TransposeAntiInvolution

/-!
# The Atkin-Lehner anti-involution of the `Γ₀(N)` Hecke pair

Placeholder; rewritten once the construction is settled.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup HeckeRing.GLn

open scoped MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- The Atkin-Lehner matrix `w = diag(1, N)`. -/
noncomputable def atkinLehnerMatrix [NeZero N] : GL (Fin 2) ℚ :=
  natDiagGL 2 ![1, N]

/-- `ι(g) = w · gᵀ · w⁻¹`, as a homomorphism to the opposite group. -/
noncomputable def atkinLehnerHom [NeZero N] : GL (Fin 2) ℚ →* (GL (Fin 2) ℚ)ᵐᵒᵖ where
  toFun g := MulOpposite.op (atkinLehnerMatrix N *
    (transposeGLEquiv 2 g).unop * (atkinLehnerMatrix N)⁻¹)
  map_one' := by simp
  map_mul' a b := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, MulOpposite.unop_mul]
    have h1 : (transposeGLEquiv 2 (a * b)).unop =
        (transposeGLEquiv 2 b).unop * (transposeGLEquiv 2 a).unop := by
      rw [map_mul]; rfl
    rw [h1]; group

/-- Transposition fixes `w`, because `w` is diagonal. -/
private lemma transposeGLEquiv_atkinLehnerMatrix [NeZero N] :
    (transposeGLEquiv 2 (atkinLehnerMatrix N)).unop = atkinLehnerMatrix N := by
  rw [atkinLehnerMatrix]
  exact transposeGLEquiv_natDiagGL 2 ![1, N]

private lemma atkinLehner_involutive [NeZero N] (g : GL (Fin 2) ℚ) :
    (atkinLehnerHom N (atkinLehnerHom N g).unop).unop = g := by
  simp only [atkinLehnerHom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
  have h_tr : (transposeGLEquiv 2 (atkinLehnerMatrix N *
      (transposeGLEquiv 2 g).unop * (atkinLehnerMatrix N)⁻¹)).unop =
      (transposeGLEquiv 2 (atkinLehnerMatrix N)⁻¹).unop *
        (transposeGLEquiv 2 (transposeGLEquiv 2 g).unop).unop *
        (transposeGLEquiv 2 (atkinLehnerMatrix N)).unop := by
    rw [map_mul, map_mul]
    simp only [MulOpposite.unop_mul]
    group
  have h_inv : (transposeGLEquiv 2 (atkinLehnerMatrix N)⁻¹).unop = (atkinLehnerMatrix N)⁻¹ := by
    rw [map_inv, MulOpposite.unop_inv, transposeGLEquiv_atkinLehnerMatrix]
  rw [h_tr, transposeGLEquiv_transposeGLEquiv, transposeGLEquiv_atkinLehnerMatrix, h_inv]
  group

/-- The integral matrix of `ι(g)`. Conjugating the transpose by `w = diag(1, N)` divides the
upper-right entry by `N` and multiplies the lower-left by `N`; the first is integral exactly
because `N ∣ A 1 0`, which is the `Δ₀(N)` shape. The two diagonal entries are untouched — in
particular the upper-left one, which is why every coprimality hypothesis about it survives.

This is the one computation both membership proofs below need, so it is done once here. -/
private lemma atkinLehner_unop_val [NeZero N] (g : GL (Fin 2) ℚ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (c : ℤ) (hc : A 1 0 = (N : ℤ) * c) :
    (((atkinLehnerHom N g).unop : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (Matrix.of ![![A 0 0, c], ![(N : ℤ) * A 0 1, A 1 1]]).map (Int.cast : ℤ → ℚ) := by
  sorry

/-- The rational matrix of an integral special-linear element is its entrywise cast. -/
private lemma mapGL_val_eq_map_intCast (τ : SpecialLinearGroup (Fin 2) ℤ) :
    ((mapGL ℚ τ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (τ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) := by
  simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]

/-- `ι` preserves the image of `Γ₀(N)`: the transported matrix again has determinant one and
lower-left entry divisible by `N`. -/
private lemma atkinLehner_mem_Gamma0 [NeZero N] (g : GL (Fin 2) ℚ)
    (hg : g ∈ (Gamma0 N).map (mapGL ℚ)) :
    (atkinLehnerHom N g).unop ∈ (Gamma0 N).map (mapGL ℚ) := by
  rw [Subgroup.mem_map] at hg ⊢
  obtain ⟨σ, hσ_mem, rfl⟩ := hg
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ_mem
  obtain ⟨c, hc⟩ := hσ_mem
  set A := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hA_def
  set B : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![A 0 0, c], ![(N : ℤ) * A 0 1, A 1 1]] with hB
  have hB_det : B.det = 1 := by
    have hdetA : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
    rw [σ.2] at hdetA
    simp only [hB, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [show c * ((N : ℤ) * A 0 1) = A 0 1 * A 1 0 by rw [hc]; ring]
  refine ⟨⟨B, hB_det⟩, Gamma0_mem.mpr ?_, Units.ext ?_⟩
  · simp only [hB, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_mul_right _ _
  · rw [atkinLehner_unop_val N _ A (mapGL_val_eq_map_intCast σ) c hc,
      mapGL_val_eq_map_intCast ⟨B, hB_det⟩]

/-- `ι` preserves `Δ₀(N)`: the determinant and the upper-left entry are unchanged, and the new
lower-left entry `N · A 0 1` is visibly divisible by `N`. -/
private lemma atkinLehner_mem_Delta0 [NeZero N] (g : GL (Fin 2) ℚ) (hg : g ∈ Delta0 N) :
    (atkinLehnerHom N g).unop ∈ Delta0 N := by
  obtain ⟨A, hA, hdet, hAN, hAunit⟩ := (mem_Delta0_iff N).mp hg
  obtain ⟨c, hc⟩ := hAN
  set B : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![A 0 0, c], ![(N : ℤ) * A 0 1, A 1 1]] with hB
  have hval := atkinLehner_unop_val N g A hA c hc
  have hB_det : B.det = A.det := by
    have hdetA : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
    simp only [hB, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [show c * ((N : ℤ) * A 0 1) = A 0 1 * A 1 0 by rw [hc]; ring]
  refine (mem_Delta0_iff N).mpr ⟨B, hval, ?_, ⟨A 0 1, by simp [hB]⟩, ?_⟩
  · rw [hval, ← Int.cast_det, hB_det, Int.cast_det, ← hA]
    exact hdet
  · simpa [hB] using hAunit

/-- **The Atkin-Lehner anti-involution** of the `Γ₀(N)` Hecke pair. -/
noncomputable def atkinLehnerAntiInvolution [NeZero N] :
    HeckeAntiInvolution (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) :=
  HeckeAntiInvolution.ofAmbient (atkinLehnerHom N) (atkinLehner_involutive N)
    (atkinLehner_mem_Gamma0 N) (atkinLehner_mem_Delta0 N)

end HeckeRing.GL2
