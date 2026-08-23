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

private lemma atkinLehner_mem_Gamma0 [NeZero N] (g : GL (Fin 2) ℚ)
    (hg : g ∈ (Gamma0 N).map (mapGL ℚ)) :
    (atkinLehnerHom N g).unop ∈ (Gamma0 N).map (mapGL ℚ) := by
  sorry

private lemma atkinLehner_mem_Delta0 [NeZero N] (g : GL (Fin 2) ℚ) (hg : g ∈ Delta0 N) :
    (atkinLehnerHom N g).unop ∈ Delta0 N := by
  sorry

/-- **The Atkin-Lehner anti-involution** of the `Γ₀(N)` Hecke pair. -/
noncomputable def atkinLehnerAntiInvolution [NeZero N] :
    HeckeAntiInvolution (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) :=
  HeckeAntiInvolution.ofAmbient (atkinLehnerHom N) (atkinLehner_involutive N)
    (atkinLehner_mem_Gamma0 N) (atkinLehner_mem_Delta0 N)

end HeckeRing.GL2
