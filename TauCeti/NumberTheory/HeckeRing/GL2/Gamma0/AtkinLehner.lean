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

Conjugating the transpose by `w = diag(1, N)`,
```
ι(g) = w · gᵀ · w⁻¹,
```
is an anti-automorphism of `GL₂(ℚ)` preserving both the image of `Γ₀(N)` and the submonoid
`Δ₀(N)`, so it restricts to a `HeckeAntiInvolution` of the `Γ₀(N)` Hecke datum.

At level one the transpose alone already does this — that is
`HeckeRing.GLn.transposeAntiInvolution`, and it is why the `GL_n` Hecke ring is commutative.
It does **not** survive the congruence condition: transposition carries `Γ₀(N)` to `Γ⁰(N)`,
swapping which off-diagonal entry is divisible by `N`. Conjugating by `w` swaps it back, which
is exactly what the Atkin-Lehner twist buys.

On entries the map is `(a, b; N c, e) ↦ (a, c; N b, e)`: the lower-left entry stays divisible
by `N`, the determinant is unchanged, and — the point of the construction — the upper-left
entry is untouched, so the coprimality condition cutting out `Δ₀(N)` transfers with no work.
Integrality of the new upper-right entry is precisely the hypothesis `N ∣ A 1 0`.

This file builds the anti-involution only. Commutativity of `R(Γ₀(N), Δ₀(N))` needs the further
input that `ι` fixes every double coset, which `HeckeCosetModule.mul_comm_of_antiInvolution`
takes as a separate hypothesis (Shimura, Proposition 3.8).

Ported from the AINTLIB `LeanModularForms` project (Chris Birkbeck),
[`HeckeRIngs/GLn/CongruenceHecke/AtkinLehner.lean`](https://github.com/CBirkbeck/AINTLIB),
declarations `wN`, `Gamma0_AL_hom`, `Gamma0_AL_involutive`, `Gamma0_AL_map_H`,
`Gamma0_AL_map_Δ` and `Gamma0_antiInvolution`. The source states its own transpose equivalence
and diagonal-matrix API; here those come from `GLn/TransposeAntiInvolution.lean` and
`GLn/DiagonalCosets.lean` instead, and the four-field bundle is assembled by
`HeckeAntiInvolution.ofAmbient`.

## Main definitions

* `HeckeRing.GL2.atkinLehnerAntiInvolution`: the anti-involution of the `Γ₀(N)` Hecke pair.

## Main results

* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar`: how it acts, `g ↦ w · gᵀ · w⁻¹`. The bundle
  itself is opaque, so this is the elimination rule a consumer works with.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.8.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup HeckeRing.GLn

open scoped MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- The scaling matrix `w = diag(1, N)` by which the transpose is conjugated.

This is **not** the Atkin-Lehner matrix of the operator `𝒲_Q`, which is `!![0, -1; N, 0]`; it is
only the diagonal rescaling that repairs the transpose's failure to preserve `Γ₀(N)`.

No `NeZero N` is needed to write it down — `natDiagGL` takes the junk value `1` when an entry
vanishes. The hypothesis first appears at `atkinLehner_unop_val`, where the entries of `w` are
evaluated. -/
private noncomputable def atkinLehnerScaleMatrix : GL (Fin 2) ℚ :=
  natDiagGL 2 ![1, N]

/-- `ι(g) = w · gᵀ · w⁻¹`, as a homomorphism to the opposite group. -/
private noncomputable def atkinLehnerHom : GL (Fin 2) ℚ →* (GL (Fin 2) ℚ)ᵐᵒᵖ where
  toFun g := MulOpposite.op (atkinLehnerScaleMatrix N *
    (transposeGLEquiv 2 g).unop * (atkinLehnerScaleMatrix N)⁻¹)
  map_one' := by simp
  map_mul' a b := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, MulOpposite.unop_mul]
    have h1 : (transposeGLEquiv 2 (a * b)).unop =
        (transposeGLEquiv 2 b).unop * (transposeGLEquiv 2 a).unop := by
      simp only [map_mul, MulOpposite.unop_mul]
    rw [h1]; group

/-- Transposition fixes `w`, because `w` is diagonal. -/
private lemma transposeGLEquiv_atkinLehnerScaleMatrix :
    (transposeGLEquiv 2 (atkinLehnerScaleMatrix N)).unop = atkinLehnerScaleMatrix N := by
  rw [atkinLehnerScaleMatrix]
  exact transposeGLEquiv_natDiagGL 2 ![1, N]

/-- `ι` is involutive: transposition is, and the two conjugations by `w` cancel because
transposition fixes `w`. -/
private lemma atkinLehner_involutive (g : GL (Fin 2) ℚ) :
    (atkinLehnerHom N (atkinLehnerHom N g).unop).unop = g := by
  simp only [atkinLehnerHom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
  have h_tr : (transposeGLEquiv 2 (atkinLehnerScaleMatrix N *
      (transposeGLEquiv 2 g).unop * (atkinLehnerScaleMatrix N)⁻¹)).unop =
      (transposeGLEquiv 2 (atkinLehnerScaleMatrix N)⁻¹).unop *
        (transposeGLEquiv 2 (transposeGLEquiv 2 g).unop).unop *
        (transposeGLEquiv 2 (atkinLehnerScaleMatrix N)).unop := by
    rw [map_mul, map_mul]
    simp only [MulOpposite.unop_mul]
    group
  have h_inv : (transposeGLEquiv 2 (atkinLehnerScaleMatrix N)⁻¹).unop =
      (atkinLehnerScaleMatrix N)⁻¹ := by
    rw [map_inv, MulOpposite.unop_inv, transposeGLEquiv_atkinLehnerScaleMatrix]
  rw [h_tr, transposeGLEquiv_transposeGLEquiv, transposeGLEquiv_atkinLehnerScaleMatrix, h_inv]
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
  have hpos : ∀ i : Fin 2, 0 < (![1, N]) i := by
    intro i; fin_cases i <;> simp [NeZero.pos]
  have hNe : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hw : ((atkinLehnerScaleMatrix N : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      Matrix.diagonal ![1, (N : ℚ)] := by
    rw [atkinLehnerScaleMatrix, natDiagGL_coe 2 _ hpos]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hwinv : (((atkinLehnerScaleMatrix N)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      Matrix.diagonal ![1, (N : ℚ)⁻¹] := by
    rw [Matrix.coe_units_inv, hw]
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hNe]
  have hcast : ((A 1 0 : ℤ) : ℚ) = (N : ℚ) * ((c : ℤ) : ℚ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) hc
  simp only [atkinLehnerHom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op,
    Units.val_mul, hw, hwinv, transposeGLEquiv_coe, hA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply,
      Matrix.transpose_apply, hcast] <;>
    field_simp

/-- Conjugating the transpose by `w` swaps which off-diagonal entry carries the factor `N`, so
the determinant is unchanged. Both membership proofs need this, at different right-hand sides. -/
private lemma det_swapEntries (A : Matrix (Fin 2) (Fin 2) ℤ) (c : ℤ) (hc : A 1 0 = (N : ℤ) * c) :
    (Matrix.of ![![A 0 0, c], ![(N : ℤ) * A 0 1, A 1 1]]).det = A.det := by
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hc]
  ring

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
  have hB_det : B.det = 1 := by rw [hB, det_swapEntries N A c hc, hA_def, σ.2]
  refine ⟨⟨B, hB_det⟩, Gamma0_mem.mpr ?_, Units.ext ?_⟩
  · simp only [hB, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_mul_right _ _
  · -- the entrywise cast of an integral special-linear element, inlined as at
    -- `GL2/DiagonalCosetDegree.lean`
    have hval : ∀ μ : SpecialLinearGroup (Fin 2) ℤ,
        ((mapGL ℚ μ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
          (μ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) :=
      fun μ ↦ by simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
    rw [atkinLehner_unop_val N _ A (hval σ) c hc, hval ⟨B, hB_det⟩]

/-- `ι` preserves `Δ₀(N)`: the determinant and the upper-left entry are unchanged, and the new
lower-left entry `N · A 0 1` is visibly divisible by `N`. -/
private lemma atkinLehner_mem_Delta0 [NeZero N] (g : GL (Fin 2) ℚ) (hg : g ∈ Delta0 N) :
    (atkinLehnerHom N g).unop ∈ Delta0 N := by
  obtain ⟨A, hA, hdet, hAN, hAunit⟩ := (mem_Delta0_iff N).mp hg
  obtain ⟨c, hc⟩ := hAN
  set B : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![A 0 0, c], ![(N : ℤ) * A 0 1, A 1 1]] with hB
  have hval := atkinLehner_unop_val N g A hA c hc
  have hB_det : B.det = A.det := by rw [hB, det_swapEntries N A c hc]
  refine (mem_Delta0_iff N).mpr ⟨B, hval, ?_, ⟨A 0 1, by simp [hB]⟩, ?_⟩
  · rw [hval, ← Int.cast_det, hB_det, Int.cast_det, ← hA]
    exact hdet
  · simpa [hB] using hAunit

/-- **The Atkin-Lehner anti-involution** of the `Γ₀(N)` Hecke pair. -/
noncomputable def atkinLehnerAntiInvolution [NeZero N] :
    HeckeAntiInvolution (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) :=
  HeckeAntiInvolution.ofAmbient (atkinLehnerHom N) (atkinLehner_involutive N)
    (atkinLehner_mem_Gamma0 N) (atkinLehner_mem_Delta0 N)

/-- The anti-involution acts by conjugating the transpose by `w`, unfolding the sealed
definition. -/
@[simp] lemma atkinLehnerAntiInvolution_bar [NeZero N] {x : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N) :
    (atkinLehnerAntiInvolution N).bar x hx =
      natDiagGL 2 ![1, N] * (transposeGLEquiv 2 x).unop * (natDiagGL 2 ![1, N])⁻¹ :=
  HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx

end HeckeRing.GL2
