/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The Hecke triple of `Γ₁(N)`

The submonoid `Δ₁(N) ⊆ GL₂(ℚ)` of integral matrices with positive determinant whose first
column is congruent to `(1, 0)` modulo `N`, and the Hecke triple it forms with the image of
the congruence subgroup `Γ₁(N)`. This is the level-`N` counterpart of the arithmetic triple
`(Δₙ, SL_n(ℤ))`, and the setting in which the Hecke operators on `M_k(Γ₁(N))` live.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Gamma1Pair.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).

## Main definitions

* `HeckeRing.GL2.Delta1`: the submonoid `Δ₁(N)`.
* `HeckeRing.GL2.Gamma1Image`: the image of `Γ₁(N)` in `GL₂(ℚ)`.

## Main results

* `HeckeRing.GL2.Gamma1Image_le_Delta1`: `Γ₁(N) ≤ Δ₁(N)`.
* `HeckeRing.GL2.Delta1_le_commensurator`: `Δ₁(N)` lies in the commensurator of `Γ₁(N)`.
* the `IsHeckeTriple (Delta1 N) (Gamma1Image N) (Gamma1Image N)` instance.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup
  Subgroup.Commensurable HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- The image of `Γ₁(N)` in `GL₂(ℚ)`. -/
noncomputable def Gamma1Image : Subgroup (GL (Fin 2) ℚ) :=
  (Gamma1 N).map (mapGL ℚ)

/-- Membership in the image of `Γ₁(N)`, by an integral witness. -/
@[simp] lemma mem_Gamma1Image_iff {g : GL (Fin 2) ℚ} :
    g ∈ Gamma1Image N ↔ ∃ σ ∈ Gamma1 N, mapGL ℚ σ = g := by
  rw [Gamma1Image, Subgroup.mem_map]

/-- `Δ₁(N)`: integral matrices of positive determinant whose first column is congruent to
`(1, 0)` modulo `N`, i.e. `a ≡ 1` and `c ≡ 0 (mod N)`. Note this constrains only the first
column: the lower-right entry is unrestricted. -/
noncomputable def Delta1 : Submonoid (GL (Fin 2) ℚ) where
  carrier := {g | ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
    (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧
      0 < (↑g : Matrix (Fin 2) (Fin 2) ℚ).det ∧ (N : ℤ) ∣ A 1 0 ∧ (A 0 0 : ZMod N) = 1}
  one_mem' := ⟨1, by simp, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨A, hA, hda, hAN, hAone⟩ ⟨B, hB, hdb, hBN, hBone⟩
    refine ⟨A * B, ?_, ?_, ?_, ?_⟩
    · ext i j
      simp [hA, hB, Matrix.mul_apply, Matrix.map_apply]
    · simpa [Matrix.det_mul] using mul_pos hda hdb
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hAN _) (dvd_mul_of_dvd_right hBN _)
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hAone, hBone,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hBN]

/-- Membership in `Δ₁(N)`, unfolded. -/
@[simp] lemma mem_Delta1_iff {g : GL (Fin 2) ℚ} :
    g ∈ Delta1 N ↔ ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
      (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧
        0 < (↑g : Matrix (Fin 2) (Fin 2) ℚ).det ∧ (N : ℤ) ∣ A 1 0 ∧
          (A 0 0 : ZMod N) = 1 :=
  Iff.rfl

/-- `Γ₁(N) ≤ Δ₁(N)`: the congruence subgroup embeds in the submonoid. -/
lemma Gamma1Image_le_Delta1 : (Gamma1Image N).toSubmonoid ≤ Delta1 N := by
  intro g hg
  obtain ⟨σ, hσ, rfl⟩ := (mem_Gamma1Image_iff N).mp hg
  obtain ⟨ha, -, hc⟩ := (Gamma1_mem _ _).mp hσ
  refine (mem_Delta1_iff N).mpr ⟨(σ : Matrix (Fin 2) (Fin 2) ℤ), ?_, ?_, ?_, ha⟩
  · rw [mapGL_coe_matrix]
    rfl
  · rw [mapGL_coe_matrix, (SpecialLinearGroup.map (algebraMap ℤ ℚ) σ).prop]
    exact one_pos
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc

/-- `Δ₁(N)` consists of integral matrices with positive determinant. -/
lemma Delta1_le_posDetInt : Delta1 N ≤ posDetInt 2 := by
  intro g hg
  obtain ⟨A, hA, hdet, -, -⟩ := (mem_Delta1_iff N).mp hg
  exact (mem_posDetInt_iff 2).mpr ⟨(hasIntEntries_iff 2).mpr ⟨A, hA⟩, hdet⟩

variable [NeZero N]

/-- `Γ₁(N)` is commensurable with `SL₂(ℤ)`: it has finite index in it. -/
lemma commensurable_Gamma1Image_SLnZ : Commensurable (Gamma1Image N) (SLnZ 2) := by
  have hSL : SLnZ 2 =
      Subgroup.map (mapGL ℚ : SpecialLinearGroup (Fin 2) ℤ →* GL (Fin 2) ℚ) ⊤ := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    exact (mem_SLnZ_iff 2).trans (by simp)
  constructor
  · rw [Gamma1Image, hSL,
      Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective, Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  · rw [Gamma1Image, hSL,
      Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective, Subgroup.relIndex_top_left]
    exact one_ne_zero

/-- `Δ₁(N)` lies in the commensurator of `Γ₁(N)`: it lies in that of `SL₂(ℤ)`, and the two
groups are commensurable. -/
lemma Delta1_le_commensurator : Delta1 N ≤ (commensurator (Gamma1Image N)).toSubmonoid := by
  rw [Subgroup.Commensurable.eq (commensurable_Gamma1Image_SLnZ N)]
  exact (Delta1_le_posDetInt N).trans (posDetInt_le_commensurator 2)

/-- **The Hecke triple of `Γ₁(N)`**: `Γ₁(N) ≤ Δ₁(N) ≤ commensurator(Γ₁(N))` inside
`GL₂(ℚ)` — the setting of the Hecke operators on modular forms of level `N`. -/
instance : IsHeckeTriple (Delta1 N) (Gamma1Image N) (Gamma1Image N) :=
  IsHeckeTriple.of_diagonal (Gamma1Image_le_Delta1 N) (Delta1_le_commensurator N)

end HeckeRing.GL2
