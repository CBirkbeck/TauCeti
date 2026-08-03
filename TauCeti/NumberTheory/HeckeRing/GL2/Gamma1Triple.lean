/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.NumberTheory.HeckeRing.GLn.Basic

/-!
# The Hecke triple for `Γ₁(N)`

The submonoid `Δ₁(N)` of `GL₂(ℚ)` — integral matrices with `a ≡ 1 (mod N)`, `c ≡ 0 (mod N)`
and positive determinant — and the Hecke triple `(Γ₁(N), Δ₁(N))`, the level-`N` foundation for
the Hecke operators on `M_k(Γ₁(N))` (Miyake §4.5, Diamond–Shurman §5.1). Commensuration
reduces to the `GL_n` case: `Δ₁(N) ≤ posDetInt ≤ commensurator(SL₂(ℤ)) = commensurator(Γ₁(N))`,
the last equality because `Γ₁(N)` has finite index in `SL₂(ℤ)`.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Gamma1Pair.lean`, Chris Birkbeck), realizing Layer 2 of the
ModularForms roadmap; the AINTLIB `HeckePair` bundle is replaced by Mathlib's `IsHeckeTriple`.
The diamond operators and character spaces from the same source file are Layer-0 material and
live in `TauCeti/NumberTheory/ModularForms/DiamondOperators.lean`.

## Main definitions

* `Delta1_submonoid`: `Δ₁(N)`, integral matrices with `a ≡ 1`, `c ≡ 0 (mod N)` and positive
  determinant.

## Main results

* `Gamma1_le_Delta1`: `Γ₁(N) ≤ Δ₁(N)` as submonoids.
* `Delta1_le_commensurator`: `Δ₁(N) ≤ commensurator(Γ₁(N))`.
* the `IsHeckeTriple (Delta1_submonoid N) ((Gamma1 N).map (mapGL ℚ)) _` instance.

## References

* Miyake, *Modular forms*, §4.5
* Diamond–Shurman, *A first course in modular forms*, §5.1
-/

public section

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ}

/-- `Δ₁(N)`: integer 2×2 matrices with `a ≡ 1 (mod N)`, `c ≡ 0 (mod N)`,
and positive determinant. This pairs with `Γ₁(N)` to form a Hecke triple. -/
noncomputable def Delta1_submonoid (N : ℕ) : Submonoid (GL (Fin 2) ℚ) where
  carrier := {g | HasIntEntries 2 g ∧ 0 < (↑g : Matrix (Fin 2) (Fin 2) ℚ).det ∧
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ, (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧
      (N : ℤ) ∣ A 1 0 ∧ (A 0 0 : ZMod N) = 1}
  one_mem' := ⟨hasIntEntries_one 2, by simp, 1, by simp, by simp, by simp⟩
  mul_mem' := by
    intro a b ⟨ha, hda, A, hA, hAN, hAone⟩ ⟨hb, hdb, B, hB, hBN, hBone⟩
    refine ⟨ha.mul _ hb, by simpa [det_mul] using mul_pos hda hdb, A * B, ?_, ?_, ?_⟩
    · ext i j
      simp [hA, hB, mul_apply, map_apply]
    · simp only [mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hAN _) (dvd_mul_of_dvd_right hBN _)
    · simp [mul_apply, Fin.sum_univ_two, hAone, hBone,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hBN]

/-- `Γ₁(N) ≤ Δ₁(N)`: the congruence subgroup embeds into the submonoid. -/
lemma Gamma1_le_Delta1 (N : ℕ) [NeZero N] :
    ((Gamma1 N).map (mapGL ℚ)).toSubmonoid ≤ Delta1_submonoid N := by
  intro g hg
  obtain ⟨σ, hσ_mem, rfl⟩ := hg
  obtain ⟨ha, -, hc⟩ := (Gamma1_mem _ _).mp hσ_mem
  refine ⟨hasIntEntries_of_mem_SLnZ 2 (coe_mem_SLnZ 2 σ), ?_, (σ : Matrix (Fin 2) (Fin 2) ℤ), rfl,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc, ha⟩
  rw [mapGL_coe_matrix, (SpecialLinearGroup.map (algebraMap ℤ ℚ) σ).prop]
  exact one_pos

private lemma Delta1_le_posDetInt (N : ℕ) : Delta1_submonoid N ≤ posDetInt_submonoid 2 :=
  fun _ ⟨hint, hdet, _⟩ ↦ (mem_posDetInt_submonoid_iff 2).mpr ⟨hint, hdet⟩

private lemma Gamma1_map_commensurable_SLnZ (N : ℕ) [NeZero N] :
    Subgroup.Commensurable ((Gamma1 N).map (mapGL ℚ))
      (Subgroup.map (mapGL ℚ : SpecialLinearGroup (Fin 2) ℤ →* GL (Fin 2) ℚ) ⊤) := by
  constructor
  · rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective, Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  · rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective, Subgroup.relIndex_top_left]
    exact one_ne_zero

/-- `Δ₁(N) ≤ commensurator(Γ₁(N))`. The proof chains:
`Δ₁(N) ≤ posDetInt ≤ commensurator(SL₂(ℤ)) = commensurator(Γ₁(N))`,
where the last equality holds because `Γ₁(N)` has finite index in `SL₂(ℤ)`. -/
lemma Delta1_le_commensurator (N : ℕ) [NeZero N] :
    Delta1_submonoid N ≤ (commensurator ((Gamma1 N).map (mapGL ℚ))).toSubmonoid := by
  rw [Subgroup.Commensurable.eq (Gamma1_map_commensurable_SLnZ N), ← SLnZ_eq_map_top]
  exact (Delta1_le_posDetInt N).trans (posDetInt_le_commensurator 2)

/-- **The Hecke triple `(Γ₁(N), Δ₁(N))`** for level `N`: the foundation for the Hecke
operators on `M_k(Γ₁(N))`. -/
instance [NeZero N] :
    IsHeckeTriple (Delta1_submonoid N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) :=
  IsHeckeTriple.of_diagonal (Gamma1_le_Delta1 N) (Delta1_le_commensurator N)

end HeckeRing.GL2
