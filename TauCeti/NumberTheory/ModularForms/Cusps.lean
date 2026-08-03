/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

/-!
# The integer cusp width of a finite-index subgroup

The image of `T = [1, 1; 0, 1]` in `GL(2, ℝ)` and its powers are the upper-triangular
shift matrices; a subgroup `𝒢` of finite relative index in `𝒮ℒ` contains some positive
power of `T`, and `integerCuspWidth 𝒢` is the least such exponent. The cosets of the
first `integerCuspWidth 𝒢` powers of `T` are pairwise distinct in `𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ`, and
the integer cusp width is a positive integer multiple of the strict width at `∞`.

## Main declarations

* `TauCeti.integerCuspWidth`.
* `TauCeti.quotient_T_pow_injective_integerCuspWidth`.
* `TauCeti.integerCuspWidth_eq_nat_mul_strictWidthInfty`.

## References

* [Mathlib PR #39087](https://github.com/leanprover-community/mathlib4/pull/39087)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup Subgroup

open scoped MatrixGroups

namespace TauCeti

/-- The image of `T : SL(2, ℤ)` in `GL(2, S)` for any commutative ring `S` is the
upper-triangular matrix `[1, 1; 0, 1]`. -/
lemma ModularGroup.mapGL_T_eq_upperRightHom {S : Type*} [CommRing S] :
    Matrix.SpecialLinearGroup.mapGL S (ModularGroup.T : SL(2, ℤ)) =
      Matrix.GeneralLinearGroup.upperRightHom (1 : S) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mapGL_coe_matrix, ModularGroup.coe_T]

/-- The image of `T ^ n : SL(2, ℤ)` in `GL(2, S)` for any commutative ring `S` is the
upper-triangular matrix `[1, n; 0, 1]`. -/
lemma ModularGroup.mapGL_T_zpow_eq_upperRightHom {S : Type*} [CommRing S] (n : ℤ) :
    Matrix.SpecialLinearGroup.mapGL S ((ModularGroup.T : SL(2, ℤ))^n) =
      Matrix.GeneralLinearGroup.upperRightHom (n : S) := by
  rw [map_zpow, ModularGroup.mapGL_T_eq_upperRightHom, ← AddChar.map_zsmul_eq_zpow, zsmul_one]

lemma ModularGroup.mapGL_T_pow_eq_upperRightHom {S : Type*} [CommRing S] (n : ℕ) :
    Matrix.SpecialLinearGroup.mapGL S ((ModularGroup.T : SL(2, ℤ))^n) =
      Matrix.GeneralLinearGroup.upperRightHom (n : S) := by
  rw [← zpow_natCast, ModularGroup.mapGL_T_zpow_eq_upperRightHom, Int.cast_natCast]


section IntegerCuspWidth

/-- A finite-index subgroup of `𝒮ℒ` always has a positive natural number in its strict periods,
namely the order of `T` modulo `𝒢 ⊓ 𝒮ℒ`. -/
lemma exists_pos_nat_mem_strictPeriods (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsFiniteRelIndex 𝒮ℒ] :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ∈ 𝒢.strictPeriods := by
  obtain ⟨n, hn_pos, _, hn_mem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := (𝒢 : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))
    ((mapGL ℝ).rangeRestrict ModularGroup.T)
  refine ⟨n, hn_pos, ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, MonoidHom.coe_rangeRestrict, ← map_pow,
    ← zpow_natCast, ModularGroup.mapGL_T_zpow_eq_upperRightHom] at hn_mem
  simpa [Subgroup.mem_strictPeriods_iff] using hn_mem

/-- The smallest positive integer `n` such that the upper-triangular matrix `[1, n; 0, 1]` lies in
`𝒢` (taking `0` if no such integer exists; one always exists when `𝒢` has finite index in `𝒮ℒ`). -/
noncomputable def integerCuspWidth (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsFiniteRelIndex 𝒮ℒ] : ℕ :=
  open Classical in Nat.find (exists_pos_nat_mem_strictPeriods 𝒢)

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex 𝒮ℒ]

lemma integerCuspWidth_pos : 0 < integerCuspWidth 𝒢 := by
  classical exact (Nat.find_spec (exists_pos_nat_mem_strictPeriods 𝒢)).1

lemma integerCuspWidth_mem_strictPeriods : (integerCuspWidth 𝒢 : ℝ) ∈ 𝒢.strictPeriods := by
  classical exact (Nat.find_spec (exists_pos_nat_mem_strictPeriods 𝒢)).2

lemma integerCuspWidth_le {n : ℕ} (hpos : 0 < n) (hmem : (n : ℝ) ∈ 𝒢.strictPeriods) :
    integerCuspWidth 𝒢 ≤ n := by
  classical exact Nat.find_le ⟨hpos, hmem⟩

lemma T_pow_integerCuspWidth_mem :
    ((ModularGroup.T : SL(2, ℤ))^(integerCuspWidth 𝒢 : ℕ) : GL (Fin 2) ℝ) ∈ 𝒢 := by
  change (mapGL ℝ ModularGroup.T)^(integerCuspWidth 𝒢 : ℕ) ∈ 𝒢
  rw [← map_pow, ModularGroup.mapGL_T_pow_eq_upperRightHom, ← mem_strictPeriods_iff]
  exact integerCuspWidth_mem_strictPeriods

/-- The cosets `T ^ j • (𝒢 ⊓ 𝒮ℒ)` for `j < integerCuspWidth 𝒢` are pairwise distinct in
`𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ`. -/
lemma quotient_T_pow_injective_integerCuspWidth [DiscreteTopology 𝒢.strictPeriods] :
    Function.Injective (fun j : Fin (integerCuspWidth 𝒢) ↦
      (⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
        𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))) := by
  suffices key : ∀ {a b : ℕ}, a ≤ b → b < integerCuspWidth 𝒢 →
      ((b : ℝ) - (a : ℝ)) ∈ 𝒢.strictPeriods → a = b by
    intro j₁ j₂ hj
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hj
    have hSub : (((((mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))^(j₁ : ℕ)))⁻¹ *
        (mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))^(j₂ : ℕ))) : 𝒮ℒ) : GL (Fin 2) ℝ) =
        mapGL ℝ ((ModularGroup.T : SL(2, ℤ))^((j₂ : ℤ) - (j₁ : ℤ))) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.coe_rangeRestrict,
        MonoidHom.coe_rangeRestrict, ← map_inv, ← map_mul, zpow_sub, zpow_natCast, zpow_natCast]
      exact congr_arg _ ((Commute.pow_pow_self ModularGroup.T _ _).inv_right).eq.symm
    rw [hSub, ModularGroup.mapGL_T_zpow_eq_upperRightHom,
      show (((j₂ : ℤ) - (j₁ : ℤ) : ℤ) : ℝ) = ((j₂ : ℝ) - (j₁ : ℝ)) by push_cast; ring,
      ← mem_strictPeriods_iff] at hj
    exact Fin.ext <| (le_total (j₁ : ℕ) (j₂ : ℕ)).elim (key · j₂.isLt hj) fun hle ↦
      (key hle j₁.isLt (by simpa [neg_sub] using neg_mem hj)).symm
  intro a b hab hb hmem
  by_contra hne
  exact absurd (integerCuspWidth_le (n := b - a) (by lia)
    (by rwa [Nat.cast_sub hab])) (by lia)

/-- The integer cusp width is a positive integer multiple of the strict width at `∞`. -/
lemma integerCuspWidth_eq_nat_mul_strictWidthInfty [DiscreteTopology 𝒢.strictPeriods] :
    ∃ m : ℕ, 0 < m ∧ (integerCuspWidth 𝒢 : ℝ) = m * 𝒢.strictWidthInfty := by
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp <|
    Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty (𝒢 := 𝒢) ▸
      integerCuspWidth_mem_strictPeriods
  rw [zsmul_eq_mul] at hm
  have hm_pos : (0 : ℤ) < m := by
    have : (0 : ℝ) < m :=
      pos_of_mul_pos_left (hm ▸ mod_cast integerCuspWidth_pos) 𝒢.strictWidthInfty_nonneg
    exact_mod_cast this
  exact ⟨m.toNat, by lia, by rw [← hm, ← Int.cast_natCast, Int.toNat_of_nonneg hm_pos.le]⟩

end IntegerCuspWidth

end TauCeti

end
