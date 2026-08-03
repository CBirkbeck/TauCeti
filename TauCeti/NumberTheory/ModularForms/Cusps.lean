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
power of `T`, and `Subgroup.integerCuspWidth 𝒢` is the least such exponent. The cosets of the
first `Subgroup.integerCuspWidth 𝒢` powers of `T` are pairwise distinct in `𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ`, and
the integer cusp width is a positive integer multiple of the strict width at `∞`.

## Main declarations

* `TauCeti.Subgroup.integerCuspWidth`.
* `TauCeti.Subgroup.natCast_mem_strictPeriods_iff`: the integer strict periods are the
  multiples of the width.
* `TauCeti.Subgroup.quotient_T_pow_integerCuspWidth_injective`.
* `TauCeti.Subgroup.integerCuspWidth_eq_nat_mul_strictWidthInfty`.

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

/-- The image of `T ^ n : SL(2, ℤ)` in `GL(2, S)`, for a natural exponent. -/
lemma ModularGroup.mapGL_T_pow_eq_upperRightHom {S : Type*} [CommRing S] (n : ℕ) :
    Matrix.SpecialLinearGroup.mapGL S ((ModularGroup.T : SL(2, ℤ))^n) =
      Matrix.GeneralLinearGroup.upperRightHom (n : S) := by
  rw [← zpow_natCast, ModularGroup.mapGL_T_zpow_eq_upperRightHom, Int.cast_natCast]


section IntegerCuspWidth

/-- A finite-index subgroup of `𝒮ℒ` always has a positive natural number in its strict periods,
namely the order of `T` modulo `𝒢 ⊓ 𝒮ℒ`. -/
lemma Subgroup.exists_pos_nat_mem_strictPeriods (𝒢 : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsFiniteRelIndex 𝒮ℒ] :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ∈ 𝒢.strictPeriods := by
  obtain ⟨n, hn_pos, _, hn_mem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := (𝒢 : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))
    ((mapGL ℝ).rangeRestrict ModularGroup.T)
  refine ⟨n, hn_pos, ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, MonoidHom.coe_rangeRestrict, ← map_pow,
    ← zpow_natCast, ModularGroup.mapGL_T_zpow_eq_upperRightHom] at hn_mem
  simpa [Subgroup.mem_strictPeriods_iff] using hn_mem

/-- The smallest positive integer `n` such that the upper-triangular matrix `[1, n; 0, 1]`
lies in `𝒢`; one exists because `𝒢` has finite relative index in `𝒮ℒ`. -/
noncomputable def Subgroup.integerCuspWidth (𝒢 : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsFiniteRelIndex 𝒮ℒ] : ℕ :=
  open Classical in Nat.find (Subgroup.exists_pos_nat_mem_strictPeriods 𝒢)

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex 𝒮ℒ]

/-- The integer cusp width is positive. -/
lemma Subgroup.integerCuspWidth_pos : 0 < Subgroup.integerCuspWidth 𝒢 := by
  classical exact (Nat.find_spec (Subgroup.exists_pos_nat_mem_strictPeriods 𝒢)).1

/-- The integer cusp width is a strict period. -/
lemma Subgroup.integerCuspWidth_mem_strictPeriods :
    (Subgroup.integerCuspWidth 𝒢 : ℝ) ∈ 𝒢.strictPeriods := by
  classical exact (Nat.find_spec (Subgroup.exists_pos_nat_mem_strictPeriods 𝒢)).2

/-- The integer cusp width is minimal among positive integer strict periods. -/
lemma Subgroup.integerCuspWidth_le {n : ℕ} (hpos : 0 < n) (hmem : (n : ℝ) ∈ 𝒢.strictPeriods) :
    Subgroup.integerCuspWidth 𝒢 ≤ n := by
  classical exact Nat.find_le ⟨hpos, hmem⟩

/-- The `integerCuspWidth 𝒢`-th power of `T` lies in `𝒢`. -/
lemma Subgroup.T_pow_integerCuspWidth_mem :
    ((ModularGroup.T : SL(2, ℤ))^(Subgroup.integerCuspWidth 𝒢 : ℕ) : GL (Fin 2) ℝ) ∈ 𝒢 := by
  -- The `GL`-coercion of a power of `T` is definitionally the power of `mapGL T`;
  -- `change` exposes that spelling once.
  change (mapGL ℝ ModularGroup.T)^(Subgroup.integerCuspWidth 𝒢 : ℕ) ∈ 𝒢
  rw [← map_pow, ModularGroup.mapGL_T_pow_eq_upperRightHom, ← mem_strictPeriods_iff]
  exact Subgroup.integerCuspWidth_mem_strictPeriods

/-- The cosets `T ^ j • (𝒢 ⊓ 𝒮ℒ)` for `j < Subgroup.integerCuspWidth 𝒢` are pairwise distinct in
`𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ`. -/
lemma Subgroup.quotient_T_pow_integerCuspWidth_injective :
    Function.Injective (fun j : Fin (Subgroup.integerCuspWidth 𝒢) ↦
      (⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
        𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))) := by
  suffices key : ∀ {a b : ℕ}, a ≤ b → b < Subgroup.integerCuspWidth 𝒢 →
      ((b : ℝ) - (a : ℝ)) ∈ 𝒢.strictPeriods → a = b by
    intro j₁ j₂ hj
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hj
    have hSub : (((((mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))^(j₁ : ℕ)))⁻¹ *
        (mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))^(j₂ : ℕ))) : 𝒮ℒ) : GL (Fin 2) ℝ) =
        mapGL ℝ ((ModularGroup.T : SL(2, ℤ))^((j₂ : ℤ) - (j₁ : ℤ))) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.coe_rangeRestrict,
        MonoidHom.coe_rangeRestrict, ← map_inv, ← map_mul, zpow_sub, zpow_natCast, zpow_natCast]
      exact congr_arg _ ((Commute.pow_pow_self ModularGroup.T _ _).inv_right).eq.symm
    -- Align the coercion routes `ℤ → ℝ` on the exponent difference before reading off
    -- strict-period membership.
    rw [hSub, ModularGroup.mapGL_T_zpow_eq_upperRightHom,
      show (((j₂ : ℤ) - (j₁ : ℤ) : ℤ) : ℝ) = ((j₂ : ℝ) - (j₁ : ℝ)) by push_cast; ring,
      ← mem_strictPeriods_iff] at hj
    exact Fin.ext <| (le_total (j₁ : ℕ) (j₂ : ℕ)).elim (key · j₂.isLt hj) fun hle ↦
      (key hle j₁.isLt (by simpa [neg_sub] using neg_mem hj)).symm
  intro a b hab hb hmem
  by_contra hne
  exact absurd (Subgroup.integerCuspWidth_le (n := b - a) (by lia)
    (by rwa [Nat.cast_sub hab])) (by lia)

/-- The integer cusp width is a positive integer multiple of the strict width at `∞`. -/
lemma Subgroup.integerCuspWidth_eq_nat_mul_strictWidthInfty [DiscreteTopology 𝒢.strictPeriods] :
    ∃ m : ℕ, 0 < m ∧ (Subgroup.integerCuspWidth 𝒢 : ℝ) = m * 𝒢.strictWidthInfty := by
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp <|
    Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty (𝒢 := 𝒢) ▸
      Subgroup.integerCuspWidth_mem_strictPeriods
  rw [zsmul_eq_mul] at hm
  have hm_pos : (0 : ℤ) < m := by
    have : (0 : ℝ) < m :=
      pos_of_mul_pos_left (hm ▸ mod_cast Subgroup.integerCuspWidth_pos) 𝒢.strictWidthInfty_nonneg
    exact_mod_cast this
  exact ⟨m.toNat, by lia, by rw [← hm, ← Int.cast_natCast, Int.toNat_of_nonneg hm_pos.le]⟩

/-- The natural numbers among the strict periods are exactly the multiples of the
integer cusp width. -/
lemma Subgroup.natCast_mem_strictPeriods_iff {n : ℕ} :
    (n : ℝ) ∈ 𝒢.strictPeriods ↔ Subgroup.integerCuspWidth 𝒢 ∣ n := by
  refine ⟨fun hn ↦ ?_, fun ⟨q, hq⟩ ↦ ?_⟩
  · suffices hr : n % Subgroup.integerCuspWidth 𝒢 = 0 from Nat.dvd_of_mod_eq_zero hr
    by_contra hr0
    -- The remainder is itself a strict period, contradicting minimality.
    have hrmem : ((n % Subgroup.integerCuspWidth 𝒢 : ℕ) : ℝ) ∈ 𝒢.strictPeriods := by
      have hcast : ((Subgroup.integerCuspWidth 𝒢 * (n / Subgroup.integerCuspWidth 𝒢) +
          n % Subgroup.integerCuspWidth 𝒢 : ℕ) : ℝ) = (n : ℝ) :=
        congrArg (fun m : ℕ => (m : ℝ)) (Nat.div_add_mod n (Subgroup.integerCuspWidth 𝒢))
      have hsub : ((n % Subgroup.integerCuspWidth 𝒢 : ℕ) : ℝ) =
          (n : ℝ) - (n / Subgroup.integerCuspWidth 𝒢 : ℕ) *
            (Subgroup.integerCuspWidth 𝒢 : ℝ) := by
        push_cast at hcast ⊢
        linarith
      have hmul := nsmul_mem (Subgroup.integerCuspWidth_mem_strictPeriods (𝒢 := 𝒢))
        (n / Subgroup.integerCuspWidth 𝒢)
      rw [nsmul_eq_mul] at hmul
      rw [hsub]
      exact sub_mem hn hmul
    exact absurd (Subgroup.integerCuspWidth_le (Nat.pos_of_ne_zero hr0) hrmem)
      (not_le.mpr (Nat.mod_lt _ Subgroup.integerCuspWidth_pos))
  · subst hq
    have hmul := nsmul_mem (Subgroup.integerCuspWidth_mem_strictPeriods (𝒢 := 𝒢)) q
    rw [nsmul_eq_mul, mul_comm] at hmul
    push_cast
    exact hmul

/-- The powers of `T` lying in `𝒢` are exactly those with exponent divisible by the
integer cusp width. -/
lemma Subgroup.T_pow_mem_iff {n : ℕ} :
    ((ModularGroup.T : SL(2, ℤ))^n : GL (Fin 2) ℝ) ∈ 𝒢 ↔
      Subgroup.integerCuspWidth 𝒢 ∣ n := by
  -- The `GL`-coercion of a power of `T` is definitionally the power of `mapGL T`;
  -- `change` exposes that spelling once.
  change (mapGL ℝ ModularGroup.T)^n ∈ 𝒢 ↔ _
  rw [← map_pow, ModularGroup.mapGL_T_pow_eq_upperRightHom, ← mem_strictPeriods_iff,
    Subgroup.natCast_mem_strictPeriods_iff]

end IntegerCuspWidth

end TauCeti

end
