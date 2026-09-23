/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.MainTerm
import TauCeti.NumberTheory.NumberField.Global.Counting.Ray.IdealCount
import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.LatticeCount
import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.MainTerm
import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Reindex
import TauCeti.RingTheory.Ideal.CoprimeCoset

/-!
# The asymptotic count of the integral ideals of a ray class

Let `𝔪` be a modulus of a number field `K` of degree `n`.  This file proves that the number of
nonzero integral ideals prime to `𝔪` in a fixed ray class with absolute norm at most `x` is
`rayClassIdealMainTerm 𝔪 * x + O(x ^ (1 - 1 / n))`, with the same main term and the same power
saving for every class.

The ideals of a class are matched, after multiplying by an ideal of the inverse class, with the
points of one coset of a congruence lattice in the ray fundamental domain, each ideal accounting
for the same number of points; the lattice-point count in that domain then gives the estimate.

## Main results

* `TauCeti.GlobalNumberFields.rayClassIdealCount`: the ray class ideal counting function is
  `rayClassIdealMainTerm 𝔪 * x + O(x ^ (1 - δ))` for some `δ > 0` uniform in the class.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI.
-/

public section

open Asymptotics Filter MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped nonZeroDivisors Pointwise

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The ray class ideal count.**  For every modulus `𝔪` there is a power saving `δ > 0` such
that, in each ray class `c` of `𝔪`, the number of nonzero integral ideals prime to `𝔪` of norm at
most `x` is `rayClassIdealMainTerm 𝔪 * x + O(x ^ (1 - δ))`.  One can take `δ = 1 / [K : ℚ]`. -/
theorem rayClassIdealCount (𝔪 : Modulus K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : RayClassGroup 𝔪,
      (fun x : ℝ =>
          (rayClassIdealCountingFunction 𝔪 c x : ℝ) - rayClassIdealMainTerm 𝔪 * x) =O[atTop]
        (fun x : ℝ => x ^ (1 - δ)) := by
  -- the volume on the mixed space is only an instance classically
  classical
  refine ⟨(finrank ℚ K : ℝ)⁻¹, inv_pos.mpr (Nat.cast_pos.mpr finrank_pos), fun c ↦ ?_⟩
  obtain ⟨𝔞, h𝔞⟩ := idealClass_surjective 𝔪 c⁻¹
  have h𝔞0 := (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp 𝔞.prop).1
  set 𝔞' : (Ideal (𝓞 K))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞0⟩
  -- an element of `𝔞` congruent to one modulo `𝔪₀` places the counted points in one coset
  obtain ⟨ξ, hξ𝔞, hξ𝔪⟩ := Ideal.isCoprime_iff_exists_mem_and_sub_one_mem.mp <|
    Ideal.isCoprime_iff_sup_eq.mpr
      (Modulus.isCoprimeTo_iff_sup_eq_top.mp (Modulus.mem_integralIdealsPrimeTo.mp 𝔞.prop)).2
  obtain ⟨A, -, hA⟩ :=
    exists_abs_ncard_rayFundamentalDomain_inter_norm_le_inter_vadd_sub_le 𝔪
      (FractionalIdeal.mk0 K 𝔞')
  have hcoef := measureReal_div_covolume_congruenceLattice_mul_absNorm 𝔪 𝔞'
  set N : ℝ := (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ)
  set w : ℝ := (Nat.card (unitsCongruenceTorsion 𝔪) : ℝ)
  have hN : 1 ≤ N := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr
    (mt Ideal.absNorm_eq_zero_iff.mp h𝔞0))
  have : Finite (unitsCongruenceTorsion 𝔪) := Finite.of_injective
    (Subgroup.inclusion fun _ hu ↦ (mem_unitsCongruenceTorsion.mp hu).2)
    (Subgroup.inclusion_injective _)
  have hw : 0 < w := Nat.cast_pos.mpr Nat.card_pos
  set V : ℝ := volume.real (rayFundamentalDomain 𝔪 ∩ {y | mixedEmbedding.norm y ≤ 1}) /
    ZLattice.covolume (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞')) volume
  refine IsBigO.of_bound (A * N ^ (1 - (finrank ℚ K : ℝ)⁻¹) / w) ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have ht : 1 ≤ x * N := one_le_mul_of_one_le_of_one_le hx hN
  have hcount := hA (mixedEmbedding K (ξ : K)) (x * N) ht
  have hset : Nat.card {a : rayIdealSet 𝔪 𝔞' // mixedEmbedding.norm (a : mixedSpace K) ≤ x * N} =
      ((rayFundamentalDomain 𝔪 ∩ {y | mixedEmbedding.norm y ≤ x * N}) ∩
        (mixedEmbedding K (ξ : K) +ᵥ
          (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞') : Set (mixedSpace K)))).ncard := by
    rw [← Nat.card_coe_set_eq, Set.inter_right_comm,
      ← rayIdealSet_eq_inter_vadd 𝔪 𝔞' hξ𝔞 hξ𝔪]
    exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ rayIdealSet 𝔪 𝔞')
      (mixedEmbedding.norm · ≤ x * N))
  have hc := congrArg (Nat.cast : ℕ → ℝ) <|
    (congrArg (· * Nat.card (unitsCongruenceTorsion 𝔪))
      (rayClassIdealCountingFunction_eq_card_dvd_and_idealClass_eq_one 𝔪 𝔞 h𝔞 x)).trans <|
    (card_idealClass_eq_one_dvd_norm_le 𝔪 𝔞 (x * N)).trans hset
  push_cast at hc
  have key : (rayClassIdealCountingFunction 𝔪 c x : ℝ) - rayClassIdealMainTerm 𝔪 * x =
      (((rayFundamentalDomain 𝔪 ∩ {y | mixedEmbedding.norm y ≤ x * N}) ∩
        (mixedEmbedding K (ξ : K) +ᵥ
          (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞') : Set (mixedSpace K)))).ncard -
        V * (x * N)) / w :=
    (eq_div_iff hw.ne').mpr (by linear_combination hc + x * hcoef)
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  rw [key, norm_div, Real.norm_of_nonneg hw.le, Real.norm_of_nonneg (Real.rpow_nonneg hx0 _),
    Real.norm_eq_abs]
  calc _ ≤ A * (x * N) ^ (1 - (finrank ℚ K : ℝ)⁻¹) / w := div_le_div_of_nonneg_right hcount hw.le
    _ = _ := by rw [Real.mul_rpow hx0 (zero_le_one.trans hN)]; ring

end TauCeti.GlobalNumberFields
