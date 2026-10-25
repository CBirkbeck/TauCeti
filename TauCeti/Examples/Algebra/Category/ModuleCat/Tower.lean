/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.ProZero
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Boundary examples for the Mittag–Leffler criterion

The zero-transition tower over F_p is Mittag–Leffler with zero limit and first derived limit,
although none of its transitions is surjective. The inclusion tower pⁿZ_p is not Mittag–Leffler,
but also has zero first derived limit: summable p-adic tails solve its shift equation.
The nonzero first derived limit of the multiplication-by-p tower over Z is computed in
`TauCeti.Algebra.Category.ModuleCat.Tower.Padic`.
-/

public section

open CategoryTheory Opposite TauCeti
namespace TauCeti.Examples.ModuleTower

variable (p : ℕ) [hp : Fact p.Prime]

/-- The tower of ideals pⁿZ_p with their inclusion maps. -/
noncomputable abbrev padicIdealTower : ModuleTower ℤ_[p] where
  obj n := ModuleCat.of ℤ_[p] (Ideal.span {(p : ℤ_[p]) ^ n.unop})
  map f := ModuleCat.ofHom (Submodule.inclusion
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (leOfHom f.unop))))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The inclusion tower pⁿZ_p is not Mittag–Leffler: its images strictly decrease. -/
theorem not_isMittagLeffler_padicIdealTower : ¬(padicIdealTower p).IsMittagLeffler := by
  intro h
  obtain ⟨N, h0N, hN⟩ := ((padicIdealTower p).isMittagLeffler_iff_ranges.mp h) 0
  have he : (p : ℤ_[p]) ^ N ∈ Ideal.span {(p : ℤ_[p]) ^ N} := Ideal.subset_span (by simp)
  let e : (padicIdealTower p).obj (op N) := ⟨(p : ℤ_[p]) ^ N, he⟩
  have hm : (padicIdealTower p).transitionOfLE h0N e ∈
      LinearMap.range ((padicIdealTower p).transitionOfLE (h0N.trans N.le_succ)) := by
    rw [hN (N + 1) N.le_succ]
    exact LinearMap.mem_range_self _ e
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hm
  have heq : (b : ℤ_[p]) = (p : ℤ_[p]) ^ N := by
    simpa only [ModuleTower.transitionOfLE_def, ModuleCat.hom_ofHom,
      Submodule.coe_inclusion] using congrArg Subtype.val hb
  have hdiv : (p : ℤ_[p]) ^ (N + 1) ∣ (p : ℤ_[p]) ^ N := by
    rw [← heq]
    exact Ideal.mem_span_singleton.mp b.property
  obtain ⟨c, hc⟩ := hdiv
  have hpc : (p : ℤ_[p]) * c = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero N (Nat.cast_ne_zero.mpr hp.out.ne_zero))
    rw [mul_one, ← mul_assoc, ← pow_succ]
    exact hc.symm
  have hu : IsUnit (p : ℤ_[p]) := IsUnit.of_mul_eq_one c hpc
  exact (PadicInt.not_isUnit_iff.mpr
    ((PadicInt.norm_lt_one_iff_dvd _).mpr dvd_rfl)) hu

/-- Convergent p-adic tails solve the shift equation, so the inclusion tower has zero lim¹. -/
theorem subsingleton_limOne_padicIdealTower : Subsingleton (padicIdealTower p).limOne := by
  apply (padicIdealTower p).subsingleton_limOne_iff.mpr
  intro a
  have ha (n : ℕ) : (p : ℤ_[p]) ^ n ∣ (a n : ℤ_[p]) :=
    Ideal.mem_span_singleton.mp (a n).property
  choose c hc using ha
  let x (n : ℕ) : ℤ_[p] := ∑' k, (p : ℤ_[p]) ^ k * c (n + k)
  have hs (n : ℕ) : Summable fun k => (p : ℤ_[p]) ^ k * c (n + k) :=
    PadicInt.summable_pow_mul _
  have hx (n : ℕ) : x n = c n + (p : ℤ_[p]) * x (n + 1) := by
    dsimp only [x]
    rw [(hs n).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, Nat.add_zero]
    congr 1
    rw [← (hs (n + 1)).tsum_mul_left]
    apply tsum_congr
    intro k
    rw [pow_succ, show n + (k + 1) = n + 1 + k by omega]
    ring
  let b : (padicIdealTower p).Product := fun n =>
    ⟨(p : ℤ_[p]) ^ n * x n, Ideal.mem_span_singleton.mpr ⟨x n, rfl⟩⟩
  refine ⟨b, funext fun n => Subtype.ext ?_⟩
  rw [ModuleTower.shift_apply, ModuleTower.transition_def]
  change (p : ℤ_[p]) ^ n * x n - (p : ℤ_[p]) ^ (n + 1) * x (n + 1) = (a n : ℤ_[p])
  rw [hc n, hx n, pow_succ]
  ring

/-- Zero transitions over F_p give stable images and zero limits, without surjectivity. -/
theorem zero_transition_tower : (ModuleTower.multiplicationTower (0 : ZMod p)).IsMittagLeffler ∧
    (ModuleTower.multiplicationTower (0 : ZMod p)).shift = LinearMap.id ∧
    (ModuleTower.multiplicationTower (0 : ZMod p)).lim = ⊥ ∧
    Subsingleton (ModuleTower.multiplicationTower (0 : ZMod p)).limOne ∧
    ¬Function.Surjective ((ModuleTower.multiplicationTower (0 : ZMod p)).transition 0) := by
  have h : (ModuleTower.multiplicationTower (0 : ZMod p)).IsProZero :=
    (ModuleTower.isProZero_multiplicationTower_iff (0 : ZMod p)).mpr ⟨1, by simp⟩
  refine ⟨ModuleTower.isMittagLeffler_of_isProZero h, ?_,
    ModuleTower.lim_eq_bot_of_isProZero h, ModuleTower.subsingleton_limOne_of_isProZero h, ?_⟩
  · ext x n
    simp [ModuleTower.shift_apply, ModuleTower.multiplicationTower_transition]
    rfl
  · intro hs
    obtain ⟨x, hx⟩ := hs (1 : ZMod p)
    have hzero : (0 : ZMod p) = 1 := by
      rw [ModuleTower.multiplicationTower_transition] at hx
      change (show ZMod p from x) * (0 : ZMod p) = 1 at hx
      exact (mul_zero (show ZMod p from x)).symm.trans hx
    exact zero_ne_one hzero

end TauCeti.Examples.ModuleTower
