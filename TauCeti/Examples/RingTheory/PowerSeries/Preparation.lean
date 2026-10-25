/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
public import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Weierstrass preparation at boundary and non-value-group radii

The polynomial X−1 is its own
Weierstrass polynomial at radius 1, allowing a lower coefficient with norm 1. The same
calculation works at radius √2 over Q₂, and this radius is proved not to be the norm of any
Q₂ element. The degree-zero remainder check is already `IsMulDistinguished.weierstrassMod_eq_zero`.
-/

public section

open Polynomial TauCeti.PowerSeries

namespace TauCeti.Examples.Weierstrass

variable (K : Type*) [NormedCommRing K] [IsUltrametricDist K] [NormMulClass K] [NormOneClass K]

/-- At every radius at least 1, the Weierstrass polynomial of X−1 is X−1 itself. -/
theorem preparation_X_sub_one {c : ℝ} (hc : 1 ≤ c)
    (e : PowerSeries.IsRestricted.subring (R := K) c) (ω : K[X])
    (he : IsUnit e) (hω : ω.IsMonicOfDegree 1)
    (h : (e : PowerSeries K) * (ω : PowerSeries K) = PowerSeries.X - 1) :
    e = 1 ∧ ω = X - 1 := by
  have : Nontrivial K := NormOneClass.nontrivial
  have hnorm : ‖(1 : K)‖ ≤ c := by simpa using hc
  have hd : IsDistinguished c 1 (PowerSeries.X - (1 : PowerSeries K)) := by
    simpa using isDistinguished_X_sub_C (lt_of_lt_of_le zero_lt_one hc)
      hnorm
  exact hd.eq_and_eq_of_mul_eq_mul (lt_of_lt_of_le zero_lt_one hc) he isUnit_one
    hω (by simpa using isMonicOfDegree_X_sub_one (1 : K)) h (by simp)

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The positive radius √2 does not lie in the norm value group of Q₂. -/
theorem _root_.Padic.norm_ne_sqrt_two (x : ℚ_[2]) : ‖x‖ ≠ Real.sqrt 2 := by
  intro h
  have hnonneg : (0 : ℝ) ≤ 2 := by norm_num
  have h1 : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg 2]
  have h2 : Real.sqrt 2 < 2 := by norm_num
  have hgap : ‖x‖ ≤ 1 ↔ ‖x‖ < 2 := by
    simpa using Padic.norm_le_pow_iff_norm_lt_pow_add_one x 0
  have hx := hgap.mpr (h ▸ h2)
  rw [h] at hx
  exact h1.not_ge hx

/-- Preparation at a positive radius outside the Q₂ norm value group. -/
theorem preparation_sqrt_two :
    (∀ x : ℚ_[2], ‖x‖ ≠ Real.sqrt 2) ∧
    ∃! p : PowerSeries.IsRestricted.subring (R := ℚ_[2]) (Real.sqrt 2) × (ℚ_[2])[X],
      IsUnit p.1 ∧ p.2.IsMonicOfDegree 1 ∧
        (p.1 : PowerSeries ℚ_[2]) * (p.2 : PowerSeries ℚ_[2]) = PowerSeries.X - 1 := by
  refine ⟨Padic.norm_ne_sqrt_two, (1, X - 1), ⟨isUnit_one, ?_, by simp⟩, ?_⟩
  · simpa using isMonicOfDegree_X_sub_one (1 : ℚ_[2])
  · rintro ⟨e, ω⟩ ⟨he, hω, h⟩
    have hnonneg : (0 : ℝ) ≤ 2 := by norm_num
    have hc : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg 2]
    obtain ⟨he, hω⟩ := preparation_X_sub_one ℚ_[2] hc e ω he hω h
    exact Prod.ext he hω

end TauCeti.Examples.Weierstrass
