/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Weierstrass preparation at boundary and non-value-group radii

These examples supply the X−1 and non-value-group-radius checks from
TauCetiRoadmap/RestrictedPowerSeries/README.md, Layer 4. The polynomial X−1 is its own
Weierstrass polynomial at radius 1, allowing a lower coefficient with norm 1. The same
calculation works at radius √2 over Q₂, and this radius is proved not to be the norm of any
Q₂ element. The degree-zero remainder check is already `IsMulDistinguished.weierstrassMod_eq_zero`.
-/

public section

open Polynomial TauCeti.PowerSeries

namespace TauCeti.Examples.Weierstrass

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- At every radius at least 1, the Weierstrass polynomial of X−1 is X−1 itself. -/
theorem preparation_X_sub_one {c : ℝ} (hc : 1 ≤ c)
    (e : PowerSeries.IsRestricted.subring (R := K) c) (ω : K[X])
    (he : IsUnit e) (hω : ω.IsMonicOfDegree 1)
    (h : (e : PowerSeries K) * (ω : PowerSeries K) = PowerSeries.X - 1) :
    e = 1 ∧ ω = X - 1 := by
  have hd : IsDistinguished c 1 (PowerSeries.X - (1 : PowerSeries K)) := by
    simpa using isDistinguished_X_sub_C (lt_of_lt_of_le zero_lt_one hc)
      (show ‖(1 : K)‖ ≤ c by simpa using hc)
  exact hd.eq_and_eq_of_mul_eq_mul (lt_of_lt_of_le zero_lt_one hc) he isUnit_one
    hω (by simpa using isMonicOfDegree_X_sub_one (1 : K)) h (by simp)

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The positive radius √2 does not lie in the norm value group of Q₂. -/
theorem sqrt_two_ne_norm (x : ℚ_[2]) : ‖x‖ ≠ Real.sqrt 2 := by
  intro h
  have h1 : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h2 : Real.sqrt 2 < 2 := by norm_num
  have hx : x ≠ 0 := by
    intro hx
    simp only [hx, norm_zero] at h
    linarith
  rw [Padic.norm_eq_zpow_neg_valuation hx] at h
  norm_num only [Nat.cast_ofNat] at h
  by_cases hv : -(x.valuation) ≤ 0
  · have hn : (2 : ℝ) ^ (-x.valuation) ≤ 1 := by
      simpa using zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hv
    linarith
  · have hv : (1 : ℤ) ≤ -x.valuation := by omega
    have hn : 2 ≤ (2 : ℝ) ^ (-x.valuation) := by
      simpa using zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hv
    linarith

/-- Preparation at a positive radius outside the Q₂ norm value group. -/
theorem preparation_sqrt_two :
    (∀ x : ℚ_[2], ‖x‖ ≠ Real.sqrt 2) ∧
    ∃! p : PowerSeries.IsRestricted.subring (R := ℚ_[2]) (Real.sqrt 2) × (ℚ_[2])[X],
      IsUnit p.1 ∧ p.2.IsMonicOfDegree 1 ∧
        (p.1 : PowerSeries ℚ_[2]) * (p.2 : PowerSeries ℚ_[2]) = PowerSeries.X - 1 := by
  refine ⟨sqrt_two_ne_norm, (1, X - 1), ⟨isUnit_one, ?_, by simp⟩, ?_⟩
  · simpa using isMonicOfDegree_X_sub_one (1 : ℚ_[2])
  · rintro ⟨e, ω⟩ ⟨he, hω, h⟩
    have hc : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    obtain ⟨he, hω⟩ := preparation_X_sub_one ℚ_[2] hc e ω he hω h
    exact Prod.ext he hω

end TauCeti.Examples.Weierstrass
