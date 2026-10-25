/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.Strassmann
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AnalyticSubst
public import TauCeti.NumberTheory.Padics.RingHoms
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Evaluation and translation checks for restricted power series

These are the three checks in TauCetiRoadmap/RestrictedPowerSeries/README.md, §2.4.
Translation by 1 is an automorphism even though its constant term is nonzero. The polynomial
`X ^ p - X` has Gauss norm 1 over Q_p, but all its values on Z_p have norm at most `p⁻¹`.
Over the trivially valued field F_p, the same nonzero polynomial vanishes at every point.
-/

public section

open Polynomial

namespace TauCeti.Examples.RestrictedPowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

/-- The Gauss norm of `X ^ p - X` over Q_p is 1. -/
theorem gaussNorm_X_pow_sub_X :
    ((X ^ p - X : (ℚ_[p])[X]) : PowerSeries ℚ_[p]).gaussNorm norm 1 = 1 := by
  have hn : p ≠ 1 := hp.out.ne_one
  have h := TauCeti.PowerSeries.gaussNorm_eq_of_forall_le
    (a := ((X ^ p - X : (ℚ_[p])[X]) : PowerSeries ℚ_[p]))
    (c := 1) (v := norm) (s := p) (fun m => by
      by_cases hm : m = p
      · subst m; exact le_rfl
      · by_cases hm1 : m = 1
        · subst m; simp [PowerSeries.coeff_X, hn, Ne.symm hn]
        · simp [PowerSeries.coeff_X, hm, hm1, hn])
  simpa [PowerSeries.coeff_X, hn] using h

/-- Every value of `X ^ p - X` on Z_p lies in its maximal ideal. -/
theorem norm_pow_sub_le (x : ℤ_[p]) : ‖x ^ p - x‖ ≤ (p : ℝ)⁻¹ := by
  have hm : x ^ p - x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
    simp [ZMod.pow_card]
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow (x ^ p - x) 1).mpr (by
    simpa [← PadicInt.maximalIdeal_eq_span_p] using hm)
  simpa using h

/-- The polynomial `X ^ p - X` over F_p is nonzero. -/
theorem X_pow_sub_X_ne_zero : (X ^ p - X : (ZMod p)[X]) ≠ 0 :=
  Polynomial.X_pow_sub_X_ne_zero hp.out.one_lt

/-- The nonzero polynomial `X ^ p - X` over F_p vanishes at every point. -/
theorem eval_X_pow_sub_X (x : ZMod p) : (X ^ p - X : (ZMod p)[X]).eval x = 0 := by
  simp [ZMod.pow_card]

section Translation

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
local instance (i : Fin 1) : Fact (0 < (fun _ : Fin 1 => (1 : ℝ)) i) := ⟨zero_lt_one⟩

/-- Translation by 1 is an automorphism of the unit-radius Tate algebra in one variable. -/
noncomputable def translationOne :
    MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin 1 => (1 : ℝ)) ≃ₐ[K]
      MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin 1 => (1 : ℝ)) :=
  TauCeti.MvPowerSeries.restrictedTranslateEquiv (fun _ : Fin 1 => (1 : K))
    (fun _ => by simp)

/-- The automorphism `translationOne` sends the variable to `X + 1`. -/
theorem translationOne_X (i : Fin 1) :
    translationOne K ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ =
      ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ + 1 := by
  simp [translationOne]

end Translation
end TauCeti.Examples.RestrictedPowerSeries
