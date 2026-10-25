/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AnalyticSubst
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.NumberTheory.Padics.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Padics.MahlerBasis

/-!
# Evaluation and translation checks for restricted power series

Translation by 1 is an automorphism even though its constant term is nonzero. The polynomial
`X ^ p - X` has Gauss norm 1 over Q_p, but all its values on Z_p have norm at most `p⁻¹`.
Over the trivially valued field F_p, the same nonzero polynomial vanishes at every point;
its nonvanishing is `Polynomial.X_pow_sub_X_ne_zero`.
The bound over Z_p is attained at p, giving the exact supremum and Mahler coefficient norms
of this function. The two norms differ from its monomial Gauss norm.
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

/-- The bound for `x ^ p - x` is attained at `x = p`. -/
theorem norm_prime_pow_sub : ‖(p : ℚ_[p]) ^ p - p‖ = (p : ℝ)⁻¹ := by
  have h : ‖(p : ℚ_[p]) ^ p‖ < ‖(p : ℚ_[p])‖ := by
    rw [norm_pow]
    exact pow_lt_self_of_lt_one₀ (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero))
      Padic.norm_p_lt_one hp.out.one_lt
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (by simpa only [norm_neg] using h.ne), norm_neg, max_eq_right h.le, Padic.norm_p]

/-- Evaluation of `X ^ p - X` on the p-adic integers as a continuous Q_p-valued function. -/
noncomputable def powSubFunction : C(ℤ_[p], ℚ_[p]) :=
  ⟨fun x => (x : ℚ_[p]) ^ p - x,
    (continuous_subtype_val.pow p).sub continuous_subtype_val⟩

/-- The function evaluates to the polynomial X^p - X on each p-adic integer. -/
@[simp]
theorem powSubFunction_apply (x : ℤ_[p]) :
    powSubFunction p x = (x : ℚ_[p]) ^ p - x := (rfl)

/-- The supremum norm of `x ^ p - x` on Z_p is exactly `p⁻¹`. -/
theorem norm_powSubFunction : ‖powSubFunction p‖ = (p : ℝ)⁻¹ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    simpa only [powSubFunction_apply, ← PadicInt.coe_pow,
      ← PadicInt.coe_sub, PadicInt.norm_coe] using norm_pow_sub_le p x
  · have h := (powSubFunction p).norm_coe_le_norm (p : ℤ_[p])
    rw [powSubFunction_apply] at h
    simpa only [PadicInt.coe_natCast, norm_prime_pow_sub] using h

/-- Mahler's isometry gives the same norm `p⁻¹` for the coefficient sequence. -/
theorem norm_mahler_powSubFunction :
    ‖PadicInt.mahlerEquiv ℚ_[p] (powSubFunction p)‖ = (p : ℝ)⁻¹ := by
  rw [LinearIsometryEquiv.norm_map, norm_powSubFunction]

-- The nonzero polynomial X^p - X over F_p vanishes at every point.
example : (X ^ p - X : (ZMod p)[X]) ≠ 0 ∧
    ∀ x : ZMod p, (X ^ p - X : (ZMod p)[X]).eval x = 0 := by
  exact ⟨Polynomial.X_pow_sub_X_ne_zero hp.out.one_lt, fun x => by simp [ZMod.pow_card]⟩

section Translation

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
local instance (i : Fin 1) : Fact (0 < (fun _ : Fin 1 => (1 : ℝ)) i) := ⟨zero_lt_one⟩

-- Translation by 1 is an automorphism despite its nonzero constant term.
example (i : Fin 1) :
    TauCeti.MvPowerSeries.restrictedTranslateEquiv
      (r := fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : K)) (fun _ => by simp)
      ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ =
        ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ + 1 := by
  simp

end Translation
end TauCeti.Examples.RestrictedPowerSeries
