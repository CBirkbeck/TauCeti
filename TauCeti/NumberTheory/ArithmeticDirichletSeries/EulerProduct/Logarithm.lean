/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.EulerProduct.ExpLog

/-!
# The Euler product over the primes of a number field, in exponential form

Mathlib's `EulerProduct.exp_tsum_primes_log_eq_tsum` writes the Euler product of a completely
multiplicative `f : ℕ →*₀ ℂ` as `exp (∑' p, -log (1 - f p))`. This file is the ideal-indexed
analogue, over the height-one primes of the ring of integers of a number field, mirroring the way
`TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor` mirrors Mathlib's product form.

The logarithm is taken factor by factor, using the principal value: absolute convergence of the
ideal-indexed series forces each local ratio into the open unit disc, where `Complex.log (1 - ·)`
is defined without choosing anything.

**What this does not give.** `exp` is not injective, so an identity of the form `exp t = L`
determines `t` only modulo `2πi ℤ`; these theorems therefore do not exhibit a logarithm *of* the
`L`-series, and in particular are not a holomorphic branch on a region. Obtaining one needs the
series to be nonvanishing there first, which
`TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic` states it does not supply.

## Main results

* `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`: the `L`-series as the
  exponential of a sum of principal logarithms over the primes.
* `TauCeti.MultiplicativeIdealWeight.exp_tsum_primePow_eq_LSeries`: the same sum re-indexed by a
  prime and an exponent.
-/

public section

namespace TauCeti

open Complex IsDedekindDomain

open scoped NumberField

namespace MultiplicativeIdealWeight

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- **The Euler product in exponential form.** For a completely multiplicative ideal weight whose
ideal-indexed series converges absolutely at `s`, the `L`-series is the exponential of the sum of
principal logarithms `-log (1 - χ(P) N(P)⁻ˢ)` over the height-one primes.

The sum is not thereby a logarithm of the `L`-series: `exp` identifies it only modulo `2πi ℤ`.
This is the number-field analogue of Mathlib's `EulerProduct.exp_tsum_primes_log_eq_tsum`, and
carries the same limitation. -/
theorem exp_tsum_neg_log_one_sub_eq_LSeries
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    exp (∑' P : HeightOneSpectrum (𝓞 K),
        -log (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)) =
      LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  have hne (P : HeightOneSpectrum (𝓞 K)) :
      1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s ≠ 0 := fun h ↦ by
    have hlt := χ.norm_div_lt_one_of_summable_idealTerm hs P
    rw [sub_eq_zero] at h
    rw [← h] at hlt
    simp at hlt
  have H := (Summable.clog_one_sub
    (χ.summable_div_of_summable_idealTerm hs)).neg.hasSum.cexp.tprod_eq
  simp only [Function.comp_apply, exp_neg, exp_log (hne _)] at H
  exact H.symm.trans (χ.hasProd_eulerFactor hs).tprod_eq

/-- **The prime-power family is summable.** Bounding `‖rᵉ⁺¹ / (e + 1)‖` by `‖r‖ᵉ⁺¹` reduces this
to a geometric sum in each fibre; summability of the ratios sends them to zero along the cofinite
filter, so all but finitely many are at most `1 / 2` and the fibre sums are then at most `2‖r‖`. -/
theorem summable_div_pow_div_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    Summable fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1) := by
  set r : HeightOneSpectrum (𝓞 K) → ℂ :=
    fun P ↦ χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s with hr_def
  have hr : Summable r := χ.summable_div_of_summable_idealTerm hs
  have h1 : ∀ P, ‖r P‖ < 1 := χ.norm_div_lt_one_of_summable_idealTerm hs
  have hhalf : ∀ᶠ P in Filter.cofinite, ‖r P‖ ≤ 1 / 2 :=
    hr.tendsto_cofinite_zero.norm.eventually_le_const (by norm_num)
  have hmaj : Summable fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦ ‖r pe.1‖ ^ (pe.2 + 1) := by
    have hfib : ∀ P, Summable fun e : ℕ ↦ ‖r P‖ ^ (e + 1) := fun P ↦
      ((summable_geometric_of_lt_one (norm_nonneg _) (h1 P)).mul_left ‖r P‖).congr fun e ↦ by ring
    have hval : ∀ P, ∑' e : ℕ, ‖r P‖ ^ (e + 1) = ‖r P‖ / (1 - ‖r P‖) := fun P ↦ by
      rw [tsum_congr fun e ↦ pow_succ' ‖r P‖ e, tsum_mul_left,
        tsum_geometric_of_lt_one (norm_nonneg _) (h1 P), div_eq_mul_inv]
    have houter : Summable fun P ↦ ∑' e : ℕ, ‖r P‖ ^ (e + 1) := by
      refine Summable.of_norm_bounded_eventually (g := fun P ↦ 2 * ‖r P‖) (hr.norm.mul_left 2) ?_
      filter_upwards [hhalf] with P hP
      rw [Real.norm_of_nonneg (by positivity), hval P, div_le_iff₀ (by linarith [h1 P])]
      nlinarith [norm_nonneg (r P)]
    exact (summable_prod_of_nonneg fun pe ↦ pow_nonneg (norm_nonneg _) _).mpr ⟨hfib, houter⟩
  refine hmaj.of_norm_bounded ?_
  rintro ⟨P, e⟩
  rw [norm_div, norm_pow]
  refine div_le_self (by positivity) ?_
  have hcast : ((e : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_natCast]
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le e)

/-- **The Euler product expanded over prime powers.** Substituting the Taylor series of
`-log (1 - ·)` at each prime turns the logarithmic form into a sum indexed by a prime and an
exponent. The caveat above applies unchanged: this identifies the double sum only modulo
`2πi ℤ`, so it is a re-indexing of the exponential form and not the logarithm Layer 3.4 asks for. -/
theorem exp_tsum_primePow_eq_LSeries
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    exp (∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1)) =
      LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  have hfib : ∀ P : HeightOneSpectrum (𝓞 K),
      HasSum (fun e : ℕ ↦
          (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ (e + 1) / ((e : ℂ) + 1))
        (-log (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)) :=
    fun P ↦ hasSum_taylorSeries_neg_log' (χ.norm_div_lt_one_of_summable_idealTerm hs P)
  have hdouble := (χ.summable_div_pow_div_of_summable_idealTerm hs).hasSum.prod_fiberwise hfib
  rw [← χ.exp_tsum_neg_log_one_sub_eq_LSeries hs, ← hdouble.tsum_eq]

end MultiplicativeIdealWeight

end TauCeti
