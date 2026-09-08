/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic

import Mathlib.NumberTheory.EulerProduct.ExpLog

/-!
# The logarithm of an Euler product over the primes of a number field

Mathlib's `EulerProduct.exp_tsum_primes_log_eq_tsum` writes the Euler product of a completely
multiplicative `f : ℕ →*₀ ℂ` as `exp (∑' p, -log (1 - f p))`. This file is the ideal-indexed
analogue, over the height-one primes of the ring of integers of a number field, mirroring the way
`TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor` mirrors Mathlib's product form.

The logarithm here is taken factor by factor, so no branch on a region is chosen and no zero-free
hypothesis is needed: absolute convergence of the ideal-indexed series already forces each local
ratio into the open unit disc, where `Complex.log (1 - ·)` is the principal value.

## Main results

* `TauCeti.MultiplicativeIdealWeight.summable_localRatio`: the local ratios `χ(P) N(P)⁻ˢ` are
  summable over the height-one primes.
* `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`: the logarithmic form of
  the Euler product.
-/

public section

namespace TauCeti

open Complex IsDedekindDomain

open scoped NumberField

namespace MultiplicativeIdealWeight

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- **The local ratios are summable over the primes.** Each prime contributes its ratio as the
`e = 1` term of the geometric subseries along its own powers, and distinct primes give distinct
ideals, so this is a subseries of the ideal-indexed one. -/
theorem summable_localRatio (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s := by
  have hinj : Function.Injective fun P : HeightOneSpectrum (𝓞 K) ↦ P.primeIdealPow 1 := by
    intro P Q h
    have hpow : P.asIdeal ^ 1 = Q.asIdeal ^ 1 := by
      simpa only [HeightOneSpectrum.coe_primeIdealPow] using congrArg Subtype.val h
    exact HeightOneSpectrum.ext (by simpa using hpow)
  refine (hs.comp_injective hinj).congr fun P ↦ ?_
  simp [idealTerm_toIdealArithmeticFunction_primeIdealPow χ P 1 s]

/-- **The Euler product in logarithmic form.** For a completely multiplicative ideal weight whose
ideal-indexed series converges absolutely at `s`, the `L`-series is the exponential of the sum of
`-log (1 - χ(P) N(P)⁻ˢ)` over the height-one primes.

This is the number-field analogue of Mathlib's `EulerProduct.exp_tsum_primes_log_eq_tsum`. -/
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
  have H := (Summable.clog_one_sub (χ.summable_localRatio hs)).neg.hasSum.cexp.tprod_eq
  simp only [Function.comp_apply, exp_neg, exp_log (hne _)] at H
  exact H.symm.trans (χ.hasProd_eulerFactor hs).tprod_eq

end MultiplicativeIdealWeight

end TauCeti
