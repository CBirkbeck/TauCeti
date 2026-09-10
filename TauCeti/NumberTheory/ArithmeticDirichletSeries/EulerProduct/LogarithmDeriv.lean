/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Deriv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm
public import TauCeti.Topology.Algebra.InfiniteSum.Real

import Mathlib.Analysis.Calculus.SmoothSeries
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup

/-!
# The derivative of the prime-power logarithmic expansion

`TauCeti.MultiplicativeIdealWeight.tsum_prime_pow_eq_tsum_neg_log_one_sub` expands the sum of local
logarithms over the prime powers `(P, e)`.  This file differentiates that expansion in `s`, term by
term, on the open half-plane where the ideal-indexed series converges absolutely.

Each term `(χ(P) N(P)⁻ˢ) ^ (e+1) / (e+1)` differentiates to `-log N(P) * (χ(P) N(P)⁻ˢ) ^ (e+1)`, so
the differentiated family is the undivided one weighted by `-log N(P)`.  Termwise differentiation of
a sum needs a summable majorant valid across a neighbourhood rather than at the single point, and
the half-plane supplies it: strictly to the right of a point of absolute convergence the weight
`log N(P)` is absorbed, which is `summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`, and the
exponent direction is geometric, which is `TauCeti.summable_mul_norm_pow_succ`.

`EulerProduct/Branch.lean` identifies the derivative of a *branch* of the logarithm with the
logarithmic derivative of the `L`-series.  That is an abstract identification; this file gives the
prime-power series the derivative is equal to.

## Main results

* `TauCeti.MultiplicativeIdealWeight.hasDerivAt_tsum_primePow`: the prime-power expansion
  differentiates termwise on the half-plane of absolute convergence.
-/

public section

namespace TauCeti

open Complex IsDedekindDomain

open scoped nonZeroDivisors NumberField

namespace MultiplicativeIdealWeight

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)

/-- **The Taylor term at `(P, e)` differentiates to `-log N(P)` times the undivided power.**  The
division by `e + 1` is what makes the derivative the plain power rather than a multiple of it. -/
theorem hasDerivAt_primePowTaylorTerm (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) (s : ℂ) :
    HasDerivAt (fun z : ℂ ↦ (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ z) ^ (e + 1)
        / ((e : ℂ) + 1))
      (-(Complex.log (Ideal.absNorm P.asIdeal : ℂ)
        * (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ (e + 1))) s := by
  have hne : ((e : ℂ) + 1) ≠ 0 := by
    have : ((e : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast Nat.succ_ne_zero e
  have hterm : ∀ z : ℂ, (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ z) ^ (e + 1)
      = idealTerm K χ.toIdealArithmeticFunction z (P.primeIdealPow (e + 1)) := fun z ↦
    (idealTerm_toIdealArithmeticFunction_primeIdealPow χ P (e + 1) z).symm
  have hlog : Complex.log ((Ideal.absNorm ((P.primeIdealPow (e + 1) : (Ideal (𝓞 K))⁰) :
        Ideal (𝓞 K))) : ℂ)
      = ((e : ℂ) + 1) * Complex.log (Ideal.absNorm P.asIdeal : ℂ) := by
    rw [P.absNorm_primeIdealPow, ← Complex.natCast_log, ← Complex.natCast_log]
    push_cast [Real.log_pow]
    ring
  have hval : -(Complex.log (Ideal.absNorm P.asIdeal : ℂ)
        * idealTerm K χ.toIdealArithmeticFunction s (P.primeIdealPow (e + 1)))
      = -(Complex.log ((Ideal.absNorm ((P.primeIdealPow (e + 1) : (Ideal (𝓞 K))⁰) :
            Ideal (𝓞 K))) : ℂ)
          * idealTerm K χ.toIdealArithmeticFunction s (P.primeIdealPow (e + 1)))
        / ((e : ℂ) + 1) := by
    rw [hlog]
    field_simp
  simp_rw [hterm]
  rw [hval]
  exact (hasDerivAt_idealTerm K χ.toIdealArithmeticFunction
    (P.primeIdealPow (e + 1)) s).div_const ((e : ℂ) + 1)

/-- **The differentiated term is dominated by its value at the edge of the half-plane.**  The bound
is uniform in `z` across `σ₀ ≤ z.re`, which is what termwise differentiation of a sum requires. -/
theorem norm_log_mul_primePow_le (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) {σ₀ : ℝ} {z : ℂ}
    (hz : σ₀ ≤ z.re) :
    ‖-(Complex.log (Ideal.absNorm P.asIdeal : ℂ)
        * (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ z) ^ (e + 1))‖
      ≤ Real.log (Ideal.absNorm P.asIdeal)
          * ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (σ₀ : ℂ)‖ ^ (e + 1) := by
  have hlogpos : 0 ≤ Real.log (Ideal.absNorm P.asIdeal : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm P).le)
  have hlog : ‖Complex.log (Ideal.absNorm P.asIdeal : ℂ)‖
      = Real.log (Ideal.absNorm P.asIdeal) := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_of_nonneg hlogpos]
  have hmono : ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ z‖
      ≤ ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (σ₀ : ℂ)‖ := by
    have := norm_idealTerm_le_of_re_le_re K χ.toIdealArithmeticFunction
      (s := (σ₀ : ℂ)) (s' := z) (by simpa using hz) (P.primeIdealPow 1)
    simpa [idealTerm_toIdealArithmeticFunction_primeIdealPow] using this
  rw [norm_neg, norm_mul, norm_pow, hlog]
  gcongr

/-- **The log-weighted majorant is summable over primes and exponents together.**  Strictly to the
right of a point of absolute convergence the weight `log N(P)` is absorbed, and the exponent
direction is geometric. -/
theorem summable_log_absNorm_mul_norm_primePow {s s' : ℂ} (h : s.re < s'.re)
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s))
    (hs' : Summable (idealTerm K χ.toIdealArithmeticFunction s')) :
    Summable fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      Real.log (Ideal.absNorm pe.1.asIdeal)
        * ‖χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s'‖ ^ (pe.2 + 1) := by
  have hwr : Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      Real.log (Ideal.absNorm P.asIdeal)
        * ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s'‖ := by
    refine ((summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re K h hs).comp_injective
      HeightOneSpectrum.primeIdealPow_one_injective).congr fun P ↦ ?_
    have hP : 0 < Ideal.absNorm P.asIdeal := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm P
      omega
    simp only [Function.comp_apply, norm_idealTerm, HeightOneSpectrum.coe_primeIdealPow, pow_one,
      toIdealArithmeticFunction_apply, norm_div, Complex.norm_natCast_cpow_of_pos hP]
  have hhalf : ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s'‖ ≤ 1 / 2 :=
    (χ.summable_div_of_summable_idealTerm hs').tendsto_cofinite_zero.norm.eventually_le_const
      (by norm_num)
  refine summable_mul_norm_pow_succ ?_ hwr ?_
  · exact ⟨1 / 2, by norm_num, by filter_upwards [hhalf] with P hP _; linarith⟩
  · exact fun P _ ↦ χ.norm_div_lt_one_of_summable_idealTerm hs' P

/-- **The prime-power expansion differentiates termwise.**  On the open half-plane `σ₁ < re z`,
where the ideal-indexed series converges absolutely at every point, the sum over prime powers is
differentiable and its derivative is the termwise one: the same family weighted by `-log N(P)`,
with the division by `e + 1` gone. -/
theorem hasDerivAt_tsum_primePow {σ₁ : ℝ}
    (habs : ∀ z : ℂ, σ₁ < z.re → Summable (idealTerm K χ.toIdealArithmeticFunction z))
    {s : ℂ} (hs : σ₁ < s.re) :
    HasDerivAt (fun z : ℂ ↦ ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1))
      (∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        -(Complex.log (Ideal.absNorm pe.1.asIdeal : ℂ)
          * (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1))) s := by
  obtain ⟨σ₀, hσ₁₀, hσ₀s⟩ := exists_between hs
  obtain ⟨σ₂, hσ₁₂, hσ₂₀⟩ := exists_between hσ₁₀
  have hu : Summable fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      Real.log (Ideal.absNorm pe.1.asIdeal)
        * ‖χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ (σ₀ : ℂ)‖ ^ (pe.2 + 1) :=
    χ.summable_log_absNorm_mul_norm_primePow
      (s := (σ₂ : ℂ)) (s' := (σ₀ : ℂ)) (by simpa using hσ₂₀)
      (habs (σ₂ : ℂ) (by simpa using hσ₁₂)) (habs (σ₀ : ℂ) (by simpa using hσ₁₀))
  have hmem : σ₁ < ((σ₀ + 1 : ℝ) : ℂ).re := by simp; linarith
  have hy₀ := Complex.summable_taylorSeries_neg_log
    (r := fun P : HeightOneSpectrum (𝓞 K) ↦
      χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ₀ + 1 : ℝ) : ℂ))
    (χ.summable_div_of_summable_idealTerm (habs _ hmem))
    (χ.norm_div_lt_one_of_summable_idealTerm (habs _ hmem))
  exact hasDerivAt_tsum_of_isPreconnected
    (u := fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      Real.log (Ideal.absNorm pe.1.asIdeal)
        * ‖χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ (σ₀ : ℂ)‖ ^ (pe.2 + 1))
    (g := fun (pe : HeightOneSpectrum (𝓞 K) × ℕ) (z : ℂ) ↦
      (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1))
    (g' := fun (pe : HeightOneSpectrum (𝓞 K) × ℕ) (z : ℂ) ↦
      -(Complex.log (Ideal.absNorm pe.1.asIdeal : ℂ)
        * (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1)))
    (t := {z : ℂ | σ₀ < z.re}) (y₀ := ((σ₀ + 1 : ℝ) : ℂ))
    hu (isOpen_lt continuous_const continuous_re)
    (convex_halfSpace_re_gt σ₀).isPreconnected
    (fun pe z _ ↦ χ.hasDerivAt_primePowTaylorTerm pe.1 pe.2 z)
    (fun pe z hz ↦ χ.norm_log_mul_primePow_le pe.1 pe.2 (le_of_lt hz))
    (by simp) hy₀ hσ₀s

end MultiplicativeIdealWeight

end TauCeti
