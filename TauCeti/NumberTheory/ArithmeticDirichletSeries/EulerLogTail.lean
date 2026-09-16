/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.DirichletDensity

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.ZetaValues
import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree

/-!
# The higher prime powers in the logarithm of the Dedekind Euler product

Taking logarithms in the Euler product `ζ_K(s) = ∏_𝔭 (1 - N(𝔭) ^ (-s))⁻¹` turns it into the
double sum `∑_𝔭 ∑_{m ≥ 1} N(𝔭) ^ (-m s) / m`, whose `m = 1` part is the prime Dirichlet series
`NumberField.Set.primeIdealZetaSum Set.univ s`.  This file bounds everything else: the `m ≥ 2`
part, equivalently the difference `∑_𝔭 (-log (1 - N(𝔭) ^ (-s)) - N(𝔭) ^ (-s))`, is nonnegative
and at most `2 [K : ℚ]`.

The bound is uniform on all of `s ≥ 1`, endpoint included, and that endpoint is the whole point:
at `s = 1` the Euler-factor logarithm sum and the prime Dirichlet series each diverge, while
their termwise difference still converges, because discarding the linear term of
`-log (1 - x)` replaces the exponent `-s` by the exponent `-2 s`, and `2 s ≥ 2` already
converges.

Two elementary inputs carry the argument.

* A height-one prime `𝔭` has `N(𝔭) ≥ 2`, so `N(𝔭) ^ (-s) ≤ 1 / 2` for `s ≥ 1` and the
  denominator `1 - N(𝔭) ^ (-s)` is bounded below by `1 / 2`; the termwise difference is
  therefore at most `N(𝔭) ^ (-2)`.
* `N(𝔭)` is at least the rational prime below `𝔭` and at most `[K : ℚ]` primes lie over one
  rational prime, so `∑_𝔭 N(𝔭) ^ (-2) ≤ [K : ℚ] ∑_m m ^ (-2) ≤ 2 [K : ℚ]`; the fibring step is
  the already available `TauCeti.sum_comp_rationalPrimeBelow_le`.

## Main results

* `TauCeti.summable_neg_log_one_sub_sub_absNorm_rpow`: the termwise difference between the
  Euler-factor logarithm and the prime Dirichlet term is summable for every `s ≥ 1`.
* `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg`: that sum is nonnegative for every
  `s > 0`, the whole range on which the termwise difference is defined and nonnegative.
* `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_le`: it is at most `2 [K : ℚ]` for every
  `s ≥ 1`; together the two bound the sum in `[0, 2 [K : ℚ]]` on `s ≥ 1`.
* `NumberField.Set.abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le`: for `s > 1`, where the
  two sums converge separately, the sum of the Euler-factor logarithms differs from
  `NumberField.Set.primeIdealZetaSum Set.univ s` by at most `2 [K : ℚ]`.

## Implementation notes

The constant is explicit rather than existentially quantified, and the upper bound's hypothesis
is the closed condition `1 ≤ s` rather than a neighbourhood of `1`: both are free here, and a
consumer that wants an eventual statement near `s = 1` gets it by weakening, whereas the
converse costs work.

The two halves carry different hypotheses on purpose. Nonnegativity holds as soon as
`N(𝔭) ^ (-s) < 1`, so it is stated on `0 < s`; the upper bound needs `N(𝔭) ^ (-s) ≤ 1 / 2` to
control the denominator, and is false for `s` near `1 / 2`, where the tail already diverges.

The one-variable estimate behind the termwise bound is not proved again: it is Mathlib's
`Complex.norm_log_one_sub_inv_sub_self_le` read along the reals, which is where the factor `2`
in the denominator below comes from.

Convergence of `∑_𝔭 N(𝔭) ^ (-s)` over all height-one primes for `1 < s` is proved here as a
private helper.  It is not part of the interface of this file, which is about the difference of
the two sums and not about either of them separately.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §3.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti

-- Source: Layer 7.2 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.

variable {K : Type*} [Field K] [NumberField K]

/-! ### The prime zeta sum at exponent two -/

-- `∑' m : ℕ, m ^ (-2)` is `ζ (2) = π ^ 2 / 6`, and `π ^ 2 < 12`.
private theorem tsum_nat_rpow_neg_two_le_two : ∑' m : ℕ, (m : ℝ) ^ (-(2 : ℝ)) ≤ 2 := by
  have hfun : (fun m : ℕ ↦ (m : ℝ) ^ (-(2 : ℝ))) = fun m : ℕ ↦ (1 : ℝ) / (m : ℝ) ^ 2 := by
    funext m
    rw [Real.rpow_neg (Nat.cast_nonneg m), Real.rpow_two, one_div]
  rw [hfun, hasSum_zeta_two.tsum_eq]
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

-- The norm is `p ^ f` with `f ≥ 1`, for `p` the rational prime below.
private theorem rationalPrimeBelow_le_absNorm (𝔭 : HeightOneSpectrum (𝓞 K)) :
    rationalPrimeBelow 𝔭 ≤ Ideal.absNorm 𝔭.asIdeal := by
  have := 𝔭.isPrime
  rw [absNorm_eq_rationalPrimeBelow_pow 𝔭]
  exact Nat.le_self_pow (Ideal.inertiaDeg_pos 𝔭.asIdeal ℤ).ne' _

-- Fibre a finite sum over the rational primes below, exactly as
-- `sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum` does, but with the exponent
-- unchanged: without a residue-degree hypothesis only `p ≤ N(𝔭)` is available.
private theorem sum_absNorm_rpow_le_finrank_mul_tsum {s : ℝ} (hs : 1 < s)
    (F : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ 𝔭 ∈ F, (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
      Module.finrank ℚ K * ∑' m : ℕ, (m : ℝ) ^ (-s) := by
  classical
  have hterm : ∀ 𝔭 ∈ F, (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
      ((rationalPrimeBelow 𝔭 : ℝ)) ^ (-s) := fun 𝔭 _ ↦
    Real.rpow_le_rpow_of_nonpos (mod_cast (prime_rationalPrimeBelow 𝔭).pos)
      (mod_cast rationalPrimeBelow_le_absNorm 𝔭) (by linarith)
  refine (Finset.sum_le_sum hterm).trans ?_
  refine (sum_comp_rationalPrimeBelow_le (g := fun m ↦ (m : ℝ) ^ (-s))
    (fun m _ ↦ Real.rpow_nonneg (Nat.cast_nonneg m) _) (T := F.image rationalPrimeBelow)
    (fun 𝔭 h𝔭 ↦ Finset.mem_image_of_mem rationalPrimeBelow h𝔭)).trans ?_
  exact mul_le_mul_of_nonneg_left (Summable.sum_le_tsum _
    (fun m _ ↦ Real.rpow_nonneg (Nat.cast_nonneg m) _)
    (Real.summable_nat_rpow.mpr (by linarith))) (Nat.cast_nonneg _)

private theorem summable_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
  summable_of_sum_le (fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    fun F ↦ sum_absNorm_rpow_le_finrank_mul_tsum hs F

private theorem tsum_absNorm_rpow_neg_two_le :
    ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 : ℝ)) ≤
      2 * Module.finrank ℚ K := by
  refine Real.tsum_le_of_sum_le (fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _) fun F ↦ ?_
  refine (sum_absNorm_rpow_le_finrank_mul_tsum one_lt_two F).trans ?_
  rw [mul_comm (2 : ℝ) (Module.finrank ℚ K : ℝ)]
  exact mul_le_mul_of_nonneg_left tsum_nat_rpow_neg_two_le_two (Nat.cast_nonneg _)

/-! ### The termwise bound -/

-- `log t ≤ t - 1` at `t = 1 - x`.  Unlike the upper bound below this needs no sign condition on
-- `x`: it holds throughout `x < 1`.
private theorem neg_log_one_sub_sub_nonneg {x : ℝ} (hx1 : x < 1) :
    0 ≤ -Real.log (1 - x) - x := by
  linarith [Real.log_le_sub_one_of_pos (sub_pos.mpr hx1)]

-- Mathlib's `Complex.norm_log_one_sub_inv_sub_self_le` read along the reals, where
-- `log (1 - x)⁻¹ = -log (1 - x)`.  The real-variable `Real.abs_log_sub_add_sum_range_le` proves
-- the same shape with `1` in place of `2` in the denominator, which would double the constant in
-- `tsum_neg_log_one_sub_sub_absNorm_rpow_le`.
private theorem neg_log_one_sub_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) - x ≤ x ^ 2 / (2 * (1 - x)) := by
  have hz : ‖(x : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg hx0]
  have key := Complex.norm_log_one_sub_inv_sub_self_le hz
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv,
    ← Complex.ofReal_log (by positivity), ← Complex.ofReal_sub, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hx0, Real.log_inv] at key
  exact ((Real.le_norm_self _).trans key).trans_eq (by field_simp)

-- At `x = y ^ (-s)` with `2 ≤ y` and `1 ≤ s`, the base is at least `2` and the exponent at most
-- `-1`, so `x ≤ 1 / 2`.  Only the upper bound below needs this; nonnegativity needs just `x < 1`.
private theorem rpow_neg_le_half {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) : y ^ (-s) ≤ 1 / 2 :=
  calc y ^ (-s) ≤ (2 : ℝ) ^ (-s) := Real.rpow_le_rpow_of_nonpos two_pos hy (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    _ = 1 / 2 := by norm_num

-- Nonnegativity needs only `y ^ (-s) ∈ [0, 1)`, so `0 < s` suffices here; the upper bound below
-- is the half that genuinely needs `1 ≤ s`.
private theorem neg_log_one_sub_rpow_sub_nonneg {y s : ℝ} (hy : 2 ≤ y) (hs : 0 < s) :
    0 ≤ -Real.log (1 - y ^ (-s)) - y ^ (-s) :=
  neg_log_one_sub_sub_nonneg (Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith))

-- For `2 ≤ y` and `1 ≤ s` the ratio `x ^ 2 / (2 (1 - x))` at `x = y ^ (-s)` is at most `x ^ 2`,
-- because `x ≤ 1 / 2`, and `x ^ 2 = y ^ (-2 s) ≤ y ^ (-2)`.
private theorem neg_log_one_sub_rpow_sub_le {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) :
    -Real.log (1 - y ^ (-s)) - y ^ (-s) ≤ y ^ (-(2 : ℝ)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hx0 : 0 ≤ y ^ (-s) := Real.rpow_nonneg hy0.le _
  have hxhalf : y ^ (-s) ≤ 1 / 2 := rpow_neg_le_half hy hs
  have hhigh := neg_log_one_sub_sub_le hx0 (by linarith)
  have hsq : (y ^ (-s)) ^ 2 ≤ y ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast (y ^ (-s)) 2, ← Real.rpow_mul hy0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  refine hhigh.trans ((div_le_iff₀ (by linarith)).mpr ?_)
  nlinarith [sq_nonneg (y ^ (-s))]

/-! ### The prime-power tail -/

/-- **The prime-power tail is summable.** The termwise difference between the Euler-factor
logarithm `-log (1 - N(𝔭) ^ (-s))` and the prime Dirichlet term `N(𝔭) ^ (-s)` is summable for
every `s ≥ 1`, endpoint included — unlike either of the two families it is built from, which is
summable only for `s > 1`. -/
theorem summable_neg_log_one_sub_sub_absNorm_rpow {s : ℝ} (hs : 1 ≤ s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
  (summable_absNorm_rpow one_lt_two).of_nonneg_of_le
    (fun 𝔓 ↦ neg_log_one_sub_rpow_sub_nonneg (two_le_absNorm_asIdeal_real 𝔓)
      (zero_lt_one.trans_le hs))
    (fun 𝔭 ↦ neg_log_one_sub_rpow_sub_le (two_le_absNorm_asIdeal_real 𝔭) hs)

/-- **The prime-power tail is nonnegative.** The termwise difference between the Euler-factor
logarithm `-log (1 - N(𝔭) ^ (-s))` and the prime Dirichlet term `N(𝔭) ^ (-s)` sums to a nonnegative
number for every `s > 0`. -/
theorem tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg {s : ℝ} (hs : 0 < s) :
    0 ≤ ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) :=
  tsum_nonneg fun 𝔭 ↦ neg_log_one_sub_rpow_sub_nonneg (two_le_absNorm_asIdeal_real 𝔭) hs

/-- **The prime-power tail is bounded uniformly on `s ≥ 1`.** The constant `2 [K : ℚ]` does not
depend on `s`, so this survives the passage to the limit `s → 1⁺` that the Dirichlet-density
normalization needs. -/
theorem tsum_neg_log_one_sub_sub_absNorm_rpow_le {s : ℝ} (hs : 1 ≤ s) :
    ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ≤ 2 * Module.finrank ℚ K :=
  ((summable_neg_log_one_sub_sub_absNorm_rpow hs).tsum_le_tsum
    (fun 𝔭 ↦ neg_log_one_sub_rpow_sub_le (two_le_absNorm_asIdeal_real 𝔭) hs)
    (summable_absNorm_rpow one_lt_two)).trans tsum_absNorm_rpow_neg_two_le

end TauCeti

namespace NumberField.Set

variable {K : Type*} [Field K] [NumberField K]

/-- **The Euler-factor logarithms sum to the prime Dirichlet series up to `O(1)`.** For `s > 1`,
where both series converge, `∑_𝔭 -log (1 - N(𝔭) ^ (-s))` differs from
`NumberField.Set.primeIdealZetaSum Set.univ s` by at most the constant `2 [K : ℚ]`.

The absolute value is here so that the statement can be used directly as an `O(1)` estimate; the
difference is in fact nonnegative — see `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg`. -/
theorem abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le {s : ℝ} (hs : 1 < s) :
    |(∑' 𝔭 : HeightOneSpectrum (𝓞 K), -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))) -
      primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s| ≤ 2 * Module.finrank ℚ K := by
  have hsumP := TauCeti.summable_absNorm_rpow (K := K) hs
  have hsumL : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
    simpa using (TauCeti.summable_neg_log_one_sub_sub_absNorm_rpow hs.le).add hsumP
  -- Both series converge separately, so their difference is the sum of the prime-power tail.
  rw [primeIdealZetaSum_def, tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s), ← hsumL.tsum_sub hsumP,
    abs_of_nonneg (TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg (zero_lt_one.trans hs))]
  exact TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_le hs.le

end NumberField.Set
