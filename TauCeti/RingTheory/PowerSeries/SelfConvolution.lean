/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Self-convolution coefficients of a formal power series

`PowerSeries.coeff_mul` gives the coefficients of a product as a sum over `Finset.antidiagonal`.
For a recursion that reads off one coefficient from strictly earlier ones the equivalent sum over
`Finset.range` is what is wanted, so this file names the two shapes that occur, for a square and
for a cube, and records the translation.

Both are stated for an arbitrary coefficient function `f : ℕ → R` rather than for the
coefficients of a given series: the congruence lemmas compare two such functions, and the
truncation lemmas feed in a modified one.

The load-bearing facts are `PowerSeries.selfConvTwo_congr` and `PowerSeries.selfConvThree_congr`.
When `f 0 = 0` the convolution at index `n` depends only on the values of `f` strictly below `n`,
because the extreme terms of the sum each carry a factor `f 0`. That is what makes a recursion
defined through these convolutions well founded.

## Main definitions

* `PowerSeries.selfConvTwo`, `PowerSeries.selfConvThree`: the `Finset.range`-form convolution
  sums computing the coefficients of a square and of a cube.

## Main results

* `PowerSeries.selfConvTwo_def`, `PowerSeries.selfConvThree_def`: the defining formulas, as
  named lemmas. Rewrite with these rather than unfolding the definitions.
* `PowerSeries.coeff_pow_two`, `PowerSeries.coeff_pow_three`: those sums do compute the
  coefficients of `w ^ 2` and `w ^ 3`.
* `PowerSeries.selfConvTwo_congr`, `PowerSeries.selfConvThree_congr`: for a function vanishing at
  `0`, the convolution at `n` depends only on the values strictly below `n`.
* `PowerSeries.selfConvTwo_truncate`, `PowerSeries.selfConvTwo_truncate_sub_one`,
  `PowerSeries.selfConvThree_truncate`: truncating the function above the index in question
  leaves the convolution unchanged.

## Provenance

Adapted from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned
by `TauCetiRoadmap/EllipticCurves/README.md` at `dev/hasse-weil @ 513e83879e2f`),
`HasseWeil/FormalGroup.lean`, declarations `conv₂` and `conv₃` together with the coefficient
lemmas `coeff_formalW_sq` and `coeff_formalW_cube`.

Changes from the source. The source states its two convolution-coefficient lemmas only for its
`formalW`, although neither proof uses anything about that series; they are stated here for an
arbitrary series. The truncation lemmas likewise assumed `formalW`, and are stated here for any
`f` vanishing at `0`, as consequences of the sharper congruence lemmas. The source works
throughout over a `CommRing`; nothing here needs more than a `Semiring`.
-/

public section

open Finset

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- The `n`-th coefficient of the square of the series with coefficients `f`. -/
def selfConvTwo (f : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ range (n + 1), f i * f (n - i)

/-- The defining formula for `selfConvTwo`. -/
theorem selfConvTwo_def (f : ℕ → R) (n : ℕ) :
    selfConvTwo f n = ∑ i ∈ range (n + 1), f i * f (n - i) := (rfl)

/-- The `n`-th coefficient of the cube of the series with coefficients `f`. -/
def selfConvThree (f : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ range (n + 1), ∑ j ∈ range (n - i + 1), f i * f j * f (n - i - j)

/-- The defining formula for `selfConvThree`. -/
theorem selfConvThree_def (f : ℕ → R) (n : ℕ) :
    selfConvThree f n = ∑ i ∈ range (n + 1), ∑ j ∈ range (n - i + 1), f i * f j * f (n - i - j) :=
  (rfl)

/-- `selfConvTwo` computes the coefficients of a square. -/
theorem coeff_pow_two (w : PowerSeries R) (n : ℕ) :
    coeff n (w ^ 2) = selfConvTwo (fun k => coeff k w) n := by
  rw [sq, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (M := R) (fun i j => coeff i w * coeff j w) n]
  rfl

/-- `selfConvThree` computes the coefficients of a cube. -/
theorem coeff_pow_three (w : PowerSeries R) (n : ℕ) :
    coeff n (w ^ 3) = selfConvThree (fun k => coeff k w) n := by
  rw [pow_succ' w 2, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (M := R) (fun i j => coeff i w * coeff j (w ^ 2)) n]
  simp only [coeff_pow_two, selfConvThree, selfConvTwo, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

/-- `selfConvTwo f n` depends only on the values of `f` strictly below `n`, provided `f`
vanishes at `0`: the two extreme terms of the convolution each carry a factor `f 0`. -/
theorem selfConvTwo_congr {f g : ℕ → R} (hf : f 0 = 0) (hg : g 0 = 0) {n : ℕ}
    (h : ∀ m, m < n → f m = g m) : selfConvTwo f n = selfConvTwo g n := by
  simp only [selfConvTwo]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
  by_cases hi' : i < n
  · by_cases hk : n - i < n
    · rw [h i hi', h _ hk]
    · have : i = 0 := by omega
      subst this
      simp [hf, hg]
  · have : i = n := by omega
    subst this
    simp [hf, hg]

/-- The cube analogue of `selfConvTwo_congr`. -/
theorem selfConvThree_congr {f g : ℕ → R} (hf : f 0 = 0) (hg : g 0 = 0) {n : ℕ}
    (h : ∀ m, m < n → f m = g m) : selfConvThree f n = selfConvThree g n := by
  simp only [selfConvThree]
  refine Finset.sum_congr rfl fun i hi => ?_
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi hj
  by_cases hi' : i < n
  · by_cases hj' : j < n
    · by_cases hk : n - i - j < n
      · rw [h i hi', h j hj', h _ hk]
      · have : i = 0 := by omega
        subst this
        simp [hf, hg]
    · have : i = 0 := by omega
      subst this
      simp [hf, hg]
  · have : i = n := by omega
    subst this
    simp [hf, hg]

/-- Truncating `f` above `n` does not change `selfConvTwo f n`, when `f 0 = 0`. -/
theorem selfConvTwo_truncate (f : ℕ → R) (hf : f 0 = 0) (n : ℕ) :
    selfConvTwo (fun m => if m < n then f m else 0) n = selfConvTwo f n :=
  selfConvTwo_congr (by by_cases h : 0 < n <;> simp [h, hf]) hf fun m hm => by simp [hm]

/-- The shifted form of `selfConvTwo_truncate` needed at index `n - 1`. -/
theorem selfConvTwo_truncate_sub_one (f : ℕ → R) (n : ℕ) (hn : 1 ≤ n) :
    selfConvTwo (fun m => if m < n then f m else 0) (n - 1) = selfConvTwo f (n - 1) := by
  simp only [selfConvTwo]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have h1 : i < n := by omega
  have h2 : n - 1 - i < n := by omega
  simp [h1, h2]

/-- Truncating `f` above `n` does not change `selfConvThree f n`, when `f 0 = 0`. -/
theorem selfConvThree_truncate (f : ℕ → R) (hf : f 0 = 0) (n : ℕ) :
    selfConvThree (fun m => if m < n then f m else 0) n = selfConvThree f n :=
  selfConvThree_congr (by by_cases h : 0 < n <;> simp [h, hf]) hf fun m hm => by simp [hm]

end PowerSeries
