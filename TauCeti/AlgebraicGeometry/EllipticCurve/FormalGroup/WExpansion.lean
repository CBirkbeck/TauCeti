/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The `w`-expansion of a Weierstrass curve (Silverman IV.1)

Substituting `x = z / w` and `y = -1 / w` into the Weierstrass equation of `W` and clearing
denominators turns it into

`w = z ^ 3 + a₁ z w + a₂ z ^ 2 w + a₃ w ^ 2 + a₄ z w ^ 2 + a₆ w ^ 3`,

which determines a unique power series `w(z) ∈ R⟦z⟧` with no terms below `z ^ 3`. This file
constructs that series and proves it satisfies the equation.

## Main definitions

* `TauCeti.formalWCoeff`: the coefficients of `w(z)`, by strong recursion.
* `TauCeti.formalW`: the series `w(z)` itself.
* `TauCeti.formalUCoeff`: the coefficients of `u(z) = w(z) / z ^ 3`, the unit
  part of `w`.

## Main results

* `TauCeti.formalW_recurrence`: **Silverman IV.1.1(a)**, that `w(z)` satisfies
  the displayed equation as an identity of power series.
* `TauCeti.coeff_formalW_rhs`: the coefficientwise form of that equation's right-hand side.
* `TauCeti.formalWCoeff_zero`, `_one`, `_two`, `_three`: the series begins
  `w(z) = z ^ 3 + ⋯`.

## Scope

This is the `w`-expansion only, the foundation of the formal group of `W`; the group law
`F(z₁, z₂)` is not here. Mathlib's `FormalGroup` (`Mathlib/RingTheory/FormalGroup/Basic.lean`)
bundles an associativity proof, and associativity of the Weierstrass group law is a separate
theorem of real depth, so a `FormalGroup` term cannot be produced from the `w`-expansion alone.
The directory anticipates that later work.

These declarations sit directly in `TauCeti` rather than in a `TauCeti.WeierstrassCurve`
namespace, so `WeierstrassCurve` dot notation is not available for them:
`scripts/lint-dot-notation.py` rejects new declarations placed in a `TauCeti`-nested Mathlib
type namespace, and the elliptic files on `main` that do use one predate that lint and are
grandfathered by its baseline.

## Provenance

Adapted from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned
by `TauCetiRoadmap/EllipticCurves/README.md` at `dev/hasse-weil @ 513e83879e2f`),
`HasseWeil/FormalGroup.lean`, declarations `conv₂`, `conv₃`, `formalW_step`, `formalW_coeff`,
`formalW`, `formalU_coeff`, the `formalW_coeff_*` lemmas and `formalW_recurrence`.

Changes from the source. The source states its two convolution-coefficient lemmas
(`coeff_formalW_sq`, `coeff_formalW_cube`) only for `formalW`, although neither proof uses
anything about it; here they are `coeff_mk_pow_two` and `coeff_mk_pow_three`, for an arbitrary
coefficient function. The truncation lemmas likewise assumed `formalW` and are stated here for
any `f` vanishing at `0`. The source's own generic formal-group scaffolding (`FormalGroupLaw`,
`bmul`, `binv`, `bpow`, `bcomp`) is deliberately not ported: it predates and duplicates Mathlib's
`Mathlib/RingTheory/FormalGroup/Basic.lean`.
-/

public section

open Finset

namespace TauCeti

variable {R : Type*} [CommRing R]

/-! ### Self-convolutions

`PowerSeries.coeff_mul` gives coefficients of a product as a sum over `Finset.antidiagonal`.
For the recursion below the equivalent sum over `Finset.range` is what is wanted, so we name
the two shapes that occur and record the translation. They are stated for an arbitrary
coefficient function; if a second consumer appears they belong in `TauCeti/RingTheory/PowerSeries/`.
-/

/-- The `n`-th coefficient of the square of the series with coefficients `f`. -/
def selfConvTwo (f : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ range (n + 1), f i * f (n - i)

/-- The `n`-th coefficient of the cube of the series with coefficients `f`. -/
def selfConvThree (f : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ range (n + 1), ∑ j ∈ range (n - i + 1), f i * f j * f (n - i - j)

theorem coeff_mk_pow_two (f : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f ^ 2) = selfConvTwo f n := by
  rw [sq, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (M := R) (fun i j => PowerSeries.coeff i (PowerSeries.mk f) *
        PowerSeries.coeff j (PowerSeries.mk f)) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]

theorem coeff_mk_pow_three (f : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f ^ 3) = selfConvThree f n := by
  have h : (PowerSeries.mk f ^ 3 : PowerSeries R) = PowerSeries.mk f * PowerSeries.mk f ^ 2 := by
    ring
  rw [h, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (M := R) (fun i j => PowerSeries.coeff i (PowerSeries.mk f) *
        PowerSeries.coeff j (PowerSeries.mk f ^ 2)) n]
  simp only [coeff_mk_pow_two, PowerSeries.coeff_mk, selfConvThree, selfConvTwo, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Truncating `f` above `n` does not change `selfConvTwo f n`, when `f 0 = 0`. -/
theorem selfConvTwo_truncate (f : ℕ → R) (hf : f 0 = 0) (n : ℕ) :
    selfConvTwo (fun m => if m < n then f m else 0) n = selfConvTwo f n := by
  simp only [selfConvTwo]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    simp [hf]
  · rcases eq_or_lt_of_le (Nat.sub_le n i) with h' | h'
    · have : i = 0 := by omega
      subst this
      simp [hf]
    · simp [h, h']

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
    selfConvThree (fun m => if m < n then f m else 0) n = selfConvThree f n := by
  simp only [selfConvThree]
  refine Finset.sum_congr rfl fun i hi => ?_
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi hj
  by_cases hi' : i < n
  · by_cases hj' : j < n
    · by_cases hk : n - i - j < n
      · simp [hi', hj', hk]
      · have h0 : i = 0 := by omega
        have h1 : j = 0 := by omega
        subst h0
        subst h1
        simp [hf]
    · have h0 : i = 0 := by omega
      subst h0
      simp [hf]
  · have h0 : i = n := by omega
    subst h0
    have h1 : j = 0 := by omega
    subst h1
    simp [hf]

/-! ### The series `w(z)` -/

/-- One step of the recursion defining `formalWCoeff`: the coefficient of `z ^ n` in
`z ^ 3 + a₁ z w + a₂ z ^ 2 w + a₃ w ^ 2 + a₄ z w ^ 2 + a₆ w ^ 3`, given the earlier
coefficients `ih` of `w`. -/
def formalWStep (W : WeierstrassCurve R) (n : ℕ) (ih : ∀ m, m < n → R) : R :=
  if n < 3 then 0 else if n = 3 then 1 else
  let w : ℕ → R := fun m => if h : m < n then ih m h else 0
  W.a₁ * w (n - 1) + W.a₂ * w (n - 2) + W.a₃ * selfConvTwo w n +
    W.a₄ * selfConvTwo w (n - 1) + W.a₆ * selfConvThree w n

/-- The coefficients of the `w`-expansion of `W`. -/
noncomputable def formalWCoeff (W : WeierstrassCurve R) : ℕ → R :=
  WellFoundedRelation.wf.fix (formalWStep W)

/-- The `w`-expansion `w(z)` of `W`, as a power series (Silverman IV.1). -/
noncomputable def formalW (W : WeierstrassCurve R) : PowerSeries R :=
  PowerSeries.mk (formalWCoeff W)

/-- The coefficients of the unit part `u(z) = w(z) / z ^ 3` of the `w`-expansion. -/
noncomputable def formalUCoeff (W : WeierstrassCurve R) : ℕ → R :=
  fun n => formalWCoeff W (n + 3)

variable (W : WeierstrassCurve R)

/-- Unfolding `formalWCoeff` through its defining recursion. -/
theorem formalWCoeff_eq_step (n : ℕ) :
    formalWCoeff W n = formalWStep W n fun m _ => formalWCoeff W m := by
  change WellFoundedRelation.wf.fix (formalWStep W) n = _
  rw [WellFoundedRelation.wf.fix_eq]
  rfl

@[simp]
theorem formalWCoeff_zero : formalWCoeff W 0 = 0 := by
  rw [formalWCoeff_eq_step]; rfl

@[simp]
theorem formalWCoeff_one : formalWCoeff W 1 = 0 := by
  rw [formalWCoeff_eq_step]; rfl

@[simp]
theorem formalWCoeff_two : formalWCoeff W 2 = 0 := by
  rw [formalWCoeff_eq_step]; rfl

@[simp]
theorem formalWCoeff_three : formalWCoeff W 3 = 1 := by
  rw [formalWCoeff_eq_step]; rfl

@[simp]
theorem formalUCoeff_zero : formalUCoeff W 0 = 1 :=
  formalWCoeff_three W

@[simp]
theorem coeff_formalW (n : ℕ) : PowerSeries.coeff n (formalW W) = formalWCoeff W n :=
  PowerSeries.coeff_mk n _

/-- The `n`-th coefficient of the right-hand side of the `w`-expansion equation, expressed
through the coefficients of `w` itself. Extracted from `formalW_recurrence`, whose proof
compares it with the defining recursion. -/
theorem coeff_formalW_rhs (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.X ^ 3 +
        PowerSeries.C W.a₁ * PowerSeries.X * formalW W +
        PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * formalW W +
        PowerSeries.C W.a₃ * formalW W ^ 2 +
        PowerSeries.C W.a₄ * PowerSeries.X * formalW W ^ 2 +
        PowerSeries.C W.a₆ * formalW W ^ 3) =
      (if n = 3 then 1 else 0) +
        W.a₁ * (if 1 ≤ n then formalWCoeff W (n - 1) else 0) +
        W.a₂ * (if 2 ≤ n then formalWCoeff W (n - 2) else 0) +
        W.a₃ * selfConvTwo (formalWCoeff W) n +
        W.a₄ * (if 1 ≤ n then selfConvTwo (formalWCoeff W) (n - 1) else 0) +
        W.a₆ * selfConvThree (formalWCoeff W) n := by
  simp only [formalW]
  rw [show (PowerSeries.C W.a₁ * PowerSeries.X * PowerSeries.mk (formalWCoeff W)
          : PowerSeries R) =
        PowerSeries.C W.a₁ * (PowerSeries.X ^ 1 * PowerSeries.mk (formalWCoeff W)) by
      rw [pow_one, mul_assoc],
    show (PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * PowerSeries.mk (formalWCoeff W)
          : PowerSeries R) =
        PowerSeries.C W.a₂ * (PowerSeries.X ^ 2 * PowerSeries.mk (formalWCoeff W)) from
      mul_assoc _ _ _,
    show (PowerSeries.C W.a₄ * PowerSeries.X * PowerSeries.mk (formalWCoeff W) ^ 2
          : PowerSeries R) =
        PowerSeries.C W.a₄ * (PowerSeries.X ^ 1 * PowerSeries.mk (formalWCoeff W) ^ 2) by
      rw [pow_one, mul_assoc]]
  rw [map_add, map_add, map_add, map_add, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_mk, coeff_mk_pow_two, coeff_mk_pow_two,
    coeff_mk_pow_three]

/-- **Silverman IV.1.1(a).** The `w`-expansion satisfies the equation obtained from the
Weierstrass equation of `W` by the substitution `x = z / w`, `y = -1 / w`. -/
theorem formalW_recurrence :
    formalW W =
      PowerSeries.X ^ 3 +
        PowerSeries.C W.a₁ * PowerSeries.X * formalW W +
        PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * formalW W +
        PowerSeries.C W.a₃ * formalW W ^ 2 +
        PowerSeries.C W.a₄ * PowerSeries.X * formalW W ^ 2 +
        PowerSeries.C W.a₆ * formalW W ^ 3 := by
  ext n
  rw [coeff_formalW_rhs, coeff_formalW, formalWCoeff_eq_step]
  unfold formalWStep
  dsimp only
  simp only [dite_eq_ite]
  rcases lt_trichotomy n 3 with h | h | h
  · interval_cases n <;>
      simp [selfConvTwo, selfConvThree, Finset.sum_range_succ]
  · subst h
    norm_num [selfConvTwo, selfConvThree, Finset.sum_range_succ]
  · have h1 : ¬ n < 3 := by omega
    have h2 : ¬ n = 3 := by omega
    have h3 : 1 ≤ n := by omega
    have h4 : 2 ≤ n := by omega
    have h5 : n - 1 < n := by omega
    have h6 : n - 2 < n := by omega
    simp only [h1, h2, h3, h4, h5, h6, ite_true, ite_false]
    rw [selfConvTwo_truncate _ (formalWCoeff_zero W) n,
      selfConvTwo_truncate_sub_one _ n h3,
      selfConvThree_truncate _ (formalWCoeff_zero W) n]
    ring

end TauCeti
