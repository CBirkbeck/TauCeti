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
constructs that series, proves it satisfies the equation, and proves it is the only series
vanishing below degree `3` that does.

## Main definitions

* `TauCeti.formalWCoeff`: the coefficients of `w(z)`, by strong recursion.
* `TauCeti.formalW`: the series `w(z)` itself.
* `TauCeti.formalUCoeff`: the coefficients of `u(z) = w(z) / z ^ 3`, the unit
  part of `w`.

## Main results

* `TauCeti.formalW_recurrence`: **Silverman IV.1.1(a), existence** — `w(z)` satisfies the
  displayed equation as an identity of power series.
* `TauCeti.eq_formalW_of_wEquation`: **Silverman IV.1.1(a), uniqueness** — any power series
  vanishing below degree `3` that satisfies the equation equals `w(z)`. The two together are
  the full statement, that `w(z)` is *the* such series.
* `TauCeti.coeff_wEquation`: the coefficientwise form of that equation's right-hand side, for
  an arbitrary series; this is what makes the uniqueness induction go through.
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
anything about it; here they are `coeff_pow_two` and `coeff_pow_three`, for an arbitrary series.
The truncation lemmas likewise assumed `formalW` and are stated here for any `f` vanishing at
`0`, as consequences of the sharper `selfConvTwo_congr` and `selfConvThree_congr`.

The source does **not** prove uniqueness: its closing note records that the factoring step is
blocked by a `PowerSeries` typeclass gap (`RightDistribClass` and `IsRightCancelAdd` failing to
synthesize), and names coefficient induction as the untried alternative. That is the route
`eq_formalW_of_wEquation` takes here, so this file proves a result the source leaves open.

The source's own generic formal-group scaffolding (`FormalGroupLaw`,
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

theorem coeff_pow_two (w : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (w ^ 2) = selfConvTwo (fun k => PowerSeries.coeff k w) n := by
  rw [sq, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (M := R) (fun i j => PowerSeries.coeff i w * PowerSeries.coeff j w) n]
  rfl

theorem coeff_pow_three (w : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (w ^ 3) = selfConvThree (fun k => PowerSeries.coeff k w) n := by
  have h : (w ^ 3 : PowerSeries R) = w * w ^ 2 := by ring
  rw [h, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (M := R) (fun i j => PowerSeries.coeff i w * PowerSeries.coeff j (w ^ 2)) n]
  simp only [coeff_pow_two, selfConvThree, selfConvTwo, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

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

/-- The `n`-th coefficient of the right-hand side of the `w`-equation, for an arbitrary series
`w`, expressed through the coefficients of `w` itself. Every occurrence of `w` on the right is
multiplied by `X` or appears in a square or cube, which is why the result involves only
coefficients of `w` strictly below `n` once `w` vanishes below degree `3`; that is what makes
both `formalW_recurrence` and `eq_formalW_of_wEquation` go through. -/
theorem coeff_wEquation (w : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.X ^ 3 +
        PowerSeries.C W.a₁ * PowerSeries.X * w +
        PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * w +
        PowerSeries.C W.a₃ * w ^ 2 +
        PowerSeries.C W.a₄ * PowerSeries.X * w ^ 2 +
        PowerSeries.C W.a₆ * w ^ 3) =
      (if n = 3 then 1 else 0) +
        W.a₁ * (if 1 ≤ n then PowerSeries.coeff (n - 1) w else 0) +
        W.a₂ * (if 2 ≤ n then PowerSeries.coeff (n - 2) w else 0) +
        W.a₃ * selfConvTwo (fun k => PowerSeries.coeff k w) n +
        W.a₄ * (if 1 ≤ n then selfConvTwo (fun k => PowerSeries.coeff k w) (n - 1) else 0) +
        W.a₆ * selfConvThree (fun k => PowerSeries.coeff k w) n := by
  rw [show (PowerSeries.C W.a₁ * PowerSeries.X * w : PowerSeries R) =
        PowerSeries.C W.a₁ * (PowerSeries.X ^ 1 * w) by rw [pow_one, mul_assoc],
    show (PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * w : PowerSeries R) =
        PowerSeries.C W.a₂ * (PowerSeries.X ^ 2 * w) from mul_assoc _ _ _,
    show (PowerSeries.C W.a₄ * PowerSeries.X * w ^ 2 : PowerSeries R) =
        PowerSeries.C W.a₄ * (PowerSeries.X ^ 1 * w ^ 2) by rw [pow_one, mul_assoc]]
  rw [map_add, map_add, map_add, map_add, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
    coeff_pow_two, coeff_pow_two, coeff_pow_three]

/-- **Silverman IV.1.1(a), existence.** The `w`-expansion satisfies the equation obtained from
the Weierstrass equation of `W` by the substitution `x = z / w`, `y = -1 / w`. -/
theorem formalW_recurrence :
    formalW W =
      PowerSeries.X ^ 3 +
        PowerSeries.C W.a₁ * PowerSeries.X * formalW W +
        PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * formalW W +
        PowerSeries.C W.a₃ * formalW W ^ 2 +
        PowerSeries.C W.a₄ * PowerSeries.X * formalW W ^ 2 +
        PowerSeries.C W.a₆ * formalW W ^ 3 := by
  ext n
  rw [coeff_wEquation]
  simp only [coeff_formalW]
  rw [formalWCoeff_eq_step]
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

/-- **Silverman IV.1.1(a), uniqueness.** A power series vanishing below degree `3` and satisfying
the `w`-equation is `formalW W`. Together with `formalW_recurrence` this is the full statement of
Silverman IV.1.1(a): `formalW W` is *the* such series.

The equation determines each coefficient from the strictly earlier ones, so the proof is a strong
induction: at index `n` the right-hand side involves `w` only below `n`, by `coeff_wEquation`
together with `selfConvTwo_congr` and `selfConvThree_congr`. -/
theorem eq_formalW_of_wEquation (w : PowerSeries R)
    (hlow : ∀ k, k < 3 → PowerSeries.coeff k w = 0)
    (hw : w =
      PowerSeries.X ^ 3 +
        PowerSeries.C W.a₁ * PowerSeries.X * w +
        PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * w +
        PowerSeries.C W.a₃ * w ^ 2 +
        PowerSeries.C W.a₄ * PowerSeries.X * w ^ 2 +
        PowerSeries.C W.a₆ * w ^ 3) :
    w = formalW W := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_trichotomy n 3 with h | h | h
    · rw [hlow n h, coeff_formalW, formalWCoeff_eq_step]
      unfold formalWStep
      simp [h]
    · subst h
      have hL := congrArg (PowerSeries.coeff 3) hw
      rw [coeff_wEquation] at hL
      rw [hL, coeff_formalW, formalWCoeff_eq_step]
      unfold formalWStep
      norm_num [selfConvTwo, selfConvThree, Finset.sum_range_succ,
        hlow 0 (by norm_num), hlow 1 (by norm_num), hlow 2 (by norm_num)]
    · have hL := congrArg (PowerSeries.coeff n) hw
      rw [coeff_wEquation] at hL
      have hw0 : (fun k => PowerSeries.coeff k w) 0 = 0 := hlow 0 (by omega)
      have hf0 : (fun k => formalWCoeff W k) 0 = 0 := formalWCoeff_zero W
      have hagree : ∀ m, m < n → PowerSeries.coeff m w = formalWCoeff W m := fun m hm => by
        rw [ih m hm, coeff_formalW]
      have h1 : ¬ n < 3 := by omega
      have h2 : ¬ n = 3 := by omega
      have h3 : 1 ≤ n := by omega
      have h4 : 2 ≤ n := by omega
      have h5 : n - 1 < n := by omega
      have h6 : n - 2 < n := by omega
      rw [hL, coeff_formalW, formalWCoeff_eq_step]
      unfold formalWStep
      dsimp only
      simp only [h1, h2, h3, h4, h5, h6, ite_true, ite_false, dite_eq_ite]
      rw [selfConvTwo_congr hw0 hf0 hagree,
        selfConvTwo_congr (n := n - 1) hw0 hf0 (fun m hm => hagree m (by omega)),
        selfConvThree_congr hw0 hf0 hagree,
        selfConvTwo_truncate _ (formalWCoeff_zero W) n,
        selfConvTwo_truncate_sub_one _ n h3,
        selfConvThree_truncate _ (formalWCoeff_zero W) n,
        hagree (n - 1) h5, hagree (n - 2) h6]
      ring

end TauCeti
