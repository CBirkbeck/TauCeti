/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import TauCeti.RingTheory.PowerSeries.SelfConvolution

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
* `TauCeti.formalUCoeff`, `TauCeti.formalU`: the coefficients, and the series itself, of
  `u(z) = w(z) / z ^ 3`, the unit part of `w`.

## Main results

* `TauCeti.formalW_recurrence`: **Silverman IV.1.1(a), existence** — `w(z)` satisfies the
  displayed equation as an identity of power series.
* `TauCeti.eq_formalW_of_recurrence`: **Silverman IV.1.1(a), uniqueness** — any power series
  with vanishing constant coefficient that satisfies the equation equals `w(z)`. The two
  together are the full statement, that `w(z)` is *the* such series.
* `TauCeti.formalWCoeff_recurrence`: the coefficientwise recurrence — each coefficient of
  `w(z)` above the leading one, from the strictly earlier ones. This is the form to compute
  with; the strong recursion behind `formalWCoeff` is an implementation detail.
* `TauCeti.coeff_formalW_recurrence_rhs`: the coefficientwise form of that equation's
  right-hand side, for an arbitrary series; this is what makes the uniqueness induction go
  through.
* `TauCeti.formalWCoeff_zero`, `_one`, `_two`, `_three`: the series begins
  `w(z) = z ^ 3 + ⋯`.
* `TauCeti.formalW_eq_X_pow_mul_formalU`: `w(z) = z ^ 3 * u(z)`, the unit part doing what its
  name says, with `u(0) = 1` by `TauCeti.constantCoeff_formalU`.

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
`HasseWeil/FormalGroup.lean`, declarations `formalW_step`, `formalW_coeff`, `formalW`,
`formalU_coeff`, the `formalW_coeff_*` lemmas and `formalW_recurrence`.

Changes from the source. The source's convolution helpers `conv₂` and `conv₃`, and its
coefficient and truncation lemmas for them, are stated only for `formalW`, although none of
those proofs uses anything about that series. Generalised to an arbitrary series — and to a
`Semiring`, which is all they need — they are not elliptic-curve material at all, and live in
`TauCeti.RingTheory.PowerSeries.SelfConvolution`, which this file imports and which carries
their attribution.

The source does **not** prove uniqueness: its closing note records that the factoring step is
blocked by a `PowerSeries` typeclass gap (`RightDistribClass` and `IsRightCancelAdd` failing to
synthesize), and names coefficient induction as the untried alternative. That is the route
`eq_formalW_of_recurrence` takes here, so this file proves a result the source leaves open.

The source's own generic formal-group scaffolding (`FormalGroupLaw`,
`bmul`, `binv`, `bpow`, `bcomp`) is deliberately not ported: it predates and duplicates Mathlib's
`Mathlib/RingTheory/FormalGroup/Basic.lean`.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R]

/-! ### The series `w(z)` -/

/-- One step of the recursion defining `formalWCoeff`: the coefficient of `z ^ n` in
`z ^ 3 + a₁ z w + a₂ z ^ 2 w + a₃ w ^ 2 + a₄ z w ^ 2 + a₆ w ^ 3`, given the earlier
coefficients `ih` of `w`.

This is the implementation of the strong recursion and is deliberately not part of the API;
`formalWCoeff_recurrence` is the recurrence to use downstream. -/
private def formalWStep (W : WeierstrassCurve R) (n : ℕ) (ih : ∀ m, m < n → R) : R :=
  if n < 3 then 0 else if n = 3 then 1 else
  let w : ℕ → R := fun m => if h : m < n then ih m h else 0
  W.a₁ * w (n - 1) + W.a₂ * w (n - 2) + W.a₃ * PowerSeries.selfConvTwo w n +
    W.a₄ * PowerSeries.selfConvTwo w (n - 1) + W.a₆ * PowerSeries.selfConvThree w n

/-- The coefficients of the `w`-expansion of `W`. -/
noncomputable def formalWCoeff (W : WeierstrassCurve R) : ℕ → R :=
  WellFoundedRelation.wf.fix (formalWStep W)

/-- The `w`-expansion `w(z)` of `W`, as a power series (Silverman IV.1). -/
noncomputable def formalW (W : WeierstrassCurve R) : PowerSeries R :=
  PowerSeries.mk (formalWCoeff W)

/-- The coefficients of the unit part `u(z) = w(z) / z ^ 3` of the `w`-expansion. -/
@[expose] noncomputable def formalUCoeff (W : WeierstrassCurve R) : ℕ → R :=
  fun n => formalWCoeff W (n + 3)

/-- The unit part `u(z) = w(z) / z ^ 3` of the `w`-expansion, as a power series. -/
noncomputable def formalU (W : WeierstrassCurve R) : PowerSeries R :=
  PowerSeries.mk (formalUCoeff W)

variable (W : WeierstrassCurve R)

/-- Unfolding `formalWCoeff` through its defining recursion. -/
private theorem formalWCoeff_eq_step (n : ℕ) :
    formalWCoeff W n = formalWStep W n fun m _ => formalWCoeff W m := by
  unfold formalWCoeff
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

/-- The recurrence characterising the coefficients of `w(z)` above the leading term: each is
determined by the strictly earlier ones. This is the coefficientwise form of
`formalW_recurrence`, and the intended way to compute with `formalWCoeff`. -/
theorem formalWCoeff_recurrence {n : ℕ} (hn : 3 < n) :
    formalWCoeff W n =
      W.a₁ * formalWCoeff W (n - 1) + W.a₂ * formalWCoeff W (n - 2) +
        W.a₃ * PowerSeries.selfConvTwo (formalWCoeff W) n +
        W.a₄ * PowerSeries.selfConvTwo (formalWCoeff W) (n - 1) +
        W.a₆ * PowerSeries.selfConvThree (formalWCoeff W) n := by
  have h1 : ¬ n < 3 := by omega
  have h2 : ¬ n = 3 := by omega
  have h5 : n - 1 < n := by omega
  have h6 : n - 2 < n := by omega
  rw [formalWCoeff_eq_step]
  unfold formalWStep
  dsimp only
  simp only [h1, h2, h5, h6, ite_true, ite_false, dite_eq_ite]
  rw [PowerSeries.selfConvTwo_truncate _ (formalWCoeff_zero W) n,
    PowerSeries.selfConvTwo_truncate_sub_one _ n (by omega),
    PowerSeries.selfConvThree_truncate _ (formalWCoeff_zero W) n]

/-- The unit-part coefficients are the coefficients of `w(z)` shifted down by three. -/
@[simp]
theorem formalUCoeff_apply (n : ℕ) : formalUCoeff W n = formalWCoeff W (n + 3) := rfl

/-- The unit part starts at `1`. Not `@[simp]`: with `formalUCoeff_apply` in the simp set this
is already reachable from `formalWCoeff_three`, and tagging it too is a `simpNF` duplicate. -/
theorem formalUCoeff_zero : formalUCoeff W 0 = 1 :=
  formalWCoeff_three W

@[simp]
theorem coeff_formalW (n : ℕ) : PowerSeries.coeff n (formalW W) = formalWCoeff W n :=
  PowerSeries.coeff_mk n _

@[simp]
theorem coeff_formalU (n : ℕ) : PowerSeries.coeff n (formalU W) = formalUCoeff W n :=
  PowerSeries.coeff_mk n _

@[simp]
theorem constantCoeff_formalU : PowerSeries.constantCoeff (formalU W) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_formalU, formalUCoeff_zero]

/-- The `w`-expansion factors through its unit part: `w(z) = z ^ 3 * u(z)`. The unit part is a
unit in the sense that its *constant coefficient* is `1` (`constantCoeff_formalU`); the series
`u(z)` itself is of course not `1`. -/
theorem formalW_eq_X_pow_mul_formalU : formalW W = PowerSeries.X ^ 3 * formalU W := by
  ext n
  rw [coeff_formalW, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_formalU, formalUCoeff_apply, Nat.sub_add_cancel h]
  · have hn : n < 3 := by omega
    interval_cases n <;> simp

/-- The `n`-th coefficient of the right-hand side of the `w`-equation, for an arbitrary series
`w`, expressed through the coefficients of `w` itself. Every occurrence of `w` on the right is
multiplied by `X` or appears in a square or cube, which is why the result involves only
coefficients of `w` strictly below `n` once `w` vanishes below degree `3`; that is what makes
both `formalW_recurrence` and `eq_formalW_of_recurrence` go through. -/
theorem coeff_formalW_recurrence_rhs (w : PowerSeries R) (n : ℕ) :
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
        W.a₃ * PowerSeries.selfConvTwo (fun k => PowerSeries.coeff k w) n +
        W.a₄ * (if 1 ≤ n then
            PowerSeries.selfConvTwo (fun k => PowerSeries.coeff k w) (n - 1)
          else 0) +
        W.a₆ * PowerSeries.selfConvThree (fun k => PowerSeries.coeff k w) n := by
  -- `PowerSeries.coeff_C_mul` and `PowerSeries.coeff_X_pow_mul'` each need their argument in the
  -- shape `C a * (X ^ d * f)`, so first reassociate the three products and write the bare `X` as
  -- `X ^ 1`. Rewriting `← pow_one` directly is not an option: it would also fire inside `X ^ 3`.
  have hX1 : ∀ (a : R) (f : PowerSeries R),
      PowerSeries.C a * PowerSeries.X * f = PowerSeries.C a * (PowerSeries.X ^ 1 * f) := by
    intro a f
    rw [pow_one, mul_assoc]
  have hX2 : ∀ (a : R) (f : PowerSeries R),
      PowerSeries.C a * PowerSeries.X ^ 2 * f = PowerSeries.C a * (PowerSeries.X ^ 2 * f) :=
    fun a f => mul_assoc _ _ _
  rw [hX1 W.a₁ w, hX2 W.a₂ w, hX1 W.a₄ (w ^ 2)]
  -- Two passes, and the order is load-bearing: `coeff_pow_three` also matches the leading
  -- `X ^ 3`, so that term must be resolved by `coeff_X_pow` before the convolution lemmas run.
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow]
  simp only [PowerSeries.coeff_pow_two, PowerSeries.coeff_pow_three]

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
  rw [coeff_formalW_recurrence_rhs]
  simp only [coeff_formalW]
  rw [formalWCoeff_eq_step]
  unfold formalWStep
  dsimp only
  simp only [dite_eq_ite]
  rcases lt_trichotomy n 3 with h | h | h
  · interval_cases n <;>
      simp [PowerSeries.selfConvTwo_def, PowerSeries.selfConvThree_def, Finset.sum_range_succ]
  · subst h
    norm_num [PowerSeries.selfConvTwo_def, PowerSeries.selfConvThree_def, Finset.sum_range_succ]
  · have h1 : ¬ n < 3 := by omega
    have h2 : ¬ n = 3 := by omega
    have h3 : 1 ≤ n := by omega
    have h4 : 2 ≤ n := by omega
    have h5 : n - 1 < n := by omega
    have h6 : n - 2 < n := by omega
    simp only [h1, h2, h3, h4, h5, h6, ite_true, ite_false]
    rw [PowerSeries.selfConvTwo_truncate _ (formalWCoeff_zero W) n,
      PowerSeries.selfConvTwo_truncate_sub_one _ n h3,
      PowerSeries.selfConvThree_truncate _ (formalWCoeff_zero W) n]
    ring

/-- **Silverman IV.1.1(a), uniqueness.** A power series with vanishing constant coefficient that
satisfies the `w`-equation is `formalW W`. Together with `formalW_recurrence` this is the full
statement of Silverman IV.1.1(a): `formalW W` is *the* such series.

Only `coeff 0 w = 0` is assumed: the equation at degrees `1` and `2` then forces those two
coefficients to vanish as well, because every occurrence of `w` on its right-hand side is
multiplied by `X` or sits in a square or a cube.

The equation determines each coefficient from the strictly earlier ones, so the proof is a strong
induction: at index `n` the right-hand side involves `w` only below `n`, by
`coeff_formalW_recurrence_rhs` together with `PowerSeries.selfConvTwo_congr` and
`PowerSeries.selfConvThree_congr`. -/
theorem eq_formalW_of_recurrence (w : PowerSeries R)
    (h0 : PowerSeries.coeff 0 w = 0)
    (hw : w =
      PowerSeries.X ^ 3 +
        PowerSeries.C W.a₁ * PowerSeries.X * w +
        PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * w +
        PowerSeries.C W.a₃ * w ^ 2 +
        PowerSeries.C W.a₄ * PowerSeries.X * w ^ 2 +
        PowerSeries.C W.a₆ * w ^ 3) :
    w = formalW W := by
  -- Degrees `1` and `2` are forced, so the induction below can still start from degree `3`.
  have h1 : PowerSeries.coeff 1 w = 0 := by
    have hL := congrArg (PowerSeries.coeff 1) hw
    rw [coeff_formalW_recurrence_rhs] at hL
    norm_num [PowerSeries.selfConvTwo_def, PowerSeries.selfConvThree_def,
      Finset.sum_range_succ, h0] at hL
    exact hL
  have h2 : PowerSeries.coeff 2 w = 0 := by
    have hL := congrArg (PowerSeries.coeff 2) hw
    rw [coeff_formalW_recurrence_rhs] at hL
    norm_num [PowerSeries.selfConvTwo_def, PowerSeries.selfConvThree_def,
      Finset.sum_range_succ, h0, h1] at hL
    exact hL
  have hlow : ∀ k, k < 3 → PowerSeries.coeff k w = 0 := by
    intro k hk
    interval_cases k
    exacts [h0, h1, h2]
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_trichotomy n 3 with h | h | h
    · rw [hlow n h, coeff_formalW, formalWCoeff_eq_step]
      unfold formalWStep
      simp [h]
    · subst h
      have hL := congrArg (PowerSeries.coeff 3) hw
      rw [coeff_formalW_recurrence_rhs] at hL
      rw [hL, coeff_formalW, formalWCoeff_eq_step]
      unfold formalWStep
      norm_num [PowerSeries.selfConvTwo_def, PowerSeries.selfConvThree_def, Finset.sum_range_succ,
        hlow 0 (by norm_num), hlow 1 (by norm_num), hlow 2 (by norm_num)]
    · have hL := congrArg (PowerSeries.coeff n) hw
      rw [coeff_formalW_recurrence_rhs] at hL
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
      rw [PowerSeries.selfConvTwo_congr hw0 hf0 hagree,
        PowerSeries.selfConvTwo_congr (n := n - 1) hw0 hf0 (fun m hm => hagree m (by omega)),
        PowerSeries.selfConvThree_congr hw0 hf0 hagree,
        PowerSeries.selfConvTwo_truncate _ (formalWCoeff_zero W) n,
        PowerSeries.selfConvTwo_truncate_sub_one _ n h3,
        PowerSeries.selfConvThree_truncate _ (formalWCoeff_zero W) n,
        hagree (n - 1) h5, hagree (n - 2) h6]
      ring

end TauCeti
