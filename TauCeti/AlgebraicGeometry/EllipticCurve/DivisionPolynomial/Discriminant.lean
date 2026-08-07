/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# Divisibility of `4Δ` by the square of `ψ₂` at a point

This is the algebraic content of the second half of Nagell–Lutz — that a point's `y`-coordinate is
constrained by the discriminant. For a point `(x, y)` on a Weierstrass curve `W`
over a commutative ring, write `κ = ψ₂(x, y) = 2y + a₁x + a₃` — Mathlib's `2`-division polynomial
evaluated at the point. The theorem here is that if `κ² ∣ 4·Ψ₃(x)`, then either `κ = 0` or
`κ² ∣ 4Δ`.

For a short model `y² = x³ + Ax + B` we have `a₁ = a₃ = 0`, so `κ = 2y` and the conclusion reads
`y = 0` or `4y² ∣ 4Δ`, i.e. the classical `y = 0 ∨ y² ∣ Δ`. The `4`s are not removable in general:
over a ring where `2` is a zero divisor the halving is unavailable, and for a long model `κ` is the
honest invariant rather than `2y`.

The proof is short. On the curve `κ² = Ψ₂Sq(x)`, which is Mathlib's polynomial identity `ψ₂_sq`
evaluated where the Weierstrass polynomial vanishes. And there is an explicit Bézout combination of
`Ψ₂Sq(x)` and `Ψ₃(x)` equal to `4Δ` — a `ring` identity in the `b`-invariants — so anything
dividing both `κ²` and `4·Ψ₃(x)` divides `4Δ`.

## Main results

* `TauCeti.WeierstrassCurve.evalEval_ψ₂_sq`: on the curve, `ψ₂(x, y)² = Ψ₂Sq(x)`.
* `TauCeti.WeierstrassCurve.evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ`: on the curve, if
  `ψ₂(x, y)² ∣ 4·Ψ₃(x)` then `ψ₂(x, y) = 0` or `ψ₂(x, y)² ∣ 4Δ`.

Stated over an arbitrary commutative ring: no domain, integrality or ellipticity hypothesis.

⚠ **No torsion hypothesis appears here, and no part of `lutz_nagell` is proved.** The input
`κ² ∣ 4·Ψ₃(x)` is what a torsion point would supply, through the coordinate formula for `2 • P` —
but that derivation needs the point-level `[n]`-multiplication material (mathlib-track) and is not
in this file. What follows is the algebraic implication alone.

This advances the Nagell–Lutz milestone of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 6,
item "The torsion subgroup and Nagell–Lutz", whose short-model target `lutz_nagell` asks for
`x, y ∈ ℤ` and `y = 0 ∨ y² ∣ Δ` — this is the second conjunct, in the long-model form the roadmap
also names (`lutz_nagell_integrality_general`, "with its discriminant companion").

## Provenance

Ported from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), pinned by
that roadmap at `dev/modular-curves @ 9fec8eba7652`:
`LutzNagell/LutzNagellTheorem/PIDMain.lean`, declarations `kappa_sq_eq_Psi2Sq`, `bezout_identity`,
`kappa_sq_dvd_four_delta`, `eval_Ψ₃` and `lutz_nagell_pid_discriminant`. Restated here against
Mathlib's `ψ₂`, `Ψ₂Sq` and `Ψ₃` rather than the raw expressions the source carries, so no
`eval_Ψ₃` bridge lemma is needed; the source's `[IsDomain]`, `[IsPrincipalIdealRing]` and
`[CharZero]` hypotheses were already `omit`ted there and are absent here too.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate

namespace TauCeti

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve R) {x y : R}

/-- On the curve, the square of `ψ₂` at a point is the univariate `Ψ₂Sq` at its `x`-coordinate.

This is Mathlib's polynomial identity `ψ₂_sq` — `ψ₂² = C Ψ₂Sq + 4 * polynomial` — evaluated at a
point where the Weierstrass polynomial vanishes. -/
theorem evalEval_ψ₂_sq (h : W.toAffine.Equation x y) :
    W.ψ₂.evalEval x y ^ 2 = (W.Ψ₂Sq).eval x := by
  have hsq := congrArg (Polynomial.evalEval x y) W.ψ₂_sq
  rw [_root_.WeierstrassCurve.Affine.Equation] at h
  simpa [h, evalEval_C] using hsq

/-- The Bézout combination exhibiting `4Δ` from `Ψ₂Sq(x)` and `Ψ₃(x)`.

`Δ` is a polynomial in the `b`-invariants, and this is the explicit certificate that `4Δ` lies in
the ideal they generate at any `x`. -/
private theorem bezout_four_mul_Δ (x : R) :
    (432 * x ^ 3 + 108 * W.b₂ * x ^ 2 + 216 * W.b₄ * x +
        (-W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 108 * W.b₆)) * (W.Ψ₂Sq).eval x +
      (-48 * x ^ 2 - 8 * W.b₂ * x + (W.b₂ ^ 2 - 32 * W.b₄)) *
        (6 * x ^ 2 + W.b₂ * x + W.b₄) ^ 2 = 4 * W.Δ := by
  simp only [_root_.WeierstrassCurve.Ψ₂Sq, _root_.WeierstrassCurve.b₂, _root_.WeierstrassCurve.b₄,
    _root_.WeierstrassCurve.b₆, _root_.WeierstrassCurve.b₈, _root_.WeierstrassCurve.Δ,
    eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

/-- The square of `6x² + b₂x + b₄` differs from `4·Ψ₃(x)` by a multiple of `Ψ₂Sq(x)`, so anything
dividing `Ψ₂Sq(x)` and `4·Ψ₃(x)` divides it. -/
private theorem dvd_sq_of_dvd_Ψ₂Sq_of_dvd_four_mul_Ψ₃ {d : R} (hd : d ∣ (W.Ψ₂Sq).eval x)
    (hΨ₃ : d ∣ 4 * (W.Ψ₃).eval x) : d ∣ (6 * x ^ 2 + W.b₂ * x + W.b₄) ^ 2 := by
  have hid : (6 * x ^ 2 + W.b₂ * x + W.b₄) ^ 2 =
      (12 * x + W.b₂) * (W.Ψ₂Sq).eval x - 4 * (W.Ψ₃).eval x := by
    simp only [_root_.WeierstrassCurve.Ψ₂Sq, _root_.WeierstrassCurve.Ψ₃,
      _root_.WeierstrassCurve.b₂, _root_.WeierstrassCurve.b₄, _root_.WeierstrassCurve.b₆,
      _root_.WeierstrassCurve.b₈, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]
    ring
  exact hid ▸ dvd_sub (Dvd.dvd.mul_left hd _) hΨ₃

/-- **The discriminant half of Nagell–Lutz.**

For a point `(x, y)` of `W` whose `ψ₂`-value squared divides `4·Ψ₃(x)`, either that value is zero
or its square divides `4Δ`. For a short model `ψ₂(x, y) = 2y`, so this is `y = 0 ∨ y² ∣ Δ` up to the
factor of `4`. -/
theorem evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ (h : W.toAffine.Equation x y)
    (hΨ₃ : W.ψ₂.evalEval x y ^ 2 ∣ 4 * (W.Ψ₃).eval x) :
    W.ψ₂.evalEval x y = 0 ∨ W.ψ₂.evalEval x y ^ 2 ∣ 4 * W.Δ := by
  refine (eq_or_ne (W.ψ₂.evalEval x y) 0).imp id fun _ ↦ ?_
  have hκ : W.ψ₂.evalEval x y ^ 2 ∣ (W.Ψ₂Sq).eval x := (evalEval_ψ₂_sq W h) ▸ dvd_rfl
  rw [← bezout_four_mul_Δ W x]
  exact dvd_add (Dvd.dvd.mul_left hκ _)
    (Dvd.dvd.mul_left (dvd_sq_of_dvd_Ψ₂Sq_of_dvd_four_mul_Ψ₃ W hκ hΨ₃) _)

end WeierstrassCurve

end TauCeti
