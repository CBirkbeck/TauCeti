/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# The sharp discriminant divisibility for a model with `a₁ = a₃ = 0`

For a Weierstrass model with `a₁ = a₃ = 0` — so the equation is the cubic
`y² = x³ + a₂x² + a₄x + a₆` — a point whose `y²` divides `Ψ₃(x)` has `y²` dividing the
**discriminant of that cubic**, Mathlib's `Cubic.discr ⟨1, a₂, a₄, a₆⟩`.

This is sharper than dividing `Δ`. Mathlib's `twoTorsionPolynomial_discr` records
`Cubic.discr ⟨4, b₂, 2b₄, b₆⟩ = 16Δ`, and for these models `Δ = 16 · Cubic.discr ⟨1, a₂, a₄, a₆⟩`,
so the cubic discriminant is the invariant with the factors of `16` divided out. It is the `Δ` of
the classical statement of Nagell–Lutz for a short model, where `a₂ = 0` too and the conclusion
reads `y² ∣ 4a₄³ + 27a₆²` up to sign.

The proof is two ring identities over the cubic. Writing `f(x) = x³ + a₂x² + a₄x + a₆`, the
derivative square `f'(x)² = (3x² + 2a₂x + a₄)²` differs from `Ψ₃(x)` by a multiple of `f(x) = y²`;
and `Cubic.discr` is an explicit combination of `y²` and `f'(x)²`. So `y² ∣ Ψ₃(x)` propagates to
`y² ∣ f'(x)²` and then to the discriminant.

## Main results

* `TauCeti.WeierstrassCurve.sq_dvd_derivative_sq`: `y² ∣ (3x² + 2a₂x + a₄)²`.
* `TauCeti.WeierstrassCurve.sq_dvd_cubic_discr_of_sq_dvd_derivative_sq`: the discriminant step on
  its own — no `a₁ = a₃ = 0`, no `Ψ₃`, just the curve equation and that divisibility.
* `TauCeti.WeierstrassCurve.sq_dvd_cubic_discr`: `y² ∣ Cubic.discr ⟨1, a₂, a₄, a₆⟩`, the two
  composed.

Both are over an arbitrary commutative ring, for an arbitrary point of the curve — no domain,
torsion, integrality or ellipticity hypothesis. The input `y² ∣ Ψ₃(x)` is what a torsion point
supplies through the coordinate formula for `2 • P`; that derivation is not part of this file.

This advances the Nagell–Lutz milestone of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 6,
item "The torsion subgroup and Nagell–Lutz", whose short-model target `lutz_nagell` asks for
`y = 0 ∨ y² ∣ Δ`; this is the sharp form of that second conjunct.

## Provenance

Ported from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), pinned by
that roadmap at `dev/modular-curves @ 9fec8eba7652`:
`LutzNagell/LutzNagellTheorem/PIDMain.lean`, the algebraic core of
`lutz_nagell_cubicDisc_discriminant` (:438). The source states the conclusion as the raw polynomial
`4a₄³ + 27a₆² + 4a₂³a₆ − a₂²a₄² − 18a₂a₄a₆` and reaches it inside a torsion argument; here it is
the negative of Mathlib's `Cubic.discr`, and the torsion-dependent part — which needs the
point-level `[n]`-multiplication material — is left out, with `y² ∣ Ψ₃(x)` as a hypothesis instead.
-/

public section

open Polynomial

namespace TauCeti

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve R) {x y : R}

/-- For a model with `a₁ = a₃ = 0`, the square of the derivative of the defining cubic differs from
`Ψ₃(x)` by a multiple of `y²`, so `y² ∣ Ψ₃(x)` forces `y² ∣ (3x² + 2a₂x + a₄)²`. -/
theorem sq_dvd_derivative_sq (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (hcurve : y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (hΨ₃ : y ^ 2 ∣ (W.Ψ₃).eval x) : y ^ 2 ∣ (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 := by
  have hid : (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 =
      (12 * x + 4 * W.a₂) * y ^ 2 - (W.Ψ₃).eval x := by
    simp only [_root_.WeierstrassCurve.Ψ₃, _root_.WeierstrassCurve.b₂,
      _root_.WeierstrassCurve.b₄, _root_.WeierstrassCurve.b₆, _root_.WeierstrassCurve.b₈,
      ha₁, ha₃, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]
    rw [hcurve]; ring
  exact hid ▸ dvd_sub (Dvd.dvd.mul_left dvd_rfl _) hΨ₃

/-- The discriminant of `x³ + a₂x² + a₄x + a₆` is a combination of `y²` and the square of the
cubic's derivative, so `y²` divides it as soon as it divides that square.

This step needs neither `a₁ = a₃ = 0` nor anything about `Ψ₃`: only the curve equation and the
divisibility of the derivative square. -/
theorem sq_dvd_cubic_discr_of_sq_dvd_derivative_sq
    (hcurve : y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (hderiv : y ^ 2 ∣ (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2) :
    y ^ 2 ∣ (Cubic.mk 1 W.a₂ W.a₄ W.a₆).discr := by
  have hid : (Cubic.mk 1 W.a₂ W.a₄ W.a₆).discr =
      (27 * x ^ 3 + 27 * W.a₂ * x ^ 2 + 27 * W.a₄ * x - 4 * W.a₂ ^ 3 + 18 * W.a₂ * W.a₄
          - 27 * W.a₆) * y ^ 2
        - (3 * x ^ 2 + 2 * W.a₂ * x - W.a₂ ^ 2 + 4 * W.a₄) *
          (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 := by
    simp only [Cubic.discr]
    rw [hcurve]; ring
  exact hid ▸ dvd_sub (Dvd.dvd.mul_left dvd_rfl _) (Dvd.dvd.mul_left hderiv _)

/-- **The sharp discriminant divisibility.**

For a model with `a₁ = a₃ = 0`, a point whose `y²` divides `Ψ₃(x)` has `y²` dividing the
discriminant of the defining cubic `x³ + a₂x² + a₄x + a₆`. For a short model (`a₂ = 0` as well)
this is the classical `y² ∣ 4a₄³ + 27a₆²` up to sign. -/
theorem sq_dvd_cubic_discr (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (hcurve : y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (hΨ₃ : y ^ 2 ∣ (W.Ψ₃).eval x) :
    y ^ 2 ∣ (Cubic.mk 1 W.a₂ W.a₄ W.a₆).discr :=
  sq_dvd_cubic_discr_of_sq_dvd_derivative_sq W hcurve
    (sq_dvd_derivative_sq W ha₁ ha₃ hcurve hΨ₃)

end WeierstrassCurve

end TauCeti
