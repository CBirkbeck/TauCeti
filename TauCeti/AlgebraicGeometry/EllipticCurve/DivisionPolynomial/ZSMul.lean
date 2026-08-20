/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Universal

/-!
# Coordinates of scalar multiplication on the universal curve

The Nagell–Lutz route expresses `n • (X, Y)` on the universal curve through the division
polynomials: the affine `X`-coordinate is `φₙ/ψₙ²` and the `Y`-coordinate is `ωₙ/ψₙ³`, as
elements of `Universal.Field`. This file defines those two rational functions, `smulX` and
`smulY` — the identification with `n • point` itself is proved in the scalar-multiplication
development, not here — and develops the `smulX` calculus that identification consumes: values
at `0`, `1` and `2`, the offset `ψₙ₊₁ψₙ₋₁/ψₙ²` from the `X`-coordinate, evenness in `n`,
nonvanishing, the difference `smulX m - smulX n` as a single quotient, and the separation
statement `smulX m = smulX n ↔ m = n ∨ m = -n`. `smulY`'s own negative-index rule is here too:
a negative index negates the point, so `smulY (-n)` is the `negY` of `(smulX n, smulY n)`.

## Main definitions

* `WeierstrassCurve.Universal.Affine.smulX`: the rational function `φₙ/ψₙ²`.
* `WeierstrassCurve.Universal.Affine.smulY`: the rational function `ωₙ/ψₙ³`.

## Main results

* `WeierstrassCurve.Universal.Affine.smulX_eq`: `smulX n = smulX 1 - ψₙ₊₁ψₙ₋₁/ψₙ²` for `n ≠ 0`,
  the offset from the `X`-coordinate that `smulX_two` and `smulX_sub_smulX` both run through.
* `WeierstrassCurve.Universal.Affine.smulX_sub_smulX`: `smulX m - smulX n` as a single
  quotient, by the elliptic-sequence relation of the universal `ψ` family.
* `WeierstrassCurve.Universal.Affine.smulX_ne_zero`: `smulX n ≠ 0` for `n ≠ 0`.
* `WeierstrassCurve.Universal.Affine.smulX_eq_smulX_iff`: `smulX m = smulX n ↔ m = n ∨ m = -n`,
  the field-level form of the fact that `x`-coordinates separate multiples up to sign.
* `WeierstrassCurve.Universal.Affine.smulY_neg`: `smulY (-n)` is the `negY` of the coordinates
  at `n` — the long-Weierstrass correction that `ω_neg` carries, read in the universal field.

## Provenance

Ported from J. Xu and D. K. Angdinata's `projects/NagellLutz/LutzNagell/ZSMul.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main @
1c1c74664e40071c2c2165bc55ca2616a67ccd6b`): `smulX` (`:164`), `smulY` (`:168`), the value
lemmas (`:171`–`:174`), `smulX_eq` (`:176`), `smulX_two` (`:183`), `smulX_sub_smulX` (`:186`),
`smulX_neg` (`:201`), `smulX_ne_zero` (`:203`), `smulX_ne_smulX` (`:206`),
`smulX_eq_smulX_iff` (`:217`), and `smulY_neg` with its private field-level auxiliary
(`:288`–`:291`), pulled forward from the slope slice's range so that `smulY` does not ship
without its negative-index rule. The source's `ψᵤ` abbreviation is dropped in favour of
`polyToField (curve.ψ n)`, the `DivisionPolynomial/Universal.lean` convention. Three departures
beyond the respelling: the elliptic-sequence step of `smulX_sub_smulX` is respelt through
`IsEllipticNet.rel` and `linear_combination` (the source converts against its
`isEllSequence_ψᵤ`, a statement shape Mathlib has since replaced); the equation lemmas
`smulX_def` and `smulY_def` are added for consumers in other modules, as in `Omega.lean`; and
`smulY_neg` names its ring hom (`map_neg polyToField`) where the source unfolds `ψᵤ`, because
an unnamed `map_neg` does not fire on a `polyToField` application in this direction.
`smulX_sub_sub_smulX_add` (`:196`) is deliberately not ported here: its consumers are the slope
and addition formulas, and it ships with them.
-/

public section

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Universal.Affine

variable {m n : ℤ}

/-- The rational function `φₙ/ψₙ²` in the universal field, which the scalar-multiplication
development identifies as the affine `X`-coordinate of `n • (X, Y)` on the universal curve —
that identification is proved there, not here. -/
def smulX (n : ℤ) : Universal.Field :=
  polyToField (curve.φ n) / polyToField (curve.ψ n) ^ 2

/-- The rational function `ωₙ/ψₙ³` in the universal field, which the scalar-multiplication
development identifies as the affine `Y`-coordinate of `n • (X, Y)` on the universal curve —
that identification is proved there, not here. -/
def smulY (n : ℤ) : Universal.Field :=
  polyToField (curve.ω n) / polyToField (curve.ψ n) ^ 3

/-- The defining formula for `smulX`. The definition body is not exposed, so this equation
lemma is how a consumer in another module computes with it. -/
theorem smulX_def (n : ℤ) : smulX n = polyToField (curve.φ n) / polyToField (curve.ψ n) ^ 2 := (rfl)

/-- The defining formula for `smulY`. The definition body is not exposed, so this equation
lemma is how a consumer in another module computes with it. -/
theorem smulY_def (n : ℤ) : smulY n = polyToField (curve.ω n) / polyToField (curve.ψ n) ^ 3 := (rfl)

/-- `smulX` at `0` is `0`. -/
@[simp] lemma smulX_zero : smulX 0 = 0 := by simp [smulX_def]

/-- `smulY` at `0` is `0`. -/
@[simp] lemma smulY_zero : smulY 0 = 0 := by simp [smulY_def]

/-- `smulX` at `1` is the `X`-coordinate itself. -/
@[simp] lemma smulX_one : smulX 1 = polyToField (C X) := by simp [smulX_def]

/-- `smulY` at `1` is the `Y`-coordinate itself. -/
@[simp] lemma smulY_one : smulY 1 = polyToField Y := by simp [smulY_def]

/-- `smulX n` differs from the `X`-coordinate by `ψₙ₊₁ψₙ₋₁/ψₙ²`. -/
lemma smulX_eq (hn : n ≠ 0) :
    smulX n = smulX 1 - polyToField (curve.ψ (n + 1)) * polyToField (curve.ψ (n - 1)) /
      polyToField (curve.ψ n) ^ 2 := by
  have h : curve.φ n + curve.ψ (n + 1) * curve.ψ (n - 1) = C X * curve.ψ n ^ 2 := by
    rw [WeierstrassCurve.φ]
    ring
  rw [smulX_def, eq_sub_iff_add_eq, ← add_div, ← map_mul, ← map_add, h,
    div_eq_iff (pow_ne_zero 2 (polyToField_ψ_ne_zero hn)), smulX_one, ← map_pow, ← map_mul]

/-- `smulX` at `2`, in terms of the `X`-coordinate and `ψ₃/ψ₂²`. -/
lemma smulX_two : smulX 2 = smulX 1 - polyToField (curve.ψ 3) / polyToField (curve.ψ 2) ^ 2 := by
  simp [smulX_eq two_ne_zero]

/-- The difference of two values of `smulX` as a single quotient: the numerator is
`ψₙ₊ₘψₙ₋ₘ`, by the elliptic-sequence relation of the universal `ψ` family. -/
lemma smulX_sub_smulX (hm : m ≠ 0) (hn : n ≠ 0) :
    smulX m - smulX n = polyToField (curve.ψ (n + m)) * polyToField (curve.ψ (n - m)) /
      (polyToField (curve.ψ n) * polyToField (curve.ψ m)) ^ 2 := by
  have key := isEllipticSequence_polyToField_ψ n m 1
  simp only [IsEllipticNet.rel, add_zero, ψ_one, map_one, mul_one] at key
  rw [smulX_eq hm, smulX_eq hn, sub_sub_sub_cancel_left,
    div_sub_div _ _ (pow_ne_zero 2 (polyToField_ψ_ne_zero hn))
      (pow_ne_zero 2 (polyToField_ψ_ne_zero hm)), mul_pow]
  congr 1
  linear_combination -key

/-- `smulX` is even in `n`. -/
@[simp] lemma smulX_neg : smulX (-n) = smulX n := by simp [smulX_def, φ_neg, ψ_neg]

private lemma smulY_neg_aux {F : Type*} [Field F] {a₁ a₃ x y z : F} (hz : z ≠ 0) :
    (y + a₁ * x * z + a₃ * z ^ 3) / (-z) ^ 3 = -(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃ := by
  rw [neg_pow]
  field_simp
  ring

/-- `smulY` at a negative index is the negation of the point at the positive one: the
long-Weierstrass `negY` of the coordinates `(smulX n, smulY n)`. -/
lemma smulY_neg (h0 : n ≠ 0) :
    smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  simp only [WeierstrassCurve.Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX_def, smulY_def,
    ψ_neg, ω_neg, map_add, map_neg polyToField, map_mul, map_pow]
  exact smulY_neg_aux (polyToField_ψ_ne_zero h0)

/-- `smulX n` is nonzero for `n ≠ 0`. -/
lemma smulX_ne_zero (h0 : n ≠ 0) : smulX n ≠ 0 :=
  div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| polyToField_ψ_ne_zero h0)

/-- `smulX` separates indices that agree in neither order nor sign. -/
lemma smulX_ne_smulX (ne : m ≠ n) (ne_neg : m ≠ -n) : smulX m ≠ smulX n := by
  obtain rfl | hm := eq_or_ne m 0
  · simpa using (smulX_ne_zero ne.symm).symm
  obtain rfl | hn := eq_or_ne n 0
  · simpa using smulX_ne_zero ne
  rw [← sub_ne_zero, smulX_sub_smulX hm hn]
  refine div_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero _ <| mul_ne_zero ?_ ?_) <;>
    apply polyToField_ψ_ne_zero <;> omega

/-- Two values of `smulX` agree exactly when the indices agree up to sign. -/
@[simp] lemma smulX_eq_smulX_iff : smulX m = smulX n ↔ m = n ∨ m = -n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h
    exact smulX_ne_smulX h.1 h.2
  · rintro (rfl | rfl)
    exacts [rfl, smulX_neg]

end WeierstrassCurve.Universal.Affine
