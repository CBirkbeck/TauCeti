/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.NaiveHeight

/-!
# The canonical (Néron–Tate) height

The naïve height `h` is quadratic only up to a bounded error: `approx_parallelogram_law` gives a
constant `C` with `|h(P + Q) + h(P - Q) - 2(h P + h Q)| ≤ C`. Tate's observation is that averaging
that error away along the doubling map produces an honestly quadratic function. This file carries
out that construction and records the two facts that pin it down: the limit exists, and it stays
within a bounded distance of `h`.

`canonicalHeight P = lim_{n → ∞} h(2ⁿ P) / 4ⁿ`

## Main definitions

* `WeierstrassCurve.Affine.Point.canonicalHeight`: the limit above.

## Main results

* `WeierstrassCurve.Affine.Point.tendsto_naiveHeight_two_pow_nsmul_div_four_pow`: the defining
  limit is
  attained, so `canonicalHeight` is the limit and not the junk value `limUnder` returns when a
  sequence does not converge. Every property of the canonical height is proved by transporting a
  property of `h`
  along this.
* `WeierstrassCurve.Affine.Point.canonicalHeight_zero` and
  `WeierstrassCurve.Affine.Point.canonicalHeight_neg`: its values at the two points every consumer
  meets first, as `@[simp]` normal forms.
* `WeierstrassCurve.Affine.Point.abs_canonicalHeight_sub_naiveHeight_le`: the canonical height stays
  within a bounded distance of the naïve one, by a
  constant depending only on the curve. This is what makes the two interchangeable in
  finiteness arguments — in particular Northcott finiteness transfers to it.

## Implementation notes

The doubling bound `|h(2P) - 4 h(P)| ≤ C` is the parallelogram law at `Q = P`, where `P - Q = 0`
and `h(0) = 0`. Only that specialisation is used here, so it is kept private.

Convergence is `cauchySeq_of_le_geometric` at ratio `1/4`: consecutive terms of `h(2ⁿ P) / 4ⁿ`
differ by `|h(2 · 2ⁿ P) - 4 h(2ⁿ P)| / 4ⁿ⁺¹ ≤ C / 4ⁿ⁺¹`. The same estimate feeds Mathlib's
`dist_le_of_le_geometric_of_tendsto₀`, which bounds the distance from the *zeroth* term — and the
zeroth term is `h(P)` — giving `|canonicalHeight P - h(P)| ≤ (C / 4) / (1 - 1/4) = C / 3` with no
further work.

The `[DecidableEq F]` hypothesis is not incidental: `W.Point`'s `AddCommGroup` instance needs it,
since the addition formula case-splits on whether the two points share an `x`-coordinate. Without
it `2 ^ n • P` does not elaborate.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.9.
-/

public section

open Filter Height Topology

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [AdmissibleAbsValues F] [DecidableEq F]

/-- **The canonical (Néron–Tate) height** `canonicalHeight P = lim h(2ⁿ P) / 4ⁿ`.

The limit exists whenever the curve is elliptic
(`Point.tendsto_naiveHeight_two_pow_nsmul_div_four_pow`); the definition itself needs no hypothesis
beyond those making `2 ^ n • P` meaningful, so it is stated without one. -/
noncomputable def Point.canonicalHeight (P : W.Point) : ℝ :=
  limUnder atTop fun n : ℕ ↦ ((2 ^ n) • P).naiveHeight / 4 ^ n

variable (W) in
/-- The parallelogram law at `Q = P`: doubling multiplies the naïve height by `4` up to a bounded
error. The constant is nonnegative, which the geometric estimate below needs. -/
private theorem exists_abs_naiveHeight_two_nsmul_sub [W.toAffine.IsElliptic] :
    ∃ C, 0 ≤ C ∧ ∀ P : W.Point, |(2 • P).naiveHeight - 4 * P.naiveHeight| ≤ C := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  refine ⟨C, le_trans (abs_nonneg _) (hC 0 0), fun P ↦ ?_⟩
  have h := hC P P
  -- `P - P = 0` and `h 0 = 0`, so the law collapses to the doubling statement.
  rw [sub_self, Point.naiveHeight_zero] at h
  rw [two_nsmul]
  convert h using 2
  ring

/-- Consecutive terms of `h(2ⁿ P) / 4ⁿ` differ geometrically at ratio `1/4`. This is the single
estimate both results below run on. -/
private theorem dist_naiveHeight_div_succ_le [W.toAffine.IsElliptic] {C : ℝ}
    (hC : ∀ P : W.Point, |(2 • P).naiveHeight - 4 * P.naiveHeight| ≤ C) (P : W.Point) (n : ℕ) :
    dist (((2 ^ n) • P).naiveHeight / 4 ^ n) (((2 ^ (n + 1)) • P).naiveHeight / 4 ^ (n + 1))
      ≤ C / 4 * (1 / 4) ^ n := by
  have key : ((2 : ℕ) ^ (n + 1)) • P = 2 • (((2 : ℕ) ^ n) • P) := by
    rw [smul_smul]; congr 1; ring
  have e : ((2 : ℕ) ^ n • P).naiveHeight / 4 ^ n
        - ((2 : ℕ) ^ (n + 1) • P).naiveHeight / 4 ^ (n + 1)
      = (4 * ((2 : ℕ) ^ n • P).naiveHeight - (2 • ((2 : ℕ) ^ n • P)).naiveHeight)
          / 4 ^ (n + 1) := by
    rw [key]; field_simp [pow_succ]; ring
  rw [Real.dist_eq, e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ (n + 1)),
    div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ (n + 1))]
  have h := hC ((2 : ℕ) ^ n • P)
  rw [abs_sub_comm] at h
  calc |4 * ((2 : ℕ) ^ n • P).naiveHeight - (2 • ((2 : ℕ) ^ n • P)).naiveHeight| ≤ C := h
    _ = C / 4 * (1 / 4 : ℝ) ^ n * 4 ^ (n + 1) := by
        have h1 : ((1 : ℝ) / 4) ^ n * 4 ^ n = 1 := by rw [← mul_pow]; norm_num
        linear_combination (-C) * h1

/-- **The defining limit is attained.** `canonicalHeight` is `limUnder`, which returns a junk value
on a divergent sequence; this says the sequence converges, so the definition means what it says. -/
theorem Point.tendsto_naiveHeight_two_pow_nsmul_div_four_pow [W.toAffine.IsElliptic] (P : W.Point) :
    Tendsto (fun n : ℕ ↦ ((2 ^ n) • P).naiveHeight / 4 ^ n) atTop (𝓝 P.canonicalHeight) := by
  obtain ⟨C, _, hC⟩ := exists_abs_naiveHeight_two_nsmul_sub W
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 4) (C / 4) (by norm_num)
      (dist_naiveHeight_div_succ_le hC P))
  rwa [Point.canonicalHeight, ha.limUnder_eq]

/-- The point at infinity has canonical height zero: every term of the defining sequence is
`h 0 / 4 ^ n = 0`. -/
@[simp]
theorem Point.canonicalHeight_zero [W.toAffine.IsElliptic] :
    (0 : W.Point).canonicalHeight = 0 := by
  refine tendsto_nhds_unique (Point.tendsto_naiveHeight_two_pow_nsmul_div_four_pow 0) ?_
  simp

/-- Negation preserves the canonical height, because it preserves the naïve height and commutes
with doubling, so the two defining sequences agree termwise. -/
@[simp]
theorem Point.canonicalHeight_neg [W.toAffine.IsElliptic] (P : W.Point) :
    (-P).canonicalHeight = P.canonicalHeight := by
  refine tendsto_nhds_unique (Point.tendsto_naiveHeight_two_pow_nsmul_div_four_pow (-P)) ?_
  simpa only [smul_neg, Point.naiveHeight_neg] using
    Point.tendsto_naiveHeight_two_pow_nsmul_div_four_pow P

/-- **The canonical height differs from the naïve height by a bounded amount**, the bound depending
only on the curve. Northcott finiteness for `h` therefore transfers to the canonical height. -/
theorem Point.abs_canonicalHeight_sub_naiveHeight_le [W.toAffine.IsElliptic] :
    ∃ D, ∀ P : W.Point, |P.canonicalHeight - P.naiveHeight| ≤ D := by
  obtain ⟨C, _, hC⟩ := exists_abs_naiveHeight_two_nsmul_sub W
  refine ⟨C / 4 / (1 - 1 / 4), fun P ↦ ?_⟩
  have hd := dist_le_of_le_geometric_of_tendsto₀ (1 / 4) (C / 4) (by norm_num)
    (dist_naiveHeight_div_succ_le hC P) (P.tendsto_naiveHeight_two_pow_nsmul_div_four_pow)
  -- the zeroth term of the sequence is `h P` itself
  simpa [Real.dist_eq, abs_sub_comm] using hd

end WeierstrassCurve.Affine
