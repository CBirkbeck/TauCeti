/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Non-negativity of a binary quadratic form and its discriminant

Mathlib's `discrim_le_zero` shows that a quadratic *polynomial* over a linearly ordered field
which is non-negative at every point of the field has non-positive discriminant. This file
supplies two facts about the homogeneous two-variable form `a * x ^ 2 + b * x * y + c * y ^ 2`
that `discrim_le_zero` does not give.

* `nonneg_of_discrim_le_zero` is the reverse implication, over a linearly ordered commutative
  ring rather than a field: a positive leading coefficient together with a non-positive
  discriminant makes the form non-negative. The proof is the completed square
  `4a·Q = (2ax + by)² + (4ac − b²)y²`, which uses no division, so `Field` is not needed.
* `Int.discrim_le_zero_of_nonneg_of_lt_abs` runs the other way over `ℤ`, and needs far less
  than non-negativity everywhere: it is enough to test the form along a **single** line
  `y = y₀`, provided `|y₀|` exceeds the leading coefficient. Integrality is what makes so weak
  a hypothesis sufficient — over `ℚ` or `ℝ` one line says nothing about the discriminant.

Together the two give the upgrade that motivates the file: a form known to be non-negative only
on some sparse set of `(x, y)` — for instance the sublattice where a fixed prime does not divide
`y`, which is all that the degree form on an elliptic curve is directly known to satisfy — is
non-negative on all of `ℤ ⨯ ℤ`. Any single `y₀` from that set with `|y₀|` large enough feeds
`Int.discrim_le_zero_of_nonneg_of_lt_abs`, and `nonneg_of_discrim_le_zero` then propagates the
conclusion to every `(x, y)`.

## Main results

* `Int.exists_two_mul_abs_sub_mul_le`: every integer lies within `m / 2` of a multiple of `m`.
* `nonneg_of_discrim_le_zero`: `0 < a` and `discrim a b c ≤ 0` give `0 ≤ a x² + b x y + c y²`.
* `Int.discrim_le_zero_of_nonneg_of_lt_abs`: for `0 < a` and `a < |y|`, non-negativity of
  `a x² + b x y + c y²` in `x` alone forces `discrim a b c ≤ 0`.
* `Int.discrim_le_zero_of_nonneg_of_not_dvd`: the same conclusion from non-negativity on the
  sublattice complement `{(x, y) : d ∤ y}`, for any `d` with `1 < |d|`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, V.1.1, where positivity of the degree form on
  a rank-two lattice is turned into the Hasse inequality by exactly this discriminant argument.
-/

public section

/-- **Nearest multiple.** For a positive modulus `m`, every integer `a` lies within `m / 2` of a
multiple of `m`, stated division-free as `2 * |a - m * r| ≤ m`. -/
theorem Int.exists_two_mul_abs_sub_mul_le {m : ℤ} (hm : 0 < m) (a : ℤ) :
    ∃ r : ℤ, 2 * |a - m * r| ≤ m := by
  have hm2 : (0 : ℤ) < 2 * m := by linarith
  refine ⟨(2 * a + m) / (2 * m), ?_⟩
  have h0 : 0 ≤ (2 * a + m) % (2 * m) := Int.emod_nonneg _ (ne_of_gt hm2)
  have h1 : (2 * a + m) % (2 * m) < 2 * m := Int.emod_lt_of_pos _ hm2
  have hd : (2 * a + m) % (2 * m) + 2 * m * ((2 * a + m) / (2 * m)) = 2 * a + m :=
    Int.emod_add_mul_ediv (2 * a + m) (2 * m)
  have habs : 2 * |a - m * ((2 * a + m) / (2 * m))|
      = |2 * (a - m * ((2 * a + m) / (2 * m)))| := by
    rw [abs_mul]; norm_num
  rw [habs, abs_le]
  constructor <;> linarith

/-- A binary quadratic form with positive leading coefficient and non-positive discriminant is
non-negative. This is the implication opposite to Mathlib's `discrim_le_zero`, stated for the
homogeneous two-variable form; the completed square `4a·Q = (2ax + by)² + (4ac − b²)y²` uses no
division, so a linearly ordered commutative ring suffices in place of a field. -/
theorem nonneg_of_discrim_le_zero {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {a b c : R} (ha : 0 < a) (hd : discrim a b c ≤ 0) (x y : R) :
    0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  have hb : 0 ≤ 4 * a * c - b ^ 2 := by rw [discrim] at hd; linarith
  nlinarith [sq_nonneg (2 * a * x + b * y), mul_nonneg hb (sq_nonneg y)]

/-- **One line of large enough height already pins the discriminant.** If a binary quadratic
form over `ℤ` with positive leading coefficient `a` is non-negative at `(x, y)` for a *fixed*
`y` with `a < |y|` and every `x`, then its discriminant is non-positive, `b ^ 2 ≤ 4 * a * c`.

Testing one line is enough only because the variable `x` ranges over `ℤ` and not over a field:
the argument picks the integer `x` nearest to the minimum of `x ↦ a x² + b x y + c y²`, where
the completed square `4a·Q = (2ax + by)² + (4ac − b²)y²` has `(2ax + by)² ≤ a ^ 2`, so a positive
discriminant would give `4a·Q ≤ a ^ 2 - y ^ 2 < 0`. Over `ℚ` or `ℝ` the nearest point is the
exact minimum and a single line carries no information about the discriminant at all.

Consequently a form known to be non-negative only on `{(x, y) : ¬ d ∣ y}`, for some fixed `d`,
still has non-positive discriminant: any single `y` avoiding `d` with `a < |y|` — such as
`y = a * d ^ 2 + 1` when `1 < |d|` — may be used here. -/
theorem Int.discrim_le_zero_of_nonneg_of_lt_abs {a b c y : ℤ} (ha : 0 < a) (hy : a < |y|)
    (h : ∀ x : ℤ, 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2) : discrim a b c ≤ 0 := by
  by_contra! hcon
  rw [discrim] at hcon
  -- Pick `x` nearest to the minimum of the form along the line, so that `|2ax + by| ≤ a`.
  obtain ⟨x, hx⟩ := Int.exists_two_mul_abs_sub_mul_le (by linarith : (0 : ℤ) < 2 * a) (-(b * y))
  have hxa : |2 * a * x + b * y| ≤ a := by
    rw [show 2 * a * x + b * y = -(-(b * y) - 2 * a * x) by ring, abs_neg]
    linarith [hx]
  have hsq : (2 * a * x + b * y) ^ 2 ≤ a ^ 2 := by
    have habs := abs_le.mp hxa
    nlinarith [habs.1, habs.2]
  -- `a < |y|` makes the `(4ac − b²)y²` term outweigh it, so the form is negative at `(x, y)`.
  have hy2 : a ^ 2 < y ^ 2 := by
    have := abs_nonneg y
    nlinarith [sq_abs y]
  have hkey : 4 * a * (a * x ^ 2 + b * x * y + c * y ^ 2)
      = (2 * a * x + b * y) ^ 2 + (4 * a * c - b ^ 2) * y ^ 2 := by ring
  nlinarith [h x, hsq, hy2, hkey]

/-- **A sublattice already pins the discriminant.** If a binary quadratic form over `ℤ` with
positive leading coefficient is non-negative at every `(x, y)` whose second coordinate avoids
the multiples of some `d` with `1 < |d|` — in the intended application `d` is a prime, and the
locus is the sublattice complement `{(x, y) : d ∤ y}` — then its discriminant is non-positive.

This is `Int.discrim_le_zero_of_nonneg_of_lt_abs` fed the witness `y = a * d ^ 2 + 1`, which
avoids `d` and is larger than `a`. It does **not** follow from Mathlib's `discrim_le_zero`,
whose hypothesis is non-negativity at every point of a field. -/
theorem Int.discrim_le_zero_of_nonneg_of_not_dvd {a b c d : ℤ} (ha : 0 < a) (hd : 1 < |d|)
    (h : ∀ x y : ℤ, ¬ d ∣ y → 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2) : discrim a b c ≤ 0 := by
  have hnd : ¬ d ∣ a * d ^ 2 + 1 := fun hc => by
    have hd1 : d ∣ (1 : ℤ) := (dvd_add_right (Dvd.intro (a * d) (by ring))).mp hc
    exact absurd (Int.le_of_dvd one_pos ((abs_dvd d 1).mpr hd1)) (by omega)
  refine Int.discrim_le_zero_of_nonneg_of_lt_abs ha (y := a * d ^ 2 + 1) ?_ fun x => h x _ hnd
  have hd2 : 1 ≤ d ^ 2 := by nlinarith [sq_abs d, abs_nonneg d]
  rw [abs_of_pos (by nlinarith)]
  nlinarith
