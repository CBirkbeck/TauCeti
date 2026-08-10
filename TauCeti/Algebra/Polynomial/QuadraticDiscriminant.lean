/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.FieldTheory.Separable

/-!
# Separability and splitting criteria for quadratic polynomials

Mathlib's `Mathlib/Algebra/QuadraticDiscriminant.lean` works with the *equation*
`a x² + b x + c = 0` and relates its solutions to the discriminant `b² - 4 a c`. This file reads
those facts back as statements about the *polynomial* `C a * X ^ 2 + C b * X + C c` over a field,
where `a ≠ 0`:

* `Polynomial.separable_quadratic_iff`: it is separable exactly when the discriminant is nonzero.
  The engine is the Bézout-type identity `Polynomial.sq_derivative_quadratic_sub_mul`,
  `(P')² - 4 a P = C (b² - 4 a c)`, which exhibits a nonzero discriminant as a coprimality witness
  in every characteristic;
* `Polynomial.splits_quadratic_iff_exists_root`: it splits exactly when it has a root — the
  characteristic-free core, and the only one of the three that says nothing about the
  discriminant. Both directions are Mathlib's `Splits.exists_eval_eq_zero` and
  `Splits.of_natDegree_eq_two`;
* `Polynomial.splits_quadratic_iff`: away from characteristic two, it splits exactly when the
  discriminant is a square;
* `Polynomial.splits_quadratic_iff_of_two_eq_zero`: in characteristic two, where the discriminant
  degenerates to `b²` and the square-class criterion says nothing, it splits exactly when the
  Artin-Schreier invariant `a c / b²` lies in the image of `z ↦ z² + z`, written division-free.

The two splitting criteria are consumed by the node-polynomial criteria of
`TauCeti/AlgebraicGeometry/EllipticCurve/NodePolynomial.lean`, which advance
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 5 (twists): whether the node polynomial of a
multiplicative reduction splits over the residue field is exactly whether that reduction is split.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/Algebra/Polynomial/QuadraticDiscriminant.lean` at the roadmap's pin `bc2fe8ff7396`,
FLT PR #1088, Apache 2.0). That file's own header reads `Authors: Kevin Buzzard, Claude`;
following this repository's convention for adapted material, the upstream authorship is credited
here rather than in the copyright header. Ported with the source's `@[expose]` dropped, and
without its companion `FLT/Mathlib/Algebra/Polynomial/Splits.lean`: that file's
`Splits.of_natDegree_le_two_of_isRoot` is superseded here by Mathlib's own
`Polynomial.Splits.of_natDegree_eq_two`, which the one consumer can use directly since it knows
the degree is exactly two.
-/

public section

namespace Polynomial

/-- The derivative of the quadratic `a X² + b X + c` is `2 a X + b`. -/
theorem derivative_quadratic {R : Type*} [CommSemiring R] (a b c : R) :
    derivative (C a * X ^ 2 + C b * X + C c) = 2 * C a * X + C b := by
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X_pow, derivative_X,
    zero_mul, zero_add, mul_one, add_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one, map_ofNat]
  ring

/-- The Bézout-type identity `(P')² - 4 a · P = C (b² - 4 a c)` for the quadratic
`P = a X² + b X + c`: the discriminant is an explicit `R[X]`-combination of `P` and its
derivative, which is what makes it a coprimality witness in `separable_quadratic_iff`. -/
theorem sq_derivative_quadratic_sub_mul {R : Type*} [CommRing R] (a b c : R) :
    derivative (C a * X ^ 2 + C b * X + C c) ^ 2
      - 4 * C a * (C a * X ^ 2 + C b * X + C c) = C (b ^ 2 - 4 * a * c) := by
  rw [derivative_quadratic]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- A quadratic polynomial `a X² + b X + c` (with `a ≠ 0`) over a field is separable exactly when
its discriminant `b² - 4 a c` is nonzero. The `←` direction holds in every characteristic: by the
Bézout identity `sq_derivative_quadratic_sub_mul`, a nonzero — hence invertible — discriminant
exhibits `P` and `P'` as coprime. The `→` direction argues that if the discriminant vanishes then
`P ∣ (P')²`, forcing the coprimality witness `P` to be a unit, contradicting `deg P = 2`. -/
theorem separable_quadratic_iff {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Separable ↔ b ^ 2 - 4 * a * c ≠ 0 := by
  set P := C a * X ^ 2 + C b * X + C c with hP
  have hid : derivative P ^ 2 - 4 * C a * P = C (b ^ 2 - 4 * a * c) :=
    sq_derivative_quadratic_sub_mul a b c
  constructor
  · intro hsep hdisc
    rw [hdisc, map_zero] at hid
    have hdvd : P ∣ derivative P ^ 2 := ⟨4 * C a, by linear_combination hid⟩
    exact not_isUnit_of_natDegree_pos P (by rw [hP, natDegree_quadratic ha]; norm_num)
      (((separable_def P).mp hsep).pow_right.isUnit_of_dvd' dvd_rfl hdvd)
  · intro hdisc
    rw [separable_def]
    have hdinv : C (b ^ 2 - 4 * a * c)⁻¹ * C (b ^ 2 - 4 * a * c) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hdisc, C_1]
    exact ⟨-(C (b ^ 2 - 4 * a * c)⁻¹ * 4 * C a), C (b ^ 2 - 4 * a * c)⁻¹ * derivative P,
      by linear_combination C (b ^ 2 - 4 * a * c)⁻¹ * hid + hdinv⟩

/-- A quadratic `a X² + b X + c` (`a ≠ 0`) over a field splits exactly when it has a root. Both
directions are Mathlib's: `Splits.exists_eval_eq_zero` extracts a root from a splitting of
positive degree, and `Splits.of_natDegree_eq_two` builds the splitting back from one. This is the
characteristic-free core of the two split criteria below, neither of which adds anything beyond
restating "has a root" in terms of the discriminant. -/
theorem splits_quadratic_iff_exists_root {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ ∃ x, a * x ^ 2 + b * x + c = 0 := by
  set p := C a * X ^ 2 + C b * X + C c with hp
  have hdeg : p.natDegree = 2 := natDegree_quadratic ha
  have hp0 : p ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hdeg; omega
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero (by
      simp only [degree_eq_natDegree hp0, hdeg, ne_eq, Nat.cast_ofNat, OfNat.ofNat_ne_zero,
        not_false_eq_true])
    refine ⟨x, ?_⟩
    simp only [hp, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hx
    linear_combination hx
  · rintro ⟨x, hx⟩
    refine Splits.of_natDegree_eq_two hdeg (x := x) ?_
    simp only [hp, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination hx

/-- Over a field of characteristic `≠ 2`, a quadratic `a X² + b X + c` (with `a ≠ 0`) *splits*
exactly when its discriminant `b² - 4 a c` is a square: it splits iff it has a root
(`splits_quadratic_iff_exists_root`), and completing the square
(`discrim_eq_sq_of_quadratic_eq_zero`, `exists_quadratic_eq_zero`) matches roots with square roots
of the discriminant. Compare `separable_quadratic_iff`, which asks for the discriminant to be
nonzero rather than square. -/
theorem splits_quadratic_iff {k : Type*} [Field k] [NeZero (2 : k)] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ IsSquare (discrim a b c) := by
  rw [splits_quadratic_iff_exists_root ha]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨2 * a * x + b, by rw [discrim_eq_sq_of_quadratic_eq_zero (a := a) (b := b) (c := c)
      (x := x) (by linear_combination hx)]; ring⟩
  · rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha ⟨s, by rw [hs]⟩
    exact ⟨x, by linear_combination hx⟩

/-- Over a field of characteristic `2`, a quadratic `a X² + b X + c` with `a, b ≠ 0` splits
exactly when its Artin-Schreier invariant `a c / b²` lies in the image of `z ↦ z² + z`, written
division-free as `∃ z, b² (z² + z) = a c`; substitute `z = a x / b` in a root `x`. Here the
square-class criterion `splits_quadratic_iff` says nothing, since `b² - 4 a c = b²` is
automatically a square; the hypothesis `b ≠ 0` is exactly separability, by
`separable_quadratic_iff`. -/
theorem splits_quadratic_iff_of_two_eq_zero {k : Type*} [Field k] (h2 : (2 : k) = 0)
    {a b c : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ ∃ z, b ^ 2 * (z ^ 2 + z) = a * c := by
  rw [splits_quadratic_iff_exists_root ha]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨a * x / b, ?_⟩
    field_simp
    linear_combination hx - c * h2
  · rintro ⟨z, hz⟩
    refine ⟨b * z / a, ?_⟩
    field_simp
    linear_combination hz + a * c * h2

end Polynomial

end
