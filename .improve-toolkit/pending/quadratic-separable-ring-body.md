`Polynomial.separable_quadratic_iff_discrim_ne_zero` is stated over a field with `a ≠ 0`, but its reverse direction uses neither assumption. It inverts the discriminant in the Bézout-type identity `sq_derivative_quadratic_sub_mul_eq_C_discrim`, `(P')² - 4 a P = C (discrim a b c)`. This PR states that direction at its natural generality:

```lean
theorem Polynomial.separable_quadratic_of_isUnit_discrim {R : Type*} [CommRing R] {a b c : R}
    (h : IsUnit (discrim a b c)) : (C a * X ^ 2 + C b * X + C c).Separable
```

The proof is the one the field lemma already used, with the field inverse replaced by `h.unit⁻¹`. The field lemma now takes its reverse direction from the new lemma, via `isUnit_iff_ne_zero`.

This direction needs no hypothesis on `a`. The converse does: over `ℚ[t]`, `1 + t X²` is separable, since `P - (X/2) P' = 1`, but its discriminant `-4t` is not a unit. At the pinned version, Mathlib has no criterion relating the separability of a quadratic polynomial to its discriminant. Its closest lemma, `Polynomial.separable_C_mul_X_pow_add_C_mul_X_add_C`, needs `(n : R) = 0` and `IsUnit b`.

Also in this PR:

* `discrim_eq_sq_of_two_eq_zero` inlines its single-use `have (4 : R) = 0`; the proof is now `linear_combination (-2 * a * c) * h2`.
* The module docstring and the docstrings of `sq_derivative_quadratic_sub_mul_eq_C_discrim` and `separable_quadratic_iff_discrim_ne_zero` now point at the new lemma.

No declaration is removed or renamed, and no existing statement changes. The file's only consumer, `EllipticCurve/NodePolynomial.lean`, is untouched.

Roadmap: none

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01Uud3dXqKRLcZcMgZYsDCmQ
