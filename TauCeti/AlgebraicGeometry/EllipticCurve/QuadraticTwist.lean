/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The quadratic twist of a Weierstrass curve: definition and invariants

The quadratic twist `E.quadraticTwistOf t n` of a Weierstrass curve by parameters `(t, n)` — to
be thought of as the trace and norm of a generator `θ` of a separable quadratic extension
`L/K`, with `D := t² - 4n` the discriminant of its minimal polynomial — together with the
behaviour of the standard invariants under twisting, uniformly in the characteristic: over any
commutative ring `b₂, b₄, b₆` scale by `D, D², D³`, `c₄, c₆` by `D², D³`, and `Δ` by `D⁶`, so
over a field the twist of an elliptic curve is elliptic when `D ≠ 0`, with the same
`j`-invariant. Twisting twice by `(t, n)`, or changing `(t, n)` to the trace and norm of
another generator, moves the twist by an explicit change of variables over the base field.

## Main definitions

* `WeierstrassCurve.quadraticTwistOf`: the quadratic twist of a Weierstrass curve by `(t, n)`,
  an explicit Weierstrass model over any commutative ring.
* `WeierstrassCurve.Δ_quadraticTwistOf`, `WeierstrassCurve.c₄_quadraticTwistOf`,
  `WeierstrassCurve.c₆_quadraticTwistOf`: the invariants of the twist.
* `WeierstrassCurve.isElliptic_quadraticTwistOf`, `WeierstrassCurve.j_quadraticTwistOf`: over a
  field, the twist of an elliptic curve is elliptic when `t² - 4n ≠ 0`, with equal `j`.
* `WeierstrassCurve.exists_smul_eq_quadraticTwistOf_quadraticTwistOf`,
  `WeierstrassCurve.exists_smul_quadraticTwistOf_eq`: the double twist is `K`-isomorphic to the
  original curve, and changing the generator moves the twist by a change of variables.

These are the `quadraticTwistOf` seeds of `TauCetiRoadmap/EllipticCurves/README.md` §Layer 5
(twists), pinned in that roadmap's `Suggested.lean`; the extension twist `quadraticTwist E L`
by a separable quadratic extension, the point isomorphism, and the split-multiplicative-
reduction theorem are later milestones of the same layer and build on this file.

Adapted from the FLT project's quadratic-twist development (`ImperialCollegeLondon/FLT`,
`FLT/KnownIn1980s/EllipticCurves/QuadraticTwists/QuadraticTwists.lean` at the roadmap's pin
`bc2fe8ff7396`, FLT PR #1088, Apache 2.0). That file's own header reads
`Authors: Kevin Buzzard, Claude`, and it has not been touched in FLT since `bc2fe8ff7396`, so
the pin and the working clone (`d18b563029f3`, a later Mathlib bump) agree on it verbatim.
Following this repository's convention for adapted material, the upstream authorship is
credited here rather than in the copyright header.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.§10, X.§2 and X.§5
-/

public section

namespace WeierstrassCurve

section QuadraticTwistOfRing

variable {A : Type*} [CommRing A] (E : WeierstrassCurve A)

/-- The quadratic twist of a Weierstrass curve `E` over `K` by parameters `t`, `n`, to be
thought of as the trace and norm of a generator `θ` of a separable quadratic extension `L/K`
(so that `θ² = tθ - n`, and `D := t² - 4n` is the discriminant of the minimal polynomial of
`θ`, nonzero exactly when `θ` is separable).

The construction: writing the equation of `E` as `y² + A(x)y = f(x)` with `A(x) = a₁x + a₃`,
the functions `x` and `Y := (t - 2θ)y - θ·A(x)` on `E` are invariant under the Galois action
twisted by the quadratic character of `L/K`, and satisfy
`Y² + t·A(x)·Y = D·(y² + A(x)y) - n·A(x)²`; clearing denominators via `(x, Y) ↦ (Dx, DY)`
turns this relation into the Weierstrass model below of the twist:

`y² + ta₁·xy + Dta₃·y = x³ + (Da₂ - na₁²)·x² + (D²a₄ - 2Dna₁a₃)·x + (D³a₆ - D²na₃²)`.

Its discriminant is `D⁶·Δ(E)` (`Δ_quadraticTwistOf`), so the twist of an elliptic curve is
elliptic when `D ≠ 0` (`isElliptic_quadraticTwistOf`), with the same `j`-invariant
(`j_quadraticTwistOf`).

Sanity checks. If `char K ≠ 2` we may take `θ = √d`, so `t = 0`, `n = -d`, `D = 4d`; for
`E : y² = x³ + a₂x² + a₄x + a₆` the model is `y² = x³ + 4da₂x² + 16d²a₄x + 64d³a₆`, the
classical twist by `4d ≡ d mod (K^×)²`. If `char K = 2` we may take `θ` with `θ² + θ = d`
(Artin–Schreier), so `t = 1`, `n = -d`, `D = 1`; for ordinary `E : y² + xy = x³ + a₂x² + a₆`
the model is the classical twist `y² + xy = x³ + (a₂ + d)x² + a₆`, and for supersingular
`E : y² + a₃y = x³ + a₄x + a₆` it is `y² + a₃y = x³ + a₄x + (a₆ + da₃²)`. -/
def quadraticTwistOf (t n : A) : WeierstrassCurve A where
  a₁ := t * E.a₁
  a₂ := (t ^ 2 - 4 * n) * E.a₂ - n * E.a₁ ^ 2
  a₃ := (t ^ 2 - 4 * n) * t * E.a₃
  a₄ := (t ^ 2 - 4 * n) ^ 2 * E.a₄ - 2 * (t ^ 2 - 4 * n) * n * E.a₁ * E.a₃
  a₆ := (t ^ 2 - 4 * n) ^ 3 * E.a₆ - (t ^ 2 - 4 * n) ^ 2 * n * E.a₃ ^ 2

variable (t n : A)

/-- The coefficient `a₁` of the quadratic twist. -/
@[simp] theorem a₁_quadraticTwistOf : (E.quadraticTwistOf t n).a₁ = t * E.a₁ := by
  simp only [quadraticTwistOf]

/-- The coefficient `a₂` of the quadratic twist. -/
@[simp] theorem a₂_quadraticTwistOf :
    (E.quadraticTwistOf t n).a₂ = (t ^ 2 - 4 * n) * E.a₂ - n * E.a₁ ^ 2 := by
  simp only [quadraticTwistOf]

/-- The coefficient `a₃` of the quadratic twist. -/
@[simp] theorem a₃_quadraticTwistOf :
    (E.quadraticTwistOf t n).a₃ = (t ^ 2 - 4 * n) * t * E.a₃ := by
  simp only [quadraticTwistOf]

/-- The coefficient `a₄` of the quadratic twist. -/
@[simp] theorem a₄_quadraticTwistOf :
    (E.quadraticTwistOf t n).a₄
      = (t ^ 2 - 4 * n) ^ 2 * E.a₄ - 2 * (t ^ 2 - 4 * n) * n * E.a₁ * E.a₃ := by
  simp only [quadraticTwistOf]

/-- The coefficient `a₆` of the quadratic twist. -/
@[simp] theorem a₆_quadraticTwistOf :
    (E.quadraticTwistOf t n).a₆
      = (t ^ 2 - 4 * n) ^ 3 * E.a₆ - (t ^ 2 - 4 * n) ^ 2 * n * E.a₃ ^ 2 := by
  simp only [quadraticTwistOf]

/-- The invariant `b₂` of the quadratic twist: `b₂ ↦ Db₂` with `D = t² - 4n`. -/
@[simp] theorem b₂_quadraticTwistOf : (E.quadraticTwistOf t n).b₂ = (t ^ 2 - 4 * n) * E.b₂ := by
  simp only [quadraticTwistOf, b₂]; ring

/-- The invariant `b₄` of the quadratic twist: `b₄ ↦ D²b₄` with `D = t² - 4n`. -/
@[simp] theorem b₄_quadraticTwistOf : (E.quadraticTwistOf t n).b₄ = (t ^ 2 - 4 * n) ^ 2 * E.b₄ := by
  simp only [quadraticTwistOf, b₄]; ring

/-- The invariant `b₆` of the quadratic twist: `b₆ ↦ D³b₆` with `D = t² - 4n`. -/
@[simp] theorem b₆_quadraticTwistOf : (E.quadraticTwistOf t n).b₆ = (t ^ 2 - 4 * n) ^ 3 * E.b₆ := by
  simp only [quadraticTwistOf, b₆]; ring

/-- The invariant `b₈` of the quadratic twist: `b₈ ↦ D⁴b₈` with `D = t² - 4n`. -/
@[simp] theorem b₈_quadraticTwistOf : (E.quadraticTwistOf t n).b₈ = (t ^ 2 - 4 * n) ^ 4 * E.b₈ := by
  simp only [quadraticTwistOf, b₈]; ring

/-- The invariant `c₄` of the quadratic twist: `c₄ ↦ D²c₄` with `D = t² - 4n`. Immediate from
the `b₂` and `b₄` laws, since `c₄ = b₂² - 24b₄`. -/
@[simp] theorem c₄_quadraticTwistOf : (E.quadraticTwistOf t n).c₄ = (t ^ 2 - 4 * n) ^ 2 * E.c₄ := by
  simp only [c₄, b₂_quadraticTwistOf, b₄_quadraticTwistOf]
  ring

/-- The invariant `c₆` of the quadratic twist: `c₆ ↦ D³c₆` with `D = t² - 4n`. Immediate from
the `b₂`, `b₄` and `b₆` laws, since `c₆ = -b₂³ + 36b₂b₄ - 216b₆`. -/
@[simp] theorem c₆_quadraticTwistOf : (E.quadraticTwistOf t n).c₆ = (t ^ 2 - 4 * n) ^ 3 * E.c₆ := by
  simp only [c₆, b₂_quadraticTwistOf, b₄_quadraticTwistOf, b₆_quadraticTwistOf]
  ring

/-- The discriminant of the quadratic twist: `Δ ↦ D⁶Δ` with `D = t² - 4n`. Immediate from the
`b`-laws, since `Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆`. -/
@[simp] theorem Δ_quadraticTwistOf : (E.quadraticTwistOf t n).Δ = (t ^ 2 - 4 * n) ^ 6 * E.Δ := by
  simp only [Δ, b₂_quadraticTwistOf, b₄_quadraticTwistOf, b₆_quadraticTwistOf,
    b₈_quadraticTwistOf]
  ring

/-- The quadratic twist commutes with a ring homomorphism `f` (in particular with base change):
`(E.quadraticTwistOf t n).map f = (E.map f).quadraticTwistOf (f t) (f n)`. -/
@[simp] theorem quadraticTwistOf_map {B : Type*} [CommRing B] (f : A →+* B) :
    (E.quadraticTwistOf t n).map f = (E.map f).quadraticTwistOf (f t) (f n) := by
  ext <;>
    simp only [quadraticTwistOf, map_a₁, map_a₂,
      map_a₃, map_a₄, map_a₆, map_mul, map_sub,
      map_pow, map_ofNat]

/-- The constant term `54 b₆ - 3 b₂ b₄ + a₂ c₄` of the quadratic twist by `(t, n)`, in terms of
that of `E`: it becomes `D³ · (54 b₆ - 3 b₂ b₄ + a₂ c₄) - D² n a₁² c₄` where `D = t² - 4n`.

This is the constant term of the polynomial `c₄T² + a₁c₄T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)` whose
splitting characterises split multiplicative reduction (Mathlib's
`WeierstrassCurve.HasSplitMultiplicativeReduction`), and which arises from the second-order
Taylor expansion of the equation at the node. It is consumed by the twist-to-split-reduction
theorem, a later milestone of the same roadmap layer. -/
theorem nodeConst_quadraticTwistOf :
    54 * (E.quadraticTwistOf t n).b₆
      - 3 * (E.quadraticTwistOf t n).b₂ * (E.quadraticTwistOf t n).b₄
      + (E.quadraticTwistOf t n).a₂ * (E.quadraticTwistOf t n).c₄
      = (t ^ 2 - 4 * n) ^ 3 * (54 * E.b₆ - 3 * E.b₂ * E.b₄ + E.a₂ * E.c₄)
        - (t ^ 2 - 4 * n) ^ 2 * n * E.a₁ ^ 2 * E.c₄ := by
  rw [b₆_quadraticTwistOf, b₂_quadraticTwistOf, b₄_quadraticTwistOf, c₄_quadraticTwistOf,
    a₂_quadraticTwistOf]
  ring

/-- The quadratic twist of an elliptic curve is elliptic when the discriminant `D = t² - 4n` of
the twisting parameters is a unit, since `Δ ↦ D⁶Δ`. Over a field this hypothesis is `D ≠ 0`
(`isUnit_iff_ne_zero`), the form in which the source states it; over a general commutative ring
`D ≠ 0` is not enough, since `D⁶ · unit` is a unit only when `D` is (take `A = ℤ`, `D = 2`). -/
theorem isElliptic_quadraticTwistOf [E.IsElliptic] (hD : IsUnit (t ^ 2 - 4 * n)) :
    (E.quadraticTwistOf t n).IsElliptic := by
  rw [isElliptic_iff, Δ_quadraticTwistOf]
  exact (hD.pow 6).mul E.isUnit_Δ

/-- The `j`-invariant is a twist invariant: `j(E_{t,n}) = j(E)`. Both `j`s are `Δ'⁻¹c₄³`, and the
twist scales `Δ` by `D⁶` and `c₄` by `D²`, so the two `D`-powers cancel against each other. -/
theorem j_quadraticTwistOf [E.IsElliptic] (h : (E.quadraticTwistOf t n).IsElliptic) :
    (E.quadraticTwistOf t n).j = E.j := by
  have hΔ : E.Δ * ((E.Δ'⁻¹ : Aˣ) : A) = 1 := by
    rw [← coe_Δ']
    exact E.Δ'.mul_inv
  rw [j, j, Units.inv_mul_eq_iff_eq_mul, c₄_quadraticTwistOf, coe_Δ', Δ_quadraticTwistOf]
  linear_combination (-((t ^ 2 - 4 * n) ^ 6 * E.c₄ ^ 3)) * hΔ

end QuadraticTwistOfRing

section QuadraticTwistOf

variable {K : Type*} [Field K] (E : WeierstrassCurve K) (t n : K)

/-- Twisting twice by the same parameters `(t, n)` gives a curve isomorphic to `E` over `K`:
explicitly, the double twist is obtained from `E` by the change of variables
`(x, y) ↦ (D²x, D³y - 2nD²(a₁x + a₃))`, where `D = t² - 4n`. -/
theorem exists_smul_eq_quadraticTwistOf_quadraticTwistOf (hD : t ^ 2 - 4 * n ≠ 0) :
    ∃ C : VariableChange K, C • E = (E.quadraticTwistOf t n).quadraticTwistOf t n := by
  refine ⟨⟨(Units.mk0 _ hD)⁻¹, 0, 2 * n / (t ^ 2 - 4 * n) * E.a₁,
    2 * n / (t ^ 2 - 4 * n) * E.a₃⟩, ?_⟩
  rw [variableChange_def]
  ext <;> simp only [quadraticTwistOf, inv_inv, Units.val_mk0] <;> field

/-- Changing the parameters `(t, n)` — the trace and norm of a generator `θ` of a quadratic
extension — into the trace and norm `(at + 2b, b² + abt + a²n)` of another generator `aθ + b`
changes the quadratic twist by an explicit change of variables over `K`. -/
theorem exists_smul_quadraticTwistOf_eq {a : K} (b : K) (ha : a ≠ 0) :
    ∃ C : VariableChange K, C • E.quadraticTwistOf t n
      = E.quadraticTwistOf (a * t + 2 * b) (b ^ 2 + a * b * t + a ^ 2 * n) := by
  refine ⟨⟨(Units.mk0 a ha)⁻¹, 0, a⁻¹ * b * E.a₁, a⁻¹ * b * (t ^ 2 - 4 * n) * E.a₃⟩, ?_⟩
  rw [variableChange_def]
  ext <;> simp only [quadraticTwistOf, inv_inv, Units.val_mk0] <;> field

end QuadraticTwistOf

end WeierstrassCurve

end
