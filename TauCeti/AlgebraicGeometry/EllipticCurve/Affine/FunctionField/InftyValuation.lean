/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.RatFunc.Valuation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Norm

/-!
# The valuation at infinity on the function field of a Weierstrass curve

The function field `F(W)` of an affine Weierstrass curve is a quadratic extension of the rational
function field `F(x)` (`WeierstrassCurve.Affine.finrank_functionField`), so every function has an
algebra norm there. Composing that norm with Mathlib's place at infinity of `F(x)` gives the place
at infinity of the curve: `ord_∞ f = -deg N f`, the place where `x` and `y` have their poles.

## Main definitions

* `WeierstrassCurve.Affine.inftyValuation`: the valuation at infinity,
  `Valuation W.FunctionField (WithZero (Multiplicative ℤ))`, as `RatFunc.inftyValuation` composed
  with `Algebra.norm`.

## Main results

* `WeierstrassCurve.Affine.intDegree_norm_add_le`: the ultrametric inequality in degree form, which
  is what `inftyValuation`'s `map_add_le_max'` rests on. The other three valuation axioms are the
  norm's multiplicativity and Mathlib's place at infinity.
* `WeierstrassCurve.Affine.intDegree_norm_eq_max`: for `a`, `b` and `p` all nonzero, the degree of
  the norm of `(a + by)/p` is
  `max (2 deg a) (2 deg b + 3) - 2 deg p`.
* `WeierstrassCurve.Affine.inftyValuation_X`,
  `WeierstrassCurve.Affine.inftyValuation_mk_Y`: `v_∞ x = exp 2` and `v_∞ y = exp 3` —
  the double and triple poles at infinity, `ord_∞ x = -2` and `ord_∞ y = -3`, which is what Layer 0
  asks for by name. They read the norm degrees of `FunctionField/Norm.lean` through the valuation.

Only `inftyValuation`, its `apply` lemma, the two pole values and the two degree statements are
public; everything else in the file is scaffolding for the ultrametric inequality and is `private`.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors),
whose §Places asks for the one further place `W.infinityPlace` beyond the affine ones, sitting
"where `x` and `y` have their poles", with `ord_∞ x = -2`, `ord_∞ y = -3`. This file supplies the
valuation and those two degrees; `Suggested.lean` seeds no declaration it competes with, recording
that the function-field layer's "types are new API and are built there, not pinned here".

## Provenance

The route is that of the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`dev/hasse-weil` at `a582951fe96b`), `HasseWeil/Curves/Infinity.lean`: `normAsRatFunc`,
`ordAtInfty`, `ordAtInfty_mul`, `ordAtInfty_add_ge_min` (tagged T-ORD-ARITH-12) and
`ordAtInfty_coordX`/`ordAtInfty_coordY`.

Changes from the source. There `ordAtInfty` is a definition of its own, valued in `WithTop ℤ`, built
over a `SmoothPlaneCurve` structure wrapping `WeierstrassCurve.Affine`, with multiplicativity,
vanishing and the ultrametric bound all proved by hand. Here the norm is Mathlib's `Algebra.norm`
and the target is Mathlib's `ℤᵐ⁰`, so the result is a genuine `Valuation` uniform with
`RatFunc.inftyValuation` and `IsDedekindDomain.HeightOneSpectrum.valuation`; multiplicativity and
vanishing are `map_mul` and `Algebra.norm_eq_zero_iff`, and only the ultrametric inequality is
reproved.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate RatFunc

namespace WeierstrassCurve.Affine


variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

private theorem norm_algebraMap_polynomial' (d : F[X]) :
    Algebra.norm (RatFunc F) (algebraMap F[X] W.FunctionField d) =
      (algebraMap F[X] (RatFunc F) d) ^ 2 := by
  rw [IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField, Algebra.norm_algebraMap,
    finrank_functionField W (RatFunc F)]

/-- **The degree of the norm of `u / d`**: the polynomial norm's degree, less twice that of the
denominator. Stated for an arbitrary numerator `u` in the coordinate ring, so it carries no
hypothesis on the basis coefficients — they may vanish. `intDegree_norm_eq_max` specialises it to
`u = a • 1 + b • y`, where the `max` form needs `a` and `b` nonzero. -/
theorem intDegree_norm_of_mul_eq {f : W.FunctionField} (hf : f ≠ 0) {u : W.CoordinateRing}
    {d : F[X]} (hd : d ≠ 0)
    (h : f * algebraMap F[X] W.FunctionField d = algebraMap W.CoordinateRing W.FunctionField u) :
    (Algebra.norm (RatFunc F) f).intDegree
      = (Algebra.norm F[X] u).natDegree - 2 * d.natDegree := by
  have hNf : Algebra.norm (RatFunc F) f ≠ 0 :=
    fun hz => hf ((Algebra.norm_eq_zero_iff (R := RatFunc F)).mp hz)
  have hdR : algebraMap F[X] (RatFunc F) d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have hnorm := congrArg (Algebra.norm (RatFunc F)) h
  rw [map_mul, norm_algebraMap_polynomial',
    Algebra.norm_localization (R := F[X]) (M := nonZeroDivisors F[X])
      (S := W.CoordinateRing)] at hnorm
  have := congrArg RatFunc.intDegree hnorm
  rw [RatFunc.intDegree_mul hNf (pow_ne_zero _ hdR), ← map_pow,
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, natDegree_pow] at this
  omega

/-- Every function is `(a + b y) / p` with `a b p` polynomials, `p ≠ 0` — the form the degree
formula consumes: numerator in the `1, Y` basis, denominator a polynomial. -/
private theorem exists_smul_basis_div (f : W.FunctionField) :
    ∃ a b p : F[X], p ≠ 0 ∧
      f * algebraMap F[X] W.FunctionField p =
        algebraMap W.CoordinateRing W.FunctionField (a • 1 + b • CoordinateRing.mk W Y) := by
  obtain ⟨⟨u, ⟨d, _hd⟩⟩, hf⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid W.CoordinateRing (nonZeroDivisors F[X])) f
  obtain ⟨p, hp, rfl⟩ := _hd
  obtain ⟨a, b, rfl⟩ := CoordinateRing.exists_smul_basis_eq u
  refine ⟨a, b, p, nonZeroDivisors.ne_zero hp, ?_⟩
  rw [← hf, IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField]
  exact IsLocalization.mk'_spec W.FunctionField _ _

/-- natDegree form of Mathlib's `degree_norm_smul_basis` (recovered from `be8adaca`). -/
private theorem natDegree_norm_smul_basis {a b : F[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Algebra.norm F[X] (a • (1 : W.CoordinateRing) + b • CoordinateRing.mk W Y)).natDegree =
      max (2 * a.natDegree) (2 * b.natDegree + 3) := by
  refine natDegree_eq_of_degree_eq_some ?_
  rw [CoordinateRing.degree_norm_smul_basis, degree_eq_natDegree ha, degree_eq_natDegree hb]
  norm_cast

/-- **The degree of the norm, in the `(a + b y)/p` normal form.** -/
theorem intDegree_norm_eq_max {f : W.FunctionField} (hf : f ≠ 0) {a b p : F[X]}
    (ha : a ≠ 0) (hb : b ≠ 0) (hp : p ≠ 0)
    (h : f * algebraMap F[X] W.FunctionField p =
      algebraMap W.CoordinateRing W.FunctionField (a • 1 + b • CoordinateRing.mk W Y)) :
    (Algebra.norm (RatFunc F) f).intDegree
      = max (2 * (a.natDegree : ℤ) - 2 * p.natDegree)
            (2 * (b.natDegree : ℤ) + 3 - 2 * p.natDegree) := by
  rw [intDegree_norm_of_mul_eq W hf hp h, natDegree_norm_smul_basis W ha hb]
  push_cast
  omega

/-- Scaling a decomposition by a polynomial: `(a + by)/p = (ac + bcy)/(pc)`. -/
private theorem smul_basis_div_mul {f : W.FunctionField} {a b p : F[X]}
    (h : f * algebraMap F[X] W.FunctionField p =
      algebraMap W.CoordinateRing W.FunctionField (a • 1 + b • CoordinateRing.mk W Y)) (c : F[X]) :
    f * algebraMap F[X] W.FunctionField (p * c) =
      algebraMap W.CoordinateRing W.FunctionField
        ((a * c) • 1 + (b * c) • CoordinateRing.mk W Y) := by
  have : (a * c) • (1 : W.CoordinateRing) + (b * c) • CoordinateRing.mk W Y
      = (a • 1 + b • CoordinateRing.mk W Y) * algebraMap F[X] W.CoordinateRing c := by
    simp only [Algebra.smul_def, map_mul]; ring
  rw [this, map_mul, map_mul,
    ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField, ← h]
  ring

/-- **Two functions over a common denominator.** -/
private theorem exists_common_smul_basis_div (f g : W.FunctionField) :
    ∃ a₁ b₁ a₂ b₂ p : F[X], p ≠ 0 ∧
      f * algebraMap F[X] W.FunctionField p =
        algebraMap W.CoordinateRing W.FunctionField (a₁ • 1 + b₁ • CoordinateRing.mk W Y) ∧
      g * algebraMap F[X] W.FunctionField p =
        algebraMap W.CoordinateRing W.FunctionField (a₂ • 1 + b₂ • CoordinateRing.mk W Y) := by
  obtain ⟨a₁, b₁, p₁, hp₁, h₁⟩ := exists_smul_basis_div W f
  obtain ⟨a₂, b₂, p₂, hp₂, h₂⟩ := exists_smul_basis_div W g
  refine ⟨a₁ * p₂, b₁ * p₂, a₂ * p₁, b₂ * p₁, p₁ * p₂, mul_ne_zero hp₁ hp₂,
    smul_basis_div_mul W h₁ p₂, ?_⟩
  rw [mul_comm p₁ p₂]
  exact smul_basis_div_mul W h₂ p₁

section DomainCore

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve.Affine R)

/-- **The ultrametric inequality at the polynomial level**: the norm degree of a sum of two
basis-decomposed elements is at most the larger of the two. No denominators, no case analysis —
`degree` in `WithBot` handles the zero cases. -/
private theorem degree_norm_add_le (a₁ b₁ a₂ b₂ : R[X]) :
    (Algebra.norm R[X] ((a₁ + a₂) • (1 : W.CoordinateRing)
        + (b₁ + b₂) • CoordinateRing.mk W Y)).degree
      ≤ max (Algebra.norm R[X] (a₁ • 1 + b₁ • CoordinateRing.mk W Y)).degree
            (Algebra.norm R[X] (a₂ • 1 + b₂ • CoordinateRing.mk W Y)).degree := by
  rw [CoordinateRing.degree_norm_smul_basis, CoordinateRing.degree_norm_smul_basis,
    CoordinateRing.degree_norm_smul_basis]
  refine max_le ?_ ?_
  · calc (2 : ℕ) • (a₁ + a₂).degree ≤ 2 • max a₁.degree a₂.degree := by
          gcongr; exact degree_add_le a₁ a₂
    _ ≤ _ := by
          rcases max_cases a₁.degree a₂.degree with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> simp
  · calc (2 : ℕ) • (b₁ + b₂).degree + 3 ≤ 2 • max b₁.degree b₂.degree + 3 := by
          gcongr; exact degree_add_le b₁ b₂
    _ ≤ _ := by
          rcases max_cases b₁.degree b₂.degree with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> simp

/-- The `natDegree` form, and it needs no nonzero hypotheses at all: `natDegree_le_natDegree`
carries the `WithBot` bound across, and `natDegree 0 = 0` makes the zero cases hold anyway. -/
private theorem natDegree_norm_add_le (a₁ b₁ a₂ b₂ : R[X]) :
    (Algebra.norm R[X] ((a₁ + a₂) • (1 : W.CoordinateRing)
        + (b₁ + b₂) • CoordinateRing.mk W Y)).natDegree
      ≤ max (Algebra.norm R[X] (a₁ • 1 + b₁ • CoordinateRing.mk W Y)).natDegree
            (Algebra.norm R[X] (a₂ • 1 + b₂ • CoordinateRing.mk W Y)).natDegree := by
  have hd := degree_norm_add_le W a₁ b₁ a₂ b₂
  rcases max_cases
      (Algebra.norm R[X] (a₁ • (1 : W.CoordinateRing) + b₁ • CoordinateRing.mk W Y)).degree
      (Algebra.norm R[X] (a₂ • (1 : W.CoordinateRing) + b₂ • CoordinateRing.mk W Y)).degree with
    ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hd
  · exact le_max_of_le_left (natDegree_le_natDegree hd)
  · exact le_max_of_le_right (natDegree_le_natDegree hd)

end DomainCore

/-- **The ultrametric inequality on the function field.** -/
theorem intDegree_norm_add_le {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) :
    (Algebra.norm (RatFunc F) (f + g)).intDegree
      ≤ max (Algebra.norm (RatFunc F) f).intDegree (Algebra.norm (RatFunc F) g).intDegree := by
  obtain ⟨a₁, b₁, a₂, b₂, p, hp, h₁, h₂⟩ := exists_common_smul_basis_div W f g
  have h₃ : (f + g) * algebraMap F[X] W.FunctionField p =
      algebraMap W.CoordinateRing W.FunctionField
        ((a₁ + a₂) • 1 + (b₁ + b₂) • CoordinateRing.mk W Y) := by
    rw [add_mul, h₁, h₂, ← map_add]
    congr 1
    simp only [add_smul]
    ring
  rw [intDegree_norm_of_mul_eq W hf hp h₁, intDegree_norm_of_mul_eq W hg hp h₂,
    intDegree_norm_of_mul_eq W hfg hp h₃]
  have := natDegree_norm_add_le W a₁ b₁ a₂ b₂
  omega

/-- The norm of `0` is `0`: the extension is nontrivial, so `Algebra.norm_eq_zero_iff` applies. -/
private theorem norm_zero_eq_zero :
    Algebra.norm (RatFunc F) (0 : W.FunctionField) = 0 :=
  (Algebra.norm_eq_zero_iff (R := RatFunc F)).mpr rfl

open scoped Classical in
/-- The ultrametric inequality for the composite `RatFunc.inftyValuation ∘ Algebra.norm`, which is
`inftyValuation`'s `map_add_le_max'`. Split out to keep the definition short. -/
private theorem inftyValuation_add_le_max (x y : W.FunctionField) :
    RatFunc.inftyValuation F (Algebra.norm (RatFunc F) (x + y))
      ≤ max (RatFunc.inftyValuation F (Algebra.norm (RatFunc F) x))
            (RatFunc.inftyValuation F (Algebra.norm (RatFunc F) y)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · rw [hxy, norm_zero_eq_zero W, map_zero]
    exact zero_le
  have hNx : Algebra.norm (RatFunc F) x ≠ 0 :=
    fun h => hx ((Algebra.norm_eq_zero_iff (R := RatFunc F)).mp h)
  have hNy : Algebra.norm (RatFunc F) y ≠ 0 :=
    fun h => hy ((Algebra.norm_eq_zero_iff (R := RatFunc F)).mp h)
  have hNxy : Algebra.norm (RatFunc F) (x + y) ≠ 0 :=
    fun h => hxy ((Algebra.norm_eq_zero_iff (R := RatFunc F)).mp h)
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_apply, RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero F hNx, RatFunc.inftyValuation_of_nonzero F hNy,
    RatFunc.inftyValuation_of_nonzero F hNxy]
  rcases max_cases (Algebra.norm (RatFunc F) x).intDegree
      (Algebra.norm (RatFunc F) y).intDegree with ⟨h, _⟩ | ⟨h, _⟩
  · refine le_trans ?_ (le_max_left _ _)
    rw [WithZero.exp_le_exp]
    exact le_trans (intDegree_norm_add_le W hx hy hxy) (le_of_eq h)
  · refine le_trans ?_ (le_max_right _ _)
    rw [WithZero.exp_le_exp]
    exact le_trans (intDegree_norm_add_le W hx hy hxy) (le_of_eq h)

open scoped Classical in
/-- **The valuation at infinity on the function field of a Weierstrass curve**: Mathlib's place at
infinity of `F(x)`, composed with the algebra norm. -/
noncomputable def inftyValuation : Valuation W.FunctionField (WithZero (Multiplicative ℤ)) where
  toFun f := RatFunc.inftyValuation F (Algebra.norm (RatFunc F) f)
  map_zero' := by
    rw [norm_zero_eq_zero W, map_zero]
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_add_le_max' := inftyValuation_add_le_max W


open scoped Classical in
/-- The evaluation rule for `inftyValuation`: it is `RatFunc.inftyValuation` applied to the algebra
norm of the function. -/
@[simp]
theorem inftyValuation_apply (f : W.FunctionField) :
    inftyValuation W f = RatFunc.inftyValuation F (Algebra.norm (RatFunc F) f) := by
  simp [inftyValuation]

/-- A coordinate-ring element whose polynomial norm has positive degree has nonzero norm over
`RatFunc F`: a zero polynomial would have degree zero. -/
private theorem norm_ne_zero_of_natDegree_ne_zero {u : W.CoordinateRing}
    (h : (Algebra.norm F[X] u).natDegree ≠ 0) :
    Algebra.norm (RatFunc F) (algebraMap W.CoordinateRing W.FunctionField u) ≠ 0 := by
  rw [Algebra.norm_localization (R := F[X]) (M := nonZeroDivisors F[X]) (S := W.CoordinateRing)]
  refine RatFunc.algebraMap_ne_zero fun hz => h ?_
  rw [hz, natDegree_zero]

open scoped Classical in
-- NB `inftyValuation_X` and `inftyValuation_mk_Y` (and the two `natDegree_norm_*` in
-- `FunctionField/Norm.lean`) are deliberately NOT `@[simp]`: their left-hand sides are not in
-- simp-normal form — simp rewrites `algebraMap F[X] W.CoordinateRing X` to `AdjoinRoot.of` and
-- `CoordinateRing.mk W Y` to `AdjoinRoot.root` — so tagging them fails the repository's simpNF
-- lint gate. Stating them in that normal form instead would remove every mention of the curve's
-- coordinate functions, which is the whole content of the lemmas.
/-- **`x` has a double pole at infinity**: `v_∞ x = exp 2`, which is `ord_∞ x = -2`. -/
theorem inftyValuation_X :
    inftyValuation W (algebraMap W.CoordinateRing W.FunctionField
      (algebraMap F[X] W.CoordinateRing X)) = WithZero.exp 2 := by
  rw [inftyValuation_apply, RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero F
      (norm_ne_zero_of_natDegree_ne_zero W (u := algebraMap F[X] W.CoordinateRing X)
        (by rw [natDegree_norm_X]; norm_num)),
    intDegree_norm_algebraMap_coordinateRing, natDegree_norm_X]
  norm_num

open scoped Classical in
/-- **`y` has a triple pole at infinity**: `v_∞ y = exp 3`, which is `ord_∞ y = -3`. -/
theorem inftyValuation_mk_Y :
    inftyValuation W (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))
      = WithZero.exp 3 := by
  rw [inftyValuation_apply, RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero F
      (norm_ne_zero_of_natDegree_ne_zero W (u := CoordinateRing.mk W Y)
        (by rw [natDegree_norm_mk_Y]; norm_num)),
    intDegree_norm_algebraMap_coordinateRing, natDegree_norm_mk_Y]
  norm_num

end WeierstrassCurve.Affine

end
