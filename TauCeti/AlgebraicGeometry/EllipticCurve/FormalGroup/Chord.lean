/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
public import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# The chord through two points of a Weierstrass curve near the origin

Near the origin a Weierstrass curve `W` is parametrised by `z ↦ (z, w(z))`, where `w(z)` is the
`w`-expansion of `WeierstrassCurve.formalW`. This file builds the chord through the two points
with parameters `z₁` and `z₂`, as power series in `R⟦z₁, z₂⟧` — variables indexed by
`Unit ⊕ Unit`, as in Mathlib's formal-group-law conventions — and the parameter of the third
point in which that chord meets the curve.

Together these are the data of the chord construction: the formal group law of `W` is obtained
from `formalThirdRoot` by composing with the formal inverse, which is left to a later file.

## Main definitions

* `WeierstrassCurve.formalSlope`: the slope `λ(z₁, z₂) = (w(z₂) - w(z₁)) / (z₂ - z₁)` of the
  chord, defined through its coefficients rather than as a quotient.
* `WeierstrassCurve.formalIntercept`: the intercept `ν(z₁, z₂) = w(z₁) - λ(z₁, z₂) z₁`.
* `WeierstrassCurve.formalThirdRoot`: the parameter `z₃(z₁, z₂)` of the third point in which
  the chord meets the curve, obtained from Vieta's formulas.

## Main results

* `WeierstrassCurve.formalSlope_mul_sub`: the defining property `λ · (z₂ - z₁) = w(z₂) - w(z₁)`
  of the slope, which is what justifies calling it a divided difference.
* `WeierstrassCurve.formalIntercept_eq_rename_inr`: the intercept is symmetric in its two
  parameters, so the chord really does depend only on the pair of points.
* `WeierstrassCurve.constantCoeff_formalSlope`, `_formalIntercept`, `_formalThirdRoot`: all
  three series vanish at the origin.

## Implementation notes

`formalSlope` is defined by the coefficient formula rather than as a quotient of power series:
`z₂ - z₁` is not a unit in `R⟦z₁, z₂⟧`, so the divided difference has to be written down
directly and `formalSlope_mul_sub` recovers the property that names it.

Unlike `formalW`, which makes sense over a `CommSemiring`, the chord data needs subtraction
and so is stated over a `CommRing`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean`, its `Chord` section down to the third-root
series. The source's `wSeries` and `vSeries` are `formalW` and `formalU`, so neither is
re-ported and everything here is stated over the existing `w`-expansion API.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The slope and intercept of the chord -/

/-- The slope of the chord through the points with parameters `z₁` and `z₂`, that is, the
divided difference `λ(z₁, z₂) = (w(z₂) - w(z₁)) / (z₂ - z₁)`.

It is defined through its coefficients: the coefficient of `z₁ ^ i * z₂ ^ j` is the coefficient
of `z ^ (i + j + 1)` in `w(z)`. See `formalSlope_mul_sub` for the property this encodes.

The definition is `@[expose]`d because the coefficient formula *is* the definition here: it is
what `coeff_formalSlope` states, and there is no implementation detail to keep back. -/
@[expose] noncomputable def formalSlope : MvPowerSeries (Unit ⊕ Unit) R :=
  fun d => PowerSeries.coeff (d (Sum.inl ()) + d (Sum.inr ()) + 1) (formalW W)

theorem coeff_formalSlope (d : Unit ⊕ Unit →₀ ℕ) :
    coeff d (formalSlope W) =
      PowerSeries.coeff (d (Sum.inl ()) + d (Sum.inr ()) + 1) (formalW W) :=
  rfl

private theorem eq_single_inr_iff (d : Unit ⊕ Unit →₀ ℕ) :
    d = Finsupp.single (Sum.inr ()) (d (Sum.inr ())) ↔ d (Sum.inl ()) = 0 := by
  refine ⟨fun h => by rw [h]; simp, fun h => ?_⟩
  ext t
  match t with
  | .inl () => simpa using h
  | .inr () => simp

private theorem eq_single_inl_iff (d : Unit ⊕ Unit →₀ ℕ) :
    d = Finsupp.single (Sum.inl ()) (d (Sum.inl ())) ↔ d (Sum.inr ()) = 0 := by
  refine ⟨fun h => by rw [h]; simp, fun h => ?_⟩
  ext t
  match t with
  | .inl () => simp
  | .inr () => simpa using h

/-- The defining property of the slope: `λ(z₁, z₂) * (z₂ - z₁) = w(z₂) - w(z₁)`. -/
theorem formalSlope_mul_sub :
    formalSlope W * (X (Sum.inr ()) - X (Sum.inl ())) =
      rename (fun _ => Sum.inr ()) (formalW W) - rename (fun _ => Sum.inl ()) (formalW W) := by
  ext d
  set i := d (Sum.inl ()) with hi
  set j := d (Sum.inr ()) with hj
  rw [mul_sub, map_sub, map_sub,
    show (X (Sum.inr ()) : MvPowerSeries (Unit ⊕ Unit) R) =
      monomial (Finsupp.single (Sum.inr ()) 1) 1 from rfl,
    show (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit) R) =
      monomial (Finsupp.single (Sum.inl ()) 1) 1 from rfl,
    coeff_mul_monomial, coeff_mul_monomial, coeff_rename_const, coeff_rename_const]
  have hsubr : 1 ≤ j → (d - Finsupp.single (Sum.inr ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inl ()) +
      (d - Finsupp.single (Sum.inr ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inr ()) + 1 = i + j := by
    intro h
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    simp
    omega
  have hsubl : 1 ≤ i → (d - Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inl ()) +
      (d - Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inr ()) + 1 = i + j := by
    intro h
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    simp
    omega
  simp only [mul_one, eq_single_inr_iff, eq_single_inl_iff, Finsupp.single_le_iff,
    coeff_formalSlope]
  split_ifs with h1 h2 h3 h4 <;> grind

/-- The intercept `ν(z₁, z₂) = w(z₁) - λ(z₁, z₂) z₁` of the chord through the points with
parameters `z₁` and `z₂`. -/
noncomputable def formalIntercept : MvPowerSeries (Unit ⊕ Unit) R :=
  rename (fun _ => Sum.inl ()) (formalW W) - formalSlope W * X (Sum.inl ())

/-- The intercept of the chord is symmetric in its two parameters: computing it from the second
point gives the same series. -/
theorem formalIntercept_eq_rename_inr :
    formalIntercept W =
      rename (fun _ => Sum.inr ()) (formalW W) - formalSlope W * X (Sum.inr ()) := by
  have h := formalSlope_mul_sub W
  simp only [formalIntercept]
  linear_combination h

@[simp]
theorem constantCoeff_formalSlope : constantCoeff (formalSlope W) = 0 := by
  have h : constantCoeff (formalSlope W) =
      PowerSeries.coeff ((0 : Unit ⊕ Unit →₀ ℕ) (Sum.inl ()) +
        (0 : Unit ⊕ Unit →₀ ℕ) (Sum.inr ()) + 1) (formalW W) :=
    coeff_formalSlope W 0
  rw [h, coeff_formalW]
  exact formalWCoeff_eq_zero_of_lt W (by simp)

/-- `constantCoeff_formalW` transported to the one-variable `MvPowerSeries` spelling, which is
what `rename` produces. -/
theorem constantCoeff_formalW_mv : constantCoeff (formalW W) = 0 :=
  constantCoeff_formalW W

@[simp]
theorem constantCoeff_formalIntercept : constantCoeff (formalIntercept W) = 0 := by
  simp [formalIntercept, constantCoeff_rename, constantCoeff_formalW_mv]

/-! ### The third point of the chord -/

/-- The parameter `z₃(z₁, z₂)` of the third point in which the chord through the points with
parameters `z₁` and `z₂` meets the curve.

Substituting `w = λ z + ν` into the Weierstrass equation gives a cubic in `z` whose roots are
the three parameters, so by Vieta's formulas
`z₃ = -z₁ - z₂ - (a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν) / (1 + a₂λ + a₄λ² + a₆λ³)`,
the denominator being a unit because `λ` has vanishing constant coefficient. -/
noncomputable def formalThirdRoot : MvPowerSeries (Unit ⊕ Unit) R :=
  -X (Sum.inl ()) - X (Sum.inr ()) -
    (C W.a₁ * formalSlope W + C W.a₂ * formalIntercept W + C W.a₃ * formalSlope W ^ 2 +
        2 * C W.a₄ * formalSlope W * formalIntercept W +
        3 * C W.a₆ * formalSlope W ^ 2 * formalIntercept W) *
      invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
        C W.a₆ * formalSlope W ^ 3) 1

@[simp]
theorem constantCoeff_formalThirdRoot : constantCoeff (formalThirdRoot W) = 0 := by
  simp [formalThirdRoot]

end WeierstrassCurve
