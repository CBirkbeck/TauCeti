/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Chord
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Inverse

/-!
# Base change of the chord construction

Every series of the chord construction is defined from the coefficients `a₁, …, a₆` of `W` by
ring operations, so each commutes with base change along a ring homomorphism `φ : R →+* S`:
the series of `W.map φ` is the image of the series of `W`.

This is the reduction step behind associativity of the formal group law. Associativity is an
identity between power series with integer-polynomial coefficients, so it can be proved once
over the universal Weierstrass curve and then transported to an arbitrary `W` by specialising
along the homomorphism that sends the universal coefficients to those of `W`. These lemmas are
what makes that transport possible.

## Main results

* `WeierstrassCurve.map_formalW`: the `w`-expansion commutes with base change. Everything else
  here reduces to this.
* `WeierstrassCurve.map_formalSlope`, `_formalIntercept`, `_formalThirdRoot`: the chord data
  commutes with base change.
* `WeierstrassCurve.map_formalInverseDenom`, `_formalInverse`: so does the formal inverse.

## Implementation notes

`map_formalW` is proved from uniqueness of the solution of the `w`-equation
(`eq_formalW_of_wEquation`): the image of `w(z)` under `φ` has vanishing constant coefficient
and satisfies the `w`-equation of `W.map φ`, and there is only one such series. The source
instead re-runs its own `wStep` recursion under `φ`, which this repository does not carry.
`map_wEquationRHS` is the step that pushes `φ` through the equation, and is the only place the
coefficients `a₁, …, a₆` are touched.

`map_formalThirdRoot` and `map_formalInverse` need that `φ` commutes with `invOfUnit`; that is
`MvPowerSeries.map_invOfUnit`, stated once in `TauCeti/RingTheory/MvPowerSeries/Inverse.lean`
rather than reproved for each.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean` — declarations `map_wSeries`,
`map_slopeSeries`, `map_interceptSeries`, `map_uSeries`, `map_thirdRootSeries` and
`map_inverseSeries`, renamed for the `formal*` names this repository uses. The source's
`map_addSeries` is not here: it is about the addition series, which is still in review.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S)

/-- Base change passes through the right-hand side of the `w`-equation, carrying the parameter
and the unknown with it. This is where the coefficients `a₁, …, a₆` are mapped. -/
theorem map_wEquationRHS (q v : PowerSeries R) :
    PowerSeries.map φ (wEquationRHS W q v) =
      wEquationRHS (W.map φ) (PowerSeries.map φ q) (PowerSeries.map φ v) := by
  simp only [wEquationRHS_powerSeries, map_add, map_mul, map_pow, PowerSeries.map_C,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

/-- **The `w`-expansion commutes with base change**: `φ (w_W (z)) = w_{φ W} (z)`.

Both sides have vanishing constant coefficient and solve the `w`-equation of `W.map φ`, and
that solution is unique. -/
theorem map_formalW : PowerSeries.map φ (formalW W) = formalW (W.map φ) := by
  refine eq_formalW_of_wEquation (W.map φ) _ ?_ ?_
  · rw [show PowerSeries.constantCoeff (PowerSeries.map φ (formalW W)) =
      φ (PowerSeries.constantCoeff (formalW W)) from rfl, constantCoeff_formalW, map_zero]
  conv_lhs => rw [formalW_wEquation W]
  rw [map_wEquationRHS W φ, PowerSeries.map_X]

/-- The slope of the chord commutes with base change. -/
theorem map_formalSlope :
    MvPowerSeries.map φ (formalSlope W) = formalSlope (W.map φ) := by
  ext d
  rw [MvPowerSeries.coeff_map, coeff_formalSlope, coeff_formalSlope, ← map_formalW W φ,
    PowerSeries.coeff_map]

/-- The intercept of the chord commutes with base change. -/
theorem map_formalIntercept :
    MvPowerSeries.map φ (formalIntercept W) = formalIntercept (W.map φ) := by
  rw [formalIntercept_def, formalIntercept_def, map_sub, map_mul, MvPowerSeries.map_X,
    map_formalSlope W φ, ← map_formalW W φ]
  congr 1
  ext d
  simp [PowerSeries.coeff_map, apply_ite φ]

/-- The denominator of the formal inverse commutes with base change. -/
theorem map_formalInverseDenom :
    PowerSeries.map φ (formalInverseDenom W) = formalInverseDenom (W.map φ) := by
  simp only [formalInverseDenom_def, map_sub, map_one, map_mul, PowerSeries.map_C,
    PowerSeries.map_X, map_formalW W φ, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

/-- The parameter of the third point of the chord commutes with base change. -/
theorem map_formalThirdRoot :
    MvPowerSeries.map φ (formalThirdRoot W) = formalThirdRoot (W.map φ) := by
  have hinv := MvPowerSeries.map_invOfUnit (σ := Unit ⊕ Unit) (τ := Unit ⊕ Unit)
    (MvPowerSeries.map φ)
    (D := 1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 + C W.a₆ * formalSlope W ^ 3)
    (by simp) (by rw [MvPowerSeries.constantCoeff_map]; simp)
  rw [formalThirdRoot_def, formalThirdRoot_def]
  simp only [map_sub, map_neg, map_add, map_one, map_mul, map_pow, map_ofNat,
    MvPowerSeries.map_X, MvPowerSeries.map_C, map_formalSlope W φ, map_formalIntercept W φ, hinv,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

/-- **The formal inverse commutes with base change.** -/
theorem map_formalInverse :
    PowerSeries.map φ (formalInverse W) = formalInverse (W.map φ) := by
  have hD' : MvPowerSeries.constantCoeff (PowerSeries.map φ (formalInverseDenom W)) = 1 := by
    rw [show (PowerSeries.map φ (formalInverseDenom W) : PowerSeries S) =
      formalInverseDenom (W.map φ) from map_formalInverseDenom W φ]
    exact constantCoeff_formalInverseDenom (W.map φ)
  have hinv := MvPowerSeries.map_invOfUnit (σ := Unit) (τ := Unit) (PowerSeries.map φ)
    (D := formalInverseDenom W) (by exact constantCoeff_formalInverseDenom W) hD'
  -- `PowerSeries.invOfUnit` is a plain definition for `MvPowerSeries.invOfUnit` with no bridge
  -- lemma between the two spellings, so it is unfolded before `hinv` can rewrite.
  simp only [formalInverse_def, PowerSeries.invOfUnit]
  rw [map_neg, map_mul, PowerSeries.map_X, hinv, map_formalInverseDenom W φ]

end WeierstrassCurve
