/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Series

/-!
# The chord construction along an arbitrary pair of parameters

`FormalGroup/Chord.lean` builds the chord data — the slope `λ`, the intercept `ν`, the third
root `z₃` and the addition series `F` — as two-variable series in `MvPowerSeries (Unit ⊕ Unit) O`,
and states their defining identities in the two variables themselves. This file substitutes an
**arbitrary pair** `(q₁, q₂)` of series with vanishing constant coefficient for those variables,
and carries each identity across.

`FormalGroup/Add/Inverse.lean` already does this for the one pair `(z, ι(z))`. Its versions are
this file's, specialized; see the Provenance note there.

## Main results

* `WeierstrassCurve.hasSubst_pair`: the pair is a legitimate substitution family.
* `WeierstrassCurve.subst_pair_toMvPowerSeries_inl`,
  `WeierstrassCurve.subst_pair_toMvPowerSeries_inr`: the one-variable `w`-expansion, embedded in
  either variable, becomes `w(q₁)` respectively `w(q₂)`.
* `WeierstrassCurve.subst_pair_formalSlope_mul`: `λ(q₁, q₂) * (q₂ - q₁) = w(q₂) - w(q₁)`.

## Implementation notes

The pair is the family `Sum.elim (fun _ ↦ q₁) fun _ ↦ q₂` on `Unit ⊕ Unit`, written inline
throughout as `Add/Inverse.lean` writes its own family inline.

Two of Stoll's helpers in this range are not ported, because this repository already has them in
a more general form. His `subst_pair_rename`, which pushes the substitution through the
one-variable-into-two-variable embedding, is Mathlib's `PowerSeries.subst_toMvPowerSeries`
composed with `Sum.elim_inl`/`Sum.elim_inr` — this repository builds the two-variable series with
`PowerSeries.toMvPowerSeries` where the source uses `MvPowerSeries.rename`. His
`subst_wSeries_fix`, that `w` composed with any parameter solves the `w`-equation, is
`WeierstrassCurve.subst_formalW_wEquation` in `FormalGroup/WExpansion.lean`, stated there over an
arbitrary algebra.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`, whose full expansion is
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`),
`EllipticCurves/WeierstrassFormalGroup/ThirdPoint.lean`, declarations `hasSubst_pair`,
`pair_slope_identity`, `pair_intercept_identity₁` and `pair_intercept_identity₂`.

The source's `slopeSeries`, `interceptSeries` and `wSeries` are `formalSlope`, `formalIntercept`
and `formalW` here, continuing the renaming this repository applies to that development.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {O : Type*} [CommRing O] (W : WeierstrassCurve O)
variable {σ : Type*} {q₁ q₂ : MvPowerSeries σ O}

/-! ### The substitution family -/

/-- A pair of parameters with vanishing constant coefficient is a legitimate substitution
family for the two-variable chord series. -/
theorem hasSubst_pair (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    HasSubst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simpa)

/-- The `w`-expansion in the first parameter becomes `w(q₁)`. -/
theorem subst_pair_toMvPowerSeries_inl (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      ((formalW W).toMvPowerSeries (Sum.inl ())) = PowerSeries.subst q₁ (formalW W) := by
  rw [PowerSeries.subst_toMvPowerSeries (hasSubst_pair h₁ h₂), Sum.elim_inl]

/-- The `w`-expansion in the second parameter becomes `w(q₂)`. -/
theorem subst_pair_toMvPowerSeries_inr (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      ((formalW W).toMvPowerSeries (Sum.inr ())) = PowerSeries.subst q₂ (formalW W) := by
  rw [PowerSeries.subst_toMvPowerSeries (hasSubst_pair h₁ h₂), Sum.elim_inr]

/-! ### The chord through the two parametrized points -/

/-- The defining property of the slope, read at the pair `(q₁, q₂)`:
`λ(q₁, q₂) * (q₂ - q₁) = w(q₂) - w(q₁)`. -/
theorem subst_pair_formalSlope_mul (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
        (formalSlope W) * (q₂ - q₁) =
      PowerSeries.subst q₂ (formalW W) - PowerSeries.subst q₁ (formalW W) := by
  have h := congrArg (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
    Unit ⊕ Unit → MvPowerSeries σ O)) (formalSlope_mul_sub W)
  rw [← coe_substAlgHom (hasSubst_pair h₁ h₂)] at h
  simp only [map_mul, map_sub] at h
  simp only [coe_substAlgHom (hasSubst_pair h₁ h₂), subst_pair_toMvPowerSeries_inl W h₁ h₂,
    subst_pair_toMvPowerSeries_inr W h₁ h₂, subst_X (hasSubst_pair h₁ h₂)] at h
  have h1 : (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (Sum.inr ()) = q₂ := rfl
  have h2 : (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (Sum.inl ()) = q₁ := rfl
  rw [h1, h2] at h
  linear_combination h

end WeierstrassCurve
