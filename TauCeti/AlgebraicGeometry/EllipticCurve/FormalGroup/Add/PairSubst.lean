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
* `WeierstrassCurve.subst_pair_online`: the `w`-expansion at the third root is the chord
  line read there.
* `WeierstrassCurve.subst_pair_thirdRootDenom_mul`: Vieta's denominator stays a unit at the
  pair.
* `WeierstrassCurve.subst_pair_formalThirdRoot_relation`: the defining relation of `z₃` at
  the pair, with that inverse cleared.

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
`pair_slope_identity`, `pair_A_mul` and `pair_T₃_relation`, together with `pair_online`
from `EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean`.

The source's `slopeSeries`, `interceptSeries` and `wSeries` are `formalSlope`, `formalIntercept`
and `formalW` here, continuing the renaming this repository applies to that development, so
`pair_slope_identity` and `pair_online` are `subst_pair_formalSlope_mul` and `subst_pair_online`.
Stoll's `A` for Vieta's denominator is `formalThirdRootDenom` here, so `pair_A_mul` and
`pair_T₃_relation` are `subst_pair_thirdRootDenom_mul` and
`subst_pair_formalThirdRoot_relation`.

The source's `pair_intercept_identity₁` and `pair_intercept_identity₂` are not ported here. Their
consumers lie in the source's `Assembly` section, so they belong with that first consumer rather
than in this file: `pair_intercept_identity₁` and `pair_intercept_identity₂` are
`WeierstrassCurve.subst_pair_formalIntercept_eq_inl` and
`WeierstrassCurve.subst_pair_formalIntercept_eq_inr` in `FormalGroup/Add/Assoc.lean`.
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

/-! ### The third point of the chord lies on the curve -/

/-- The on-line identity at the pair `(q₁, q₂)`: reading the `w`-expansion at the third root
gives the chord line read there. -/
theorem subst_pair_online (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    subst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
        Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W)) (formalW W) =
      subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalThirdRoot W) +
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalIntercept W) := by
  have h := congrArg (substAlgHom (hasSubst_pair h₁ h₂)) (subst_formalThirdRoot_formalW W)
  simp only [map_add, map_mul] at h
  simp only [coe_substAlgHom (hasSubst_pair h₁ h₂)] at h
  rwa [subst_comp_subst_apply (hasSubst_formalThirdRoot W) (hasSubst_pair h₁ h₂)] at h

/-! ### Vieta's denominator and the third-root relation -/

/-- Vieta's denominator, read at the pair `(q₁, q₂)`, is still a unit: it times its `invOfUnit`
is `1`. -/
theorem subst_pair_thirdRootDenom_mul (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    (1 + C W.a₂ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) +
        C W.a₄ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 2 +
        C W.a₆ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 3) *
      subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
        (invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
      C W.a₆ * formalSlope W ^ 3) 1) = 1 := by
  have h := congrArg (substAlgHom (hasSubst_pair h₁ h₂))
    (mul_invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
      C W.a₆ * formalSlope W ^ 3) 1 (constantCoeff_formalThirdRootDenom W))
  simp only [map_mul, map_add, map_one, map_pow] at h
  simp only [coe_substAlgHom (hasSubst_pair h₁ h₂), subst_C] at h
  exact h

/-- The defining relation of the third root at the pair `(q₁, q₂)`, with the inverse of Vieta's
denominator eliminated. -/
theorem subst_pair_formalThirdRoot_relation (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) :
    (1 + C W.a₂ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) +
        C W.a₄ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 2 +
        C W.a₆ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 3) *
      (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalThirdRoot W) + q₁ + q₂) =
      -(C W.a₁ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) +
        C W.a₂ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalIntercept W) +
        C W.a₃ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 2 +
        2 * C W.a₄ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) *
          subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
            (formalIntercept W) +
        3 * C W.a₆ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 2 *
          subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
            (formalIntercept W)) := by
  have hexp := congrArg (substAlgHom (hasSubst_pair h₁ h₂)) (formalThirdRoot_def W)
  simp only [map_sub, map_neg, map_mul, map_add, map_pow, map_ofNat] at hexp
  simp only [coe_substAlgHom (hasSubst_pair h₁ h₂), subst_X (hasSubst_pair h₁ h₂),
    subst_C] at hexp
  have hr : (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (Sum.inr ()) = q₂ := rfl
  have hl : (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (Sum.inl ()) = q₁ := rfl
  rw [hr, hl] at hexp
  have hAd := subst_pair_thirdRootDenom_mul W h₁ h₂
  set Lp :=
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalSlope W)
  set Np :=
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalIntercept W)
  set Tp :=
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalThirdRoot W)
  set dp :=
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
      C W.a₆ * formalSlope W ^ 3) 1)
  clear_value Lp Np Tp dp
  linear_combination (1 + C W.a₂ * Lp + C W.a₄ * Lp ^ 2 + C W.a₆ * Lp ^ 3) * hexp -
    (C W.a₁ * Lp + C W.a₂ * Np + C W.a₃ * Lp ^ 2 + 2 * C W.a₄ * Lp * Np +
      3 * C W.a₆ * Lp ^ 2 * Np) * hAd

end WeierstrassCurve
