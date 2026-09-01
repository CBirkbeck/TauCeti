/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.ThirdPoint

/-!
# The chord group law over the fraction field of the series ring

Associativity of the chord addition series is proved by transporting the honest group law of a
Weierstrass curve. The parameters are power series, so the curve has to be read over a field
containing them: this file base changes `W` along `O → MvPowerSeries σ O → KK` and records the
`w`-equation there.

## Main definitions

* `WeierstrassCurve.fracCurve` : `W` base changed to a field `KK` over the series ring.

## Main statements

* `WeierstrassCurve.algebraMap_subst_formalW_wEquation` : the substituted `w`-expansion still
  solves the `w`-equation after being pushed into `KK`, now read on `fracCurve`.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean`, sections `Domain` and `Assembly`,
declarations `subst_wSeries_ne_zero`, `fracCurve`, `rho_weierstrass` and `thetaPoint`.

The source's `wSeries` and `vSeries` are `formalW` and `formalU` here, continuing the renaming
this repository applies to that development, so `subst_wSeries_ne_zero` is
`subst_formalW_ne_zero`. `FormalGroup/Add/Inverse.lean` records that the source left that lemma
unported because its only consumers lay in the source's `Assembly` and `Universal` sections;
this file is the first of them.

The statement is adapted rather than transcribed, because this repository states the `w`-equation
differently. Stoll carries a second copy of the equation as a private `def mvWStepAt` and phrases
the fixed-point property as `subst_wSeries_fix`; here `wEquationRHS` is already stated over an
arbitrary algebra, so reading it in `KK` *is* that definition, and `subst_formalW_wEquation`
supplies the fixed-point property. Stoll's proof is `congrArg` followed by unfolding `mvWStepAt`;
the corresponding step here has to move the coefficients across the base change instead, which is
what `fracCurve` in the statement records.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {O : Type*} [CommRing O]

/-- The curve `W` base changed to a field `KK` over the series ring `MvPowerSeries σ O`. The
parameters of the chord construction are series, so the group law they satisfy is the group law of
this curve. -/
noncomputable def fracCurve (W : WeierstrassCurve O) (σ : Type*) (KK : Type*) [Field KK]
    [Algebra (MvPowerSeries σ O) KK] : WeierstrassCurve KK :=
  W.map ((algebraMap (MvPowerSeries σ O) KK).comp (algebraMap O (MvPowerSeries σ O)))

variable (W : WeierstrassCurve O) {σ : Type*} {KK : Type*} [Field KK]
  [Algebra (MvPowerSeries σ O) KK]

/-- The `w`-expansion read at a substitutable parameter still solves the `w`-equation after being
pushed into `KK`, where the equation is the one of `fracCurve W`. -/
theorem algebraMap_subst_formalW_wEquation {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q (formalW W)) =
      wEquationRHS (fracCurve W σ KK) (algebraMap (MvPowerSeries σ O) KK q)
        (algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q (formalW W))) := by
  conv_lhs => rw [subst_formalW_wEquation W hq]
  rw [wEquationRHS_def, wEquationRHS_def]
  simp [fracCurve, map_add, map_mul, map_pow]

/-! ### The parametrized point -/

variable [IsDomain O]

/-- Over a domain the `w`-expansion at a nonzero parameter with vanishing constant coefficient is
itself nonzero: it factors as `q ^ 3 * u(q)`, and `u` has constant coefficient `1`. -/
private theorem subst_formalW_ne_zero {q : MvPowerSeries σ O} (hq : constantCoeff q = 0)
    (hq0 : q ≠ 0) : PowerSeries.subst q (formalW W) ≠ 0 := by
  have hs : PowerSeries.HasSubst q := PowerSeries.HasSubst.of_constantCoeff_zero hq
  have hexp : PowerSeries.subst q (formalW W) = q ^ 3 * PowerSeries.subst q (formalU W) := by
    conv_lhs => rw [formalW_eq_X_pow_mul_formalU]
    rw [← PowerSeries.coe_substAlgHom hs, map_mul, map_pow, PowerSeries.coe_substAlgHom hs,
      PowerSeries.subst_X hs]
  rw [hexp]
  refine mul_ne_zero (pow_ne_zero 3 hq0) fun h ↦ ?_
  have hc := congrArg constantCoeff h
  rw [map_zero, PowerSeries.constantCoeff_subst hs] at hc
  rw [finsum_eq_single _ 0 fun d hd ↦ ?_] at hc
  · rw [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_formalU, pow_zero, map_one,
      smul_eq_mul, mul_one] at hc
    exact one_ne_zero hc
  · rw [map_pow, hq, zero_pow hd, smul_zero]

variable [IsFractionRing (MvPowerSeries σ O) KK]

/-- The point of the base-changed curve carried by the parameter `q`: the solution `(q, w(q))` of
the `w`-equation, read in `KK` and in the affine coordinates `(q / w, -1 / w)` of the chart. -/
private noncomputable def thetaPoint (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (fracCurve W σ KK).toAffine.Point :=
  Affine.Point.some _ _ (chord_point_nonsingular (fracCurve W σ KK)
    (by
      simpa [wEquationRHS_def] using
        W.algebraMap_subst_formalW_wEquation (KK := KK)
          (PowerSeries.HasSubst.of_constantCoeff_zero hq))
    (fun h ↦ W.subst_formalW_ne_zero hq hq0
      (IsFractionRing.injective (MvPowerSeries σ O) KK (by rw [h, map_zero])))
    hΔ)

end WeierstrassCurve

end
