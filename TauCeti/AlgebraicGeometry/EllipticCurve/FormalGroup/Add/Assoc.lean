/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst

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
`EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean`, section `Assembly`, declarations
`fracCurve` and `rho_weierstrass`.

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

end WeierstrassCurve

end
