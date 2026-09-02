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
* `WeierstrassCurve.subst_pair_formalIntercept_eq_inl`,
  `WeierstrassCurve.subst_pair_formalIntercept_eq_inr` : the chord's intercept at a pair, read
  from either of the two points.
* `WeierstrassCurve.subst_pair_formalIntercept_mul_sub` : the cross combination
  `q₁ w(q₂) - q₂ w(q₁) = ν(q₁, q₂) * (q₁ - q₂)`, which is what the two readings buy.
* `WeierstrassCurve.subst_pair_formalThirdRoot_ne_zero` : a nonzero intercept forces a nonzero
  third root.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean`, sections `Domain` and `Assembly`,
declarations `subst_wSeries_ne_zero`, `fracCurve`, `rho_weierstrass`, `thetaPoint`,
`thetaPoint_add`, `thetaPoint_neg`, `thetaPoint_inj` and `pair_intercept_ne_zero_of_ne`, together
with the single-parameter helpers `single_u_mul`, `single_iota_eq`, `single_u_eq` and
`single_wIota`.

Two of those are proved differently here, because this repository already has the content in a
more usable form. `pair_intercept_ne_zero_of_ne` collapses the cross combination with the single
rewrite `subst_pair_formalIntercept_mul_sub` where the source combines its two intercept readings
by hand; and Stoll's `hA` step inside `thetaPoint_add` argues through the constant coefficient,
whereas `subst_pair_thirdRootDenom_mul` already exhibits an explicit inverse. The four
single-parameter helpers are likewise transports of the `FormalGroup/Inverse.lean` identities
along `PowerSeries.subst q`, not re-derivations of them.

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

/-! ### The chord data at the pair -/

/-- The intercept of the chord through the two parametrized points, read at the pair `(q₁, q₂)`
from the first point: `ν(q₁, q₂) = w(q₁) - λ(q₁, q₂) * q₁`. -/
theorem subst_pair_formalIntercept_eq_inl {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
        (formalIntercept W) =
      PowerSeries.subst q₁ (formalW W) -
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) * q₁ := by
  have h := congrArg (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
    Unit ⊕ Unit → MvPowerSeries σ O)) (formalIntercept_def W)
  rw [← coe_substAlgHom (hasSubst_pair h₁ h₂)] at h
  simp only [map_sub, map_mul] at h
  simp only [coe_substAlgHom (hasSubst_pair h₁ h₂), subst_pair_toMvPowerSeries_inl W h₁ h₂,
    subst_X (hasSubst_pair h₁ h₂)] at h
  have hl : (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (Sum.inl ()) = q₁ := rfl
  rwa [hl] at h

/-- The same intercept read from the second point: `ν(q₁, q₂) = w(q₂) - λ(q₁, q₂) * q₂`. Together
with `subst_pair_formalIntercept_eq_inl` this is what expresses `q₁ * w(q₂) - q₂ * w(q₁)` through
the intercept alone. -/
theorem subst_pair_formalIntercept_eq_inr {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
        (formalIntercept W) =
      PowerSeries.subst q₂ (formalW W) -
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) * q₂ := by
  have h := congrArg (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
    Unit ⊕ Unit → MvPowerSeries σ O)) (formalIntercept_eq_inr W)
  rw [← coe_substAlgHom (hasSubst_pair h₁ h₂)] at h
  simp only [map_sub, map_mul] at h
  simp only [coe_substAlgHom (hasSubst_pair h₁ h₂), subst_pair_toMvPowerSeries_inr W h₁ h₂,
    subst_X (hasSubst_pair h₁ h₂)] at h
  have hr : (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (Sum.inr ()) = q₂ := rfl
  rwa [hr] at h

/-- The cross combination `q₁ w(q₂) - q₂ w(q₁)` is expressed through the intercept alone:
`q₁ w(q₂) - q₂ w(q₁) = ν(q₁, q₂) * (q₁ - q₂)`.

Reading the intercept from *both* points is what makes the slope cancel: subtracting the two
readings weighted by `q₂` and `q₁` removes `λ` entirely. This is the form the associativity
assembly needs in order to know that the chord's `x`-coordinates are distinct. -/
theorem subst_pair_formalIntercept_mul_sub {q₁ q₂ : MvPowerSeries σ O}
    (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    q₁ * PowerSeries.subst q₂ (formalW W) - q₂ * PowerSeries.subst q₁ (formalW W) =
      subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
        (formalIntercept W) * (q₁ - q₂) := by
  linear_combination q₂ * subst_pair_formalIntercept_eq_inl W h₁ h₂ -
    q₁ * subst_pair_formalIntercept_eq_inr W h₁ h₂

/-- A nonzero intercept forces a nonzero third root: at `z₃ = 0` the on-line identity
`w(z₃) = λ z₃ + ν` collapses to `0 = ν`, since `w` has no constant term. -/
theorem subst_pair_formalThirdRoot_ne_zero {q₁ q₂ : MvPowerSeries σ O}
    (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hN : subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalIntercept W) ≠ 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalThirdRoot W) ≠ 0 := by
  intro h
  refine hN ?_
  have honline := subst_pair_online W h₁ h₂
  rw [h, show (fun _ : Unit ↦ (0 : MvPowerSeries σ O)) = 0 from rfl,
    subst_zero_of_constantCoeff_zero (constantCoeff_formalW W)] at honline
  linear_combination -honline


/-! ### The formal inverse at a parameter -/

/-- The denominator of the formal inverse, read at a parameter, still multiplies its `invOfUnit`
to `1`: substituting is a ring map, so it carries `mul_invOfUnit_formalInverseDenom` along. -/
private theorem subst_formalInverseDenom_mul {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst q (formalInverseDenom W) *
        PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1) = 1 := by
  have h := congrArg (PowerSeries.substAlgHom hq) (mul_invOfUnit_formalInverseDenom W)
  simp only [map_mul, map_one] at h
  simpa only [PowerSeries.coe_substAlgHom hq] using h

/-- The formal inverse read at a parameter: `ι(q) = -(q * u(q)⁻¹)`. -/
private theorem subst_formalInverse_eq {q : MvPowerSeries σ O} (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst q (formalInverse W) =
      -(q * PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) := by
  rw [formalInverse_def, ← PowerSeries.coe_substAlgHom hq]
  simp only [map_neg, map_mul]
  rw [PowerSeries.coe_substAlgHom hq, PowerSeries.subst_X hq]

/-- The denominator of the formal inverse read at a parameter, written out. -/
private theorem subst_formalInverseDenom_eq {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst q (formalInverseDenom W) =
      1 - C W.a₁ * q - C W.a₃ * PowerSeries.subst q (formalW W) := by
  rw [formalInverseDenom_def, ← PowerSeries.coe_substAlgHom hq]
  simp only [map_sub, map_one, map_mul, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_C]

/-- The `w`-expansion at the inverted parameter: `w(ι(q)) = -(w(q) * u(q)⁻¹)`.

This is the one-variable `subst_formalInverse_formalW` carried through the substitution `q`. -/
private theorem subst_formalW_subst_formalInverse {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst (PowerSeries.subst q (formalInverse W)) (formalW W) =
      -(PowerSeries.subst q (formalW W) *
        PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) := by
  rw [← PowerSeries.subst_comp_subst_apply (hasSubst_formalInverse W) hq,
    subst_formalInverse_formalW, ← PowerSeries.coe_substAlgHom hq]
  simp only [map_neg, map_mul]

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

variable [DecidableEq KK] in
/-- **The chord addition of parametrized points**: `θ(q₁) + θ(q₂) = θ(F(q₁, q₂))`.

The two parametrized points lie on `fracCurve W`, the chord through them meets the curve again at
the parameter `z₃`, and the addition series is exactly the reflection of that third point. So the
group law of an honest Weierstrass curve, applied to the two points, computes `F(q₁, q₂)`. -/
private theorem thetaPoint_add (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (hN : subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalIntercept W) ≠ 0)
    (hx : q₁ * PowerSeries.subst q₂ (formalW W) - q₂ * PowerSeries.subst q₁ (formalW W) ≠ 0)
    (hF : constantCoeff (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (formalAdd W)) = 0)
    (hF0 : subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalAdd W) ≠ 0) :
    W.thetaPoint hΔ h₁ hq₁0 + W.thetaPoint hΔ h₂ hq₂0 = W.thetaPoint hΔ hF hF0 := by
  classical
  set ρ := algebraMap (MvPowerSeries σ O) KK with hρ
  have hinj : Function.Injective ρ := IsFractionRing.injective (MvPowerSeries σ O) KK
  set Λp := subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
    Unit ⊕ Unit → MvPowerSeries σ O) (formalSlope W) with hΛp
  set Np := subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
    Unit ⊕ Unit → MvPowerSeries σ O) (formalIntercept W) with hNp
  set Tp := subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
    Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W) with hTp
  set w₁ := PowerSeries.subst q₁ (formalW W) with hw₁'
  set w₂ := PowerSeries.subst q₂ (formalW W) with hw₂'
  set wT := PowerSeries.subst Tp (formalW W) with hwT'
  -- the chord identities, read in `KK`
  have hslope : ρ Λp * (ρ q₂ - ρ q₁) = ρ w₂ - ρ w₁ := by
    rw [← map_sub, ← map_sub, ← map_mul]
    exact congrArg ρ (subst_pair_formalSlope_mul W h₁ h₂)
  have hNint : ρ Np = ρ w₁ - ρ Λp * ρ q₁ := by
    rw [← map_mul, ← map_sub]
    exact congrArg ρ (subst_pair_formalIntercept_eq_inl W h₁ h₂)
  have hwTeq : ρ wT = ρ Λp * ρ Tp + ρ Np := by
    have h := congrArg ρ (subst_pair_online W h₁ h₂)
    simp only [map_add, map_mul] at h
    exact h
  have hT₃ : (1 + (fracCurve W σ KK).a₂ * ρ Λp + (fracCurve W σ KK).a₄ * ρ Λp ^ 2 +
      (fracCurve W σ KK).a₆ * ρ Λp ^ 3) * (ρ Tp + ρ q₁ + ρ q₂) =
      -((fracCurve W σ KK).a₁ * ρ Λp + (fracCurve W σ KK).a₂ * ρ Np +
        (fracCurve W σ KK).a₃ * ρ Λp ^ 2 + 2 * (fracCurve W σ KK).a₄ * ρ Λp * ρ Np +
        3 * (fracCurve W σ KK).a₆ * ρ Λp ^ 2 * ρ Np) := by
    have h := congrArg ρ (subst_pair_formalThirdRoot_relation W h₁ h₂)
    simp only [map_add, map_mul, map_neg, map_pow, map_one, map_ofNat] at h
    simpa [fracCurve, MvPowerSeries.c_eq_algebraMap] using h
  -- nonvanishing
  have hA : (1 + (fracCurve W σ KK).a₂ * ρ Λp + (fracCurve W σ KK).a₄ * ρ Λp ^ 2 +
      (fracCurve W σ KK).a₆ * ρ Λp ^ 3) ≠ 0 := by
    intro h
    refine subst_pair_thirdRootDenom_ne_zero W h₁ h₂ (hinj ?_)
    simpa [fracCurve, MvPowerSeries.c_eq_algebraMap, map_zero] using h
  have hTp0 : Tp ≠ 0 := subst_pair_formalThirdRoot_ne_zero W h₁ h₂ hN
  have hw₁0 : ρ w₁ ≠ 0 := fun h ↦ W.subst_formalW_ne_zero h₁ hq₁0 (hinj (by rw [h, map_zero]))
  have hw₂0 : ρ w₂ ≠ 0 := fun h ↦ W.subst_formalW_ne_zero h₂ hq₂0 (hinj (by rw [h, map_zero]))
  have hTc : constantCoeff Tp = 0 := constantCoeff_subst_pair_formalThirdRoot W h₁ h₂
  have hwT0 : ρ wT ≠ 0 := fun h ↦ W.subst_formalW_ne_zero hTc hTp0 (hinj (by rw [h, map_zero]))
  have hxρ : ρ q₁ * ρ w₂ - ρ q₂ * ρ w₁ ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact fun h ↦ hx (hinj (by rw [h, map_zero]))
  -- the two parametrized points satisfy the Weierstrass equation of `fracCurve W`
  have hwq₁ := by
    simpa [wEquationRHS_def] using
      W.algebraMap_subst_formalW_wEquation (KK := KK)
        (PowerSeries.HasSubst.of_constantCoeff_zero h₁)
  have hwq₂ := by
    simpa [wEquationRHS_def] using
      W.algebraMap_subst_formalW_wEquation (KK := KK)
        (PowerSeries.HasSubst.of_constantCoeff_zero h₂)
  -- the honest group law of `fracCurve W`, applied to the two points
  obtain ⟨h₃, hadd⟩ := chord_point_add (fracCurve W σ KK) hwq₁ hwq₂ hslope hNint hT₃ hwTeq hA
    hw₁0 hw₂0 hwT0 hxρ
    (chord_point_nonsingular (fracCurve W σ KK) hwq₁ hw₁0 hΔ)
    (chord_point_nonsingular (fracCurve W σ KK) hwq₂ hw₂0 hΔ)
  refine Eq.trans (show W.thetaPoint hΔ h₁ hq₁0 + W.thetaPoint hΔ h₂ hq₂0 =
    Affine.Point.some _ _ h₃ from hadd) ?_
  -- identify the third point with the point of parameter `F(q₁, q₂)`
  set sp := PowerSeries.subst Tp (PowerSeries.invOfUnit (formalInverseDenom W) 1) with hsp'
  have hu : ρ (PowerSeries.subst Tp (formalInverseDenom W)) * ρ sp = 1 := by
    rw [← map_mul, ← map_one ρ]
    exact congrArg ρ (subst_pair_formalInverseDenom_mul W h₁ h₂)
  have hueq : ρ (PowerSeries.subst Tp (formalInverseDenom W)) =
      1 - (fracCurve W σ KK).a₁ * ρ Tp - (fracCurve W σ KK).a₃ * ρ wT := by
    have h := congrArg ρ (subst_pair_formalInverseDenom_eq W h₁ h₂)
    simp only [map_sub, map_mul, map_one, MvPowerSeries.c_eq_algebraMap] at h
    exact h
  have hsp0 : ρ sp ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu
    exact one_ne_zero hu.symm
  have hFeq : ρ (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (formalAdd W)) = -(ρ Tp * ρ sp) := by
    have h := congrArg ρ (subst_pair_formalAdd_eq W h₁ h₂)
    simp only [map_neg, map_mul] at h
    exact h
  have hwFeq : ρ (PowerSeries.subst (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (formalAdd W)) (formalW W)) = -(ρ wT * ρ sp) := by
    have h := congrArg ρ (subst_pair_formalW_formalAdd W h₁ h₂)
    simp only [map_neg, map_mul] at h
    exact h
  rw [thetaPoint]
  simp only [Affine.Point.some.injEq]
  constructor
  · rw [hFeq, hwFeq]
    field_simp
  · rw [hwFeq, div_eq_div_iff hwT0 (neg_ne_zero.mpr (mul_ne_zero hwT0 hsp0))]
    linear_combination (-(ρ wT)) * hu + (ρ wT * ρ sp) * hueq

/-- **The parametrized point of the inverted parameter is the negative**: `θ(ι(q)) = -θ(q)`.

The formal inverse was built to be the parameter of the reflected point, so this identifies that
construction with the group inverse of `fracCurve W`. Both coordinates come out of the two
readings of the inverse, `ι(q) = -(q * u(q)⁻¹)` and `w(ι(q)) = -(w(q) * u(q)⁻¹)`. -/
private theorem thetaPoint_neg (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) (hq0 : q ≠ 0)
    (hi : constantCoeff (PowerSeries.subst q (formalInverse W)) = 0)
    (hi0 : PowerSeries.subst q (formalInverse W) ≠ 0) :
    W.thetaPoint hΔ hi hi0 = -W.thetaPoint hΔ hq hq0 := by
  classical
  set ρ := algebraMap (MvPowerSeries σ O) KK with hρ
  have hs : PowerSeries.HasSubst q := PowerSeries.HasSubst.of_constantCoeff_zero hq
  have hu : ρ (PowerSeries.subst q (formalInverseDenom W)) *
      ρ (PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) = 1 := by
    rw [← map_mul, ← map_one ρ]
    exact congrArg ρ (W.subst_formalInverseDenom_mul hs)
  have hsp0 : ρ (PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu
    exact one_ne_zero hu.symm
  have hIeq : ρ (PowerSeries.subst q (formalInverse W)) =
      -(ρ q * ρ (PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1))) := by
    have h := congrArg ρ (W.subst_formalInverse_eq hs)
    simpa only [map_neg, map_mul] using h
  have hwIeq : ρ (PowerSeries.subst (PowerSeries.subst q (formalInverse W)) (formalW W)) =
      -(ρ (PowerSeries.subst q (formalW W)) *
        ρ (PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1))) := by
    have h := congrArg ρ (W.subst_formalW_subst_formalInverse hs)
    simpa only [map_neg, map_mul] using h
  have hueq : ρ (PowerSeries.subst q (formalInverseDenom W)) =
      1 - (fracCurve W σ KK).a₁ * ρ q -
        (fracCurve W σ KK).a₃ * ρ (PowerSeries.subst q (formalW W)) := by
    have h := congrArg ρ (W.subst_formalInverseDenom_eq hs)
    simp only [map_sub, map_mul, map_one, MvPowerSeries.c_eq_algebraMap] at h
    exact h
  have hw0 : ρ (PowerSeries.subst q (formalW W)) ≠ 0 := fun h ↦
    W.subst_formalW_ne_zero hq hq0
      (IsFractionRing.injective (MvPowerSeries σ O) KK (by rw [h, map_zero]))
  simp only [thetaPoint, Affine.Point.neg_some, Affine.Point.some.injEq]
  simp only [← hρ]
  constructor
  · rw [hIeq, hwIeq]
    field_simp
  · rw [hwIeq, Affine.negY]
    field_simp
    linear_combination
      ρ (PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) * hueq - hu

/-- **The parametrized point determines the parameter**: `θ` is injective.

The `y`-coordinate `-1 / w(q)` already pins down `w(q)`, and the `x`-coordinate `q / w(q)` then
pins down `q`. -/
private theorem thetaPoint_inj (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (h : W.thetaPoint hΔ h₁ hq₁0 = W.thetaPoint hΔ h₂ hq₂0) : q₁ = q₂ := by
  classical
  set ρ := algebraMap (MvPowerSeries σ O) KK with hρ
  have hinj : Function.Injective ρ := IsFractionRing.injective (MvPowerSeries σ O) KK
  simp only [thetaPoint, Affine.Point.some.injEq] at h
  simp only [← hρ] at h
  have hw₁0 : ρ (PowerSeries.subst q₁ (formalW W)) ≠ 0 := fun hh ↦
    W.subst_formalW_ne_zero h₁ hq₁0 (hinj (by rw [hh, map_zero]))
  have hw₂0 : ρ (PowerSeries.subst q₂ (formalW W)) ≠ 0 := fun hh ↦
    W.subst_formalW_ne_zero h₂ hq₂0 (hinj (by rw [hh, map_zero]))
  have hw : ρ (PowerSeries.subst q₁ (formalW W)) = ρ (PowerSeries.subst q₂ (formalW W)) := by
    have h2 := h.2
    field_simp at h2
    linear_combination h2
  refine hinj ?_
  have h1 := h.1
  rw [div_eq_div_iff hw₁0 hw₂0, hw] at h1
  exact mul_right_cancel₀ hw₂0 h1

/-- The intercept at a pair is nonzero as soon as the two parameters are distinct and not
mutually inverse.

If the intercept vanished, the cross combination `q₁ w(q₂) - q₂ w(q₁)` would vanish with it, so
the two parametrized points would share an `x`-coordinate and hence agree up to sign. Injectivity
of `θ` then contradicts one of the two hypotheses. -/
private theorem pair_intercept_ne_zero_of_ne (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0) (hne₁ : q₁ ≠ q₂)
    (hne₂ : q₁ ≠ PowerSeries.subst q₂ (formalInverse W)) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalIntercept W) ≠ 0 := by
  classical
  intro h0
  set ρ := algebraMap (MvPowerSeries σ O) KK with hρ
  have hinj : Function.Injective ρ := IsFractionRing.injective (MvPowerSeries σ O) KK
  have hs₂ : PowerSeries.HasSubst q₂ := PowerSeries.HasSubst.of_constantCoeff_zero h₂
  -- a vanishing intercept collapses the cross combination, so the `x`-coordinates agree
  have hqw : q₁ * PowerSeries.subst q₂ (formalW W) -
      q₂ * PowerSeries.subst q₁ (formalW W) = 0 := by
    rw [subst_pair_formalIntercept_mul_sub W h₁ h₂, h0, zero_mul]
  have hw₁0 : ρ (PowerSeries.subst q₁ (formalW W)) ≠ 0 := fun hh ↦
    W.subst_formalW_ne_zero h₁ hq₁0 (hinj (by rw [hh, map_zero]))
  have hw₂0 : ρ (PowerSeries.subst q₂ (formalW W)) ≠ 0 := fun hh ↦
    W.subst_formalW_ne_zero h₂ hq₂0 (hinj (by rw [hh, map_zero]))
  have hx : ρ q₁ / ρ (PowerSeries.subst q₁ (formalW W)) =
      ρ q₂ / ρ (PowerSeries.subst q₂ (formalW W)) := by
    rw [div_eq_div_iff hw₁0 hw₂0, ← map_mul, ← map_mul]
    exact congrArg ρ (by linear_combination hqw)
  have hcase := (Affine.Point.X_eq_iff
    (h₁ := chord_point_nonsingular (fracCurve W σ KK)
      (by
        simpa [wEquationRHS_def] using W.algebraMap_subst_formalW_wEquation (KK := KK)
          (PowerSeries.HasSubst.of_constantCoeff_zero h₁))
      hw₁0 hΔ)
    (h₂ := chord_point_nonsingular (fracCurve W σ KK)
      (by simpa [wEquationRHS_def] using W.algebraMap_subst_formalW_wEquation (KK := KK) hs₂)
      hw₂0 hΔ)).mp hx
  -- the data carried by the inverted parameter
  have hs0 : PowerSeries.subst q₂ (PowerSeries.invOfUnit (formalInverseDenom W) 1) ≠ 0 := by
    intro hh
    have hmul := W.subst_formalInverseDenom_mul hs₂
    rw [hh, mul_zero] at hmul
    exact one_ne_zero hmul.symm
  have hi : constantCoeff (PowerSeries.subst q₂ (formalInverse W)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h₂ (formalInverse W) (constantCoeff_formalInverse W)
  have hi0 : PowerSeries.subst q₂ (formalInverse W) ≠ 0 := by
    rw [W.subst_formalInverse_eq hs₂]
    exact neg_ne_zero.mpr (mul_ne_zero hq₂0 hs0)
  rcases hcase with hc | hc
  · exact hne₁ (W.thetaPoint_inj hΔ h₁ h₂ hq₁0 hq₂0 hc)
  · -- `hc` comes out of `X_eq_iff` with `thetaPoint` unfolded, so fold it back before rewriting
    have hc' : W.thetaPoint hΔ h₁ hq₁0 = -W.thetaPoint hΔ h₂ hq₂0 := hc
    rw [← W.thetaPoint_neg hΔ h₂ hq₂0 hi hi0] at hc'
    exact hne₂ (W.thetaPoint_inj hΔ h₁ hi hq₁0 hi0 hc')

end WeierstrassCurve

end
