/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Unit
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Eval
public import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Evaluating the chord construction at a pair of parameters

The chord construction of `FormalGroup/Chord.lean` and the addition series of
`FormalGroup/Add/Series.lean` are two-variable power series. This file evaluates them at a pair
of parameters, as `FormalGroup/Eval.lean` evaluates the one-variable series at a single one, and
carries the identities of series over to identities of values.

The pair is the family `Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂` on `Unit ⊕ Unit`, and it admits
evaluation as soon as each parameter does — `MvPowerSeries.hasEval_sumElim`, the decay condition
being vacuous over finitely many variables.

## Main definitions

* `WeierstrassCurve.formalSlopeEval` : the slope `λ(t₁, t₂)` of the chord.
* `WeierstrassCurve.formalInterceptEval` : the intercept `ν(t₁, t₂)`.
* `WeierstrassCurve.formalThirdRootEval` : the parameter `t₃(t₁, t₂)` of the third point.
* `WeierstrassCurve.formalAddEval` : the value `F(t₁, t₂)` of the addition series.

## Main results

* `WeierstrassCurve.formalSlopeEval_mul_sub` : `λ(t₁, t₂) * (t₂ - t₁) = w(t₂) - w(t₁)`.
* `WeierstrassCurve.formalInterceptEval_eq` : `ν(t₁, t₂) = w(t₁) - λ(t₁, t₂) * t₁`.
* `WeierstrassCurve.formalSlopeEval_mem`, `WeierstrassCurve.formalThirdRootEval_mem` : parameters
  in `I ^ k` keep the slope and the third root there.
* `WeierstrassCurve.formalThirdRootEval_relation` : Vieta's formula at a pair, cleared of the
  inverse of the cubic's leading coefficient.
* `WeierstrassCurve.formalAddEval_eq` : `F(t₁, t₂) = ι(t₃(t₁, t₂))`.
* `WeierstrassCurve.formalAddEval_sub_add_mem` : `F(t₁, t₂) - (t₁ + t₂) ∈ I ^ (2 * k)` for
  parameters in `I ^ k`, so the group law is `t₁ + t₂` to first order.

## Implementation notes

Two of the series are built from one-variable ones through `PowerSeries.toMvPowerSeries` and
`MvPowerSeries.subst`; evaluating those is `PowerSeries.eval₂_id_toMvPowerSeries` and
`MvPowerSeries.aeval_subst`, both of which hold over a coefficient ring that is not discrete —
which the ambient adic ring is not.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`, whose full expansion is
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`),
`EllipticCurves/WeierstrassFormalGroup/Eval.lean` — its pair-evaluation layer, declarations
`slopeEval`, `interceptEval`, `thirdRootEval`, `addEval`, `hasEval_pairElim`, `eval_pair_rename`,
`eval_pair_subst_single`, `slopeEval_mul_sub`, `interceptEval_eq`, `slopeEval_mem`,
`thirdRootEval_mem`, `thirdRootEval_relation`, `addEval_eq` and `addEval_sub_add_mem`.

Three things are spelled differently here.

* The source's `eval_pair_rename` transports along `MvPowerSeries.rename`; this repository builds
  the one-variable series into two variables with `PowerSeries.toMvPowerSeries` instead, so the
  transport is `PowerSeries.eval₂_id_toMvPowerSeries`.
* The source states everything over `IsLocalRing.maximalIdeal O` at `k = 1`; the membership
  results here are over an arbitrary adic ideal and an arbitrary power of it, and the identities
  that use no ideal at all take `PowerSeries.HasEval` on each parameter, matching
  `FormalGroup/Eval.lean`.
* The source evaluates through its own `ChabautyColeman.MvPSeries.eval`, a wrapper for
  `MvPowerSeries.eval₂ (RingHom.id _)`, which is not ported.
-/

public section

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O] (W : WeierstrassCurve O)

/-- The pair `(t₁, t₂)` as a family indexed by the two variables of the chord construction. -/
private def pair (t₁ t₂ : O) : Unit ⊕ Unit → O := Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂

omit [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] [IsLinearTopology O O] in
/-- The pair takes the first parameter on the first variable. -/
private theorem pair_inl (t₁ t₂ : O) : pair t₁ t₂ (Sum.inl ()) = t₁ := rfl

omit [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] [IsLinearTopology O O] in
/-- The pair takes the second parameter on the second variable. -/
private theorem pair_inr (t₁ t₂ : O) : pair t₁ t₂ (Sum.inr ()) = t₂ := rfl

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- A pair of parameters admits evaluation as soon as each of them does. -/
private theorem hasEval_pair {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) : MvPowerSeries.HasEval (pair t₁ t₂) :=
  MvPowerSeries.hasEval_sumElim (fun _ ↦ h₁) fun _ ↦ h₂

/-- Evaluation at a pair of parameters, as a ring homomorphism. Every identity in this file is
the image of an identity of series under this map. -/
private noncomputable def evalPair {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) : MvPowerSeries (Unit ⊕ Unit) O →+* O :=
  MvPowerSeries.eval₂Hom (φ := RingHom.id O) (by simpa using continuous_id) (hasEval_pair h₁ h₂)

/-- `evalPair` is `MvPowerSeries.eval₂` at the identity ring hom, as a function. -/
private theorem coe_evalPair {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    ⇑(evalPair h₁ h₂) = MvPowerSeries.eval₂ (RingHom.id O) (pair t₁ t₂) :=
  MvPowerSeries.coe_eval₂Hom (φ := RingHom.id O) _ (hasEval_pair h₁ h₂)

/-- The value of the slope series at a pair of parameters. -/
noncomputable def formalSlopeEval (t₁ t₂ : O) : O :=
  MvPowerSeries.eval₂ (RingHom.id O) (pair t₁ t₂) W.formalSlope

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalSlopeEval` is evaluation of `formalSlope` at the pair, through the identity ring hom. -/
theorem formalSlopeEval_def (t₁ t₂ : O) :
    W.formalSlopeEval t₁ t₂ =
      MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
        W.formalSlope := (rfl)

/-- The value of the intercept series at a pair of parameters. -/
noncomputable def formalInterceptEval (t₁ t₂ : O) : O :=
  MvPowerSeries.eval₂ (RingHom.id O) (pair t₁ t₂) W.formalIntercept

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalInterceptEval` is evaluation of `formalIntercept` at the pair, through the identity
ring hom. -/
theorem formalInterceptEval_def (t₁ t₂ : O) :
    W.formalInterceptEval t₁ t₂ =
      MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
        W.formalIntercept := (rfl)

/-- The value of the third-root series at a pair of parameters. -/
noncomputable def formalThirdRootEval (t₁ t₂ : O) : O :=
  MvPowerSeries.eval₂ (RingHom.id O) (pair t₁ t₂) W.formalThirdRoot

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalThirdRootEval` is evaluation of `formalThirdRoot` at the pair, through the identity
ring hom. -/
theorem formalThirdRootEval_def (t₁ t₂ : O) :
    W.formalThirdRootEval t₁ t₂ =
      MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
        W.formalThirdRoot := (rfl)

/-- The value of the addition series at a pair of parameters. -/
noncomputable def formalAddEval (t₁ t₂ : O) : O :=
  MvPowerSeries.eval₂ (RingHom.id O) (pair t₁ t₂) W.formalAdd

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalAddEval` is evaluation of `formalAdd` at the pair, through the identity ring hom. -/
theorem formalAddEval_def (t₁ t₂ : O) :
    W.formalAddEval t₁ t₂ =
      MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
        W.formalAdd := (rfl)

/-- **The evaluated slope identity**: `λ(t₁, t₂) * (t₂ - t₁) = w(t₂) - w(t₁)`. -/
theorem formalSlopeEval_mul_sub {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    W.formalSlopeEval t₁ t₂ * (t₂ - t₁) = W.formalWEval t₂ - W.formalWEval t₁ := by
  have h := congrArg (evalPair h₁ h₂) W.formalSlope_mul_sub
  rw [map_mul, map_sub, map_sub] at h
  simpa [formalSlopeEval, W.formalWEval_def, coe_evalPair, pair_inl, pair_inr,
    PowerSeries.eval₂_id_toMvPowerSeries (hasEval_pair h₁ h₂),
    MvPowerSeries.eval₂_X] using h

/-- **The evaluated intercept identity**: `ν(t₁, t₂) = w(t₁) - λ(t₁, t₂) * t₁`. -/
theorem formalInterceptEval_eq {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    W.formalInterceptEval t₁ t₂ = W.formalWEval t₁ - W.formalSlopeEval t₁ t₂ * t₁ := by
  have h := congrArg (evalPair h₁ h₂) W.formalIntercept_def
  rw [map_sub, map_mul] at h
  simpa [formalInterceptEval, formalSlopeEval, W.formalWEval_def, coe_evalPair, pair_inl,
    pair_inr, PowerSeries.eval₂_id_toMvPowerSeries (hasEval_pair h₁ h₂),
    MvPowerSeries.eval₂_X] using h

/-- The slope of the chord at parameters of `I ^ k` again lies in `I ^ k`: the slope series has
vanishing constant coefficient. -/
theorem formalSlopeEval_mem {I : Ideal O} (hI : IsAdic I) {k : ℕ} {t₁ t₂ : O}
    (h₁ : PowerSeries.HasEval t₁) (h₂ : PowerSeries.HasEval t₂) (hk₁ : t₁ ∈ I ^ k)
    (hk₂ : t₂ ∈ I ^ k) : W.formalSlopeEval t₁ t₂ ∈ I ^ k :=
  MvPowerSeries.eval₂_mem_pow (φ := RingHom.id O) (by simpa using continuous_id)
    (hasEval_pair h₁ h₂) hI (by rintro (_ | _) <;> [exact hk₁; exact hk₂]) W.formalSlope (by simp)

/-- The third point's parameter at parameters of `I ^ k` again lies in `I ^ k`. -/
theorem formalThirdRootEval_mem {I : Ideal O} (hI : IsAdic I) {k : ℕ} {t₁ t₂ : O}
    (h₁ : PowerSeries.HasEval t₁) (h₂ : PowerSeries.HasEval t₂) (hk₁ : t₁ ∈ I ^ k)
    (hk₂ : t₂ ∈ I ^ k) : W.formalThirdRootEval t₁ t₂ ∈ I ^ k :=
  MvPowerSeries.eval₂_mem_pow (φ := RingHom.id O) (by simpa using continuous_id)
    (hasEval_pair h₁ h₂) hI (by rintro (_ | _) <;> [exact hk₁; exact hk₂]) W.formalThirdRoot
    (by simp)

/-- **Vieta's formula at a pair of parameters**, cleared of the inverse of the cubic's leading
coefficient: the third root satisfies
`(1 + a₂λ + a₄λ² + a₆λ³)(t₃ + t₁ + t₂) = -(a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν)`. -/
theorem formalThirdRootEval_relation {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    (1 + W.a₂ * W.formalSlopeEval t₁ t₂ + W.a₄ * W.formalSlopeEval t₁ t₂ ^ 2 +
        W.a₆ * W.formalSlopeEval t₁ t₂ ^ 3) *
      (W.formalThirdRootEval t₁ t₂ + t₁ + t₂) =
      -(W.a₁ * W.formalSlopeEval t₁ t₂ + W.a₂ * W.formalInterceptEval t₁ t₂ +
        W.a₃ * W.formalSlopeEval t₁ t₂ ^ 2 +
        2 * W.a₄ * W.formalSlopeEval t₁ t₂ * W.formalInterceptEval t₁ t₂ +
        3 * W.a₆ * W.formalSlopeEval t₁ t₂ ^ 2 * W.formalInterceptEval t₁ t₂) := by
  have hT := congrArg (evalPair h₁ h₂) W.formalThirdRoot_def
  have hD := congrArg (evalPair h₁ h₂) (MvPowerSeries.mul_invOfUnit
    (1 + MvPowerSeries.C W.a₂ * W.formalSlope + MvPowerSeries.C W.a₄ * W.formalSlope ^ 2 +
      MvPowerSeries.C W.a₆ * W.formalSlope ^ 3) 1 (by simp))
  simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_one, map_ofNat, coe_evalPair,
    MvPowerSeries.eval₂_X, MvPowerSeries.eval₂_C, RingHom.id_apply, pair_inl, pair_inr] at hT hD
  simp only [show MvPowerSeries.eval₂ (RingHom.id O) (pair t₁ t₂) W.formalSlope =
      W.formalSlopeEval t₁ t₂ from rfl,
    show MvPowerSeries.eval₂ (RingHom.id O) (pair t₁ t₂) W.formalIntercept =
      W.formalInterceptEval t₁ t₂ from rfl,
    show MvPowerSeries.eval₂ (RingHom.id O) (pair t₁ t₂) W.formalThirdRoot =
      W.formalThirdRootEval t₁ t₂ from rfl] at hT hD
  set L := W.formalSlopeEval t₁ t₂
  set N := W.formalInterceptEval t₁ t₂
  set T := W.formalThirdRootEval t₁ t₂
  set d := MvPowerSeries.eval₂ (RingHom.id O) (pair t₁ t₂)
    (MvPowerSeries.invOfUnit (1 + MvPowerSeries.C W.a₂ * W.formalSlope +
      MvPowerSeries.C W.a₄ * W.formalSlope ^ 2 + MvPowerSeries.C W.a₆ * W.formalSlope ^ 3) 1)
  clear_value L N T d
  linear_combination (1 + W.a₂ * L + W.a₄ * L ^ 2 + W.a₆ * L ^ 3) * hT -
    (W.a₁ * L + W.a₂ * N + W.a₃ * L ^ 2 + 2 * W.a₄ * L * N + 3 * W.a₆ * L ^ 2 * N) * hD

/-- **The addition series at a pair of parameters is the formal inverse of the third root**:
`F(t₁, t₂) = ι(t₃(t₁, t₂))`, the sum of two points being the negative of the third point of the
chord through them. -/
theorem formalAddEval_eq {I : Ideal O} (hI : IsAdic I) {t₁ t₂ : O}
    (h₁ : PowerSeries.HasEval t₁) (h₂ : PowerSeries.HasEval t₂) (hm₁ : t₁ ∈ I) (hm₂ : t₂ ∈ I) :
    W.formalAddEval t₁ t₂ = W.formalInverseEval (W.formalThirdRootEval t₁ t₂) := by
  have hmem : W.formalThirdRootEval t₁ t₂ ∈ I := by
    simpa using W.formalThirdRootEval_mem (k := 1) hI h₁ h₂ (by simpa using hm₁)
      (by simpa using hm₂)
  have hT : PowerSeries.HasEval (W.formalThirdRootEval t₁ t₂) :=
    hI.isTopologicallyNilpotent_of_mem hmem
  have hae : MvPowerSeries.aeval (hasEval_pair h₁ h₂) W.formalThirdRoot =
      W.formalThirdRootEval t₁ t₂ :=
    congrFun (MvPowerSeries.coe_aeval (hasEval_pair h₁ h₂)) W.formalThirdRoot
  have hT' : PowerSeries.HasEval (MvPowerSeries.aeval (hasEval_pair h₁ h₂) W.formalThirdRoot) := by
    rw [hae]; exact hT
  have h := MvPowerSeries.aeval_subst W.hasSubst_formalThirdRoot
    (MvPowerSeries.continuous_aeval (hasEval_pair h₁ h₂))
    (PowerSeries.hasEval hT') W.formalInverse
  rw [← W.formalAdd_def] at h
  simpa [formalAddEval, W.formalInverseEval_def, MvPowerSeries.coe_aeval, PowerSeries.eval₂,
    show MvPowerSeries.eval₂ (RingHom.id O) (pair t₁ t₂) W.formalThirdRoot =
      W.formalThirdRootEval t₁ t₂ from rfl] using h

/-- **The group law is `t₁ + t₂` to first order**: at parameters of `I ^ k` the addition series
deviates from their sum by an element of `I ^ (2 * k)`, because it agrees with `z₁ + z₂` below
total degree two. -/
theorem formalAddEval_sub_add_mem {I : Ideal O} (hI : IsAdic I) {k : ℕ} {t₁ t₂ : O}
    (h₁ : PowerSeries.HasEval t₁) (h₂ : PowerSeries.HasEval t₂) (hk₁ : t₁ ∈ I ^ k)
    (hk₂ : t₂ ∈ I ^ k) : W.formalAddEval t₁ t₂ - (t₁ + t₂) ∈ I ^ (2 * k) := by
  have heval : MvPowerSeries.eval₂ (RingHom.id O) (pair t₁ t₂)
      (W.formalAdd - MvPowerSeries.X (Sum.inl ()) - MvPowerSeries.X (Sum.inr ())) =
      W.formalAddEval t₁ t₂ - (t₁ + t₂) := by
    rw [← coe_evalPair h₁ h₂, map_sub, map_sub]
    simp [coe_evalPair, formalAddEval, MvPowerSeries.eval₂_X, pair_inl, pair_inr, sub_sub]
  rw [← heval]
  exact MvPowerSeries.eval₂_mem_pow_mul (φ := RingHom.id O) (by simpa using continuous_id)
    (hasEval_pair h₁ h₂) hI (by rintro (_ | _) <;> [exact hk₁; exact hk₂]) _
    (fun d hd ↦ W.coeff_formalAdd_sub_eq_zero_of_degree_lt hd)

end WeierstrassCurve
