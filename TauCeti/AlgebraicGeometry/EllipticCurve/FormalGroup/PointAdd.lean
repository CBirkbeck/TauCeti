/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.PairEval
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.ThirdPoint

/-!
# The parametrisation carries the group law: the chord case

`FormalGroup/Point.lean` sends a parameter `t` of an adic ideal to a point of `W⁄K`, and
`FormalGroup/PairEval.lean` gives the group law `F(t₁, t₂)` on parameters. This file joins them in
the case where the chord through the two points is not vertical: the point of the parameter
`F(t₁, t₂)` is the sum of the points of `t₁` and `t₂`.

Together with the injectivity of `formalPoint`, this is what makes the parameters of an adic ideal
a subgroup of the points of `W⁄K` rather than merely an indexed family of them: the group laws
`formalAdd` satisfies at parameters are then the group laws of `W⁄K`, transported.

## The hypotheses

`t₁ * w(t₂) ≠ t₂ * w(t₁)` is the chord condition: over a field, where a nonzero parameter `t`
carries the coordinates `x = t / w(t)` and `y = -1 / w(t)`, it says the two points have distinct
`x`-coordinates, so the line through them is not vertical. It is what excludes the doubling and
inverse cases, which need a different argument and are not treated here.

The two parameters are required nonzero because the zero parameter is the point at infinity, which
has no affine coordinates. The sum is nonzero automatically: `formalAddEval_ne_zero` derives that
from the chord condition. `hF` is the membership `formalPoint` needs of its argument, and is what
`formalAddEval_mem` supplies.

## Main results

* `WeierstrassCurve.formalPoint_formalAddEval_of_x_ne`: the parametrisation carries the group law
  at a pair of parameters whose points have distinct `x`-coordinates.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Filtration.lean`, declaration `paramPoint_add`.

The argument here is a transposition of this repository's own `FormalGroup/Add/Assoc.lean`, whose
private `thetaPoint_add` runs the same chord computation one level up — over a fraction field of
the power-series ring rather than at a parameter — for the associativity of `formalAdd`. The
scalar inputs come from the `Eval` and `PairEval` layers instead of that file's substitution
layer, and `formalPoint` replaces its `thetaPoint`.
-/

open Polynomial

public section

namespace WeierstrassCurve

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O] (W : WeierstrassCurve O)
variable {K : Type*} [Field K] [Algebra O K]

/-! ### The scalar inputs, read in `K`

The identities of the `Eval` and `PairEval` layers hold in `O`, while the chord computation happens
in `K`; these are their images under `algebraMap O K`, in the shape `chord_point_add` consumes.
They ask nothing of the curve beyond its coefficients and nothing of `K` beyond being a field over
`O`; the point-level statements below need more. -/

/-- The `w`-equation of the `(z, w)`-chart, read at a parameter in `K`. This is the shape
`chord_point_nonsingular` and `chord_point_add` ask of each of their three points. -/
private theorem algebraMap_formalWEval_wEquation {s : O} (hs : PowerSeries.HasEval s) :
    algebraMap O K (W.formalWEval s) = algebraMap O K s ^ 3 +
      (W.baseChange K).a₁ * algebraMap O K s * algebraMap O K (W.formalWEval s) +
      (W.baseChange K).a₂ * algebraMap O K s ^ 2 * algebraMap O K (W.formalWEval s) +
      (W.baseChange K).a₃ * algebraMap O K (W.formalWEval s) ^ 2 +
      (W.baseChange K).a₄ * algebraMap O K s * algebraMap O K (W.formalWEval s) ^ 2 +
      (W.baseChange K).a₆ * algebraMap O K (W.formalWEval s) ^ 3 := by
  have hkey := congrArg (algebraMap O K) (W.formalWEval_wEquation hs)
  rw [wEquationRHS_def] at hkey
  simpa [baseChange, map_add, map_mul, map_pow, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] using hkey

/-- Vieta's relation for the third root, read in `K`. -/
private theorem algebraMap_formalThirdRootEval_relation {t₁ t₂ : O}
    (h₁ : PowerSeries.HasEval t₁) (h₂ : PowerSeries.HasEval t₂) :
    (1 + (W.baseChange K).a₂ * algebraMap O K (W.formalSlopeEval t₁ t₂) +
        (W.baseChange K).a₄ * algebraMap O K (W.formalSlopeEval t₁ t₂) ^ 2 +
        (W.baseChange K).a₆ * algebraMap O K (W.formalSlopeEval t₁ t₂) ^ 3) *
      (algebraMap O K (W.formalThirdRootEval t₁ t₂) + algebraMap O K t₁ + algebraMap O K t₂) =
    -((W.baseChange K).a₁ * algebraMap O K (W.formalSlopeEval t₁ t₂) +
      (W.baseChange K).a₂ * algebraMap O K (W.formalInterceptEval t₁ t₂) +
      (W.baseChange K).a₃ * algebraMap O K (W.formalSlopeEval t₁ t₂) ^ 2 +
      2 * (W.baseChange K).a₄ * algebraMap O K (W.formalSlopeEval t₁ t₂) *
        algebraMap O K (W.formalInterceptEval t₁ t₂) +
      3 * (W.baseChange K).a₆ * algebraMap O K (W.formalSlopeEval t₁ t₂) ^ 2 *
        algebraMap O K (W.formalInterceptEval t₁ t₂)) := by
  have h := congrArg (algebraMap O K) (W.formalThirdRootEval_relation h₁ h₂)
  simp only [map_add, map_mul, map_neg, map_pow, map_one, map_ofNat] at h
  simpa [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] using h

/-- The chord cubic's leading coefficient does not vanish in `K`: it is a unit in `O` by
`isUnit_thirdRootDenom`, and a unit maps to a unit. -/
private theorem algebraMap_thirdRootDenom_ne_zero {I : Ideal O} (hI : IsAdic I) {t₁ t₂ : O}
    (h₁ : t₁ ∈ I) (h₂ : t₂ ∈ I) :
    (1 + (W.baseChange K).a₂ * algebraMap O K (W.formalSlopeEval t₁ t₂) +
      (W.baseChange K).a₄ * algebraMap O K (W.formalSlopeEval t₁ t₂) ^ 2 +
      (W.baseChange K).a₆ * algebraMap O K (W.formalSlopeEval t₁ t₂) ^ 3) ≠ 0 := by
  have : NonarchimedeanRing O := hI ▸ I.nonarchimedean
  have hnil : IsTopologicallyNilpotent (W.formalSlopeEval t₁ t₂) :=
    hI.isTopologicallyNilpotent_of_mem
      (by simpa using W.formalSlopeEval_mem hI (k := 1) (by simpa using h₁) (by simpa using h₂))
  have heq : algebraMap O K (1 + W.a₂ * W.formalSlopeEval t₁ t₂ +
        W.a₄ * W.formalSlopeEval t₁ t₂ ^ 2 + W.a₆ * W.formalSlopeEval t₁ t₂ ^ 3) =
      1 + (W.baseChange K).a₂ * algebraMap O K (W.formalSlopeEval t₁ t₂) +
        (W.baseChange K).a₄ * algebraMap O K (W.formalSlopeEval t₁ t₂) ^ 2 +
        (W.baseChange K).a₆ * algebraMap O K (W.formalSlopeEval t₁ t₂) ^ 3 := by
    simp [baseChange, map_add, map_mul, map_one, map_pow, map_a₂, map_a₄, map_a₆]
  rw [← heq]
  exact ((W.isUnit_thirdRootDenom hnil).map (algebraMap O K)).ne_zero

/-- The evaluated slope's defining property, read in `K`. -/
private theorem algebraMap_formalSlopeEval_mul_sub {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    algebraMap O K (W.formalSlopeEval t₁ t₂) * (algebraMap O K t₂ - algebraMap O K t₁) =
      algebraMap O K (W.formalWEval t₂) - algebraMap O K (W.formalWEval t₁) := by
  rw [← map_sub, ← map_sub, ← map_mul]
  exact congrArg (algebraMap O K) (W.formalSlopeEval_mul_sub h₁ h₂)

/-- The evaluated intercept identity, read in `K`. -/
private theorem algebraMap_formalInterceptEval_eq {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    algebraMap O K (W.formalInterceptEval t₁ t₂) = algebraMap O K (W.formalWEval t₁) -
      algebraMap O K (W.formalSlopeEval t₁ t₂) * algebraMap O K t₁ := by
  rw [← map_mul, ← map_sub]
  exact congrArg (algebraMap O K) (W.formalInterceptEval_eq h₁ h₂)

/-- The on-line identity, read in `K`: the third root lies on the chord. -/
private theorem algebraMap_formalWEval_formalThirdRootEval {t₁ t₂ : O}
    (h₁ : PowerSeries.HasEval t₁) (h₂ : PowerSeries.HasEval t₂) :
    algebraMap O K (W.formalWEval (W.formalThirdRootEval t₁ t₂)) =
      algebraMap O K (W.formalSlopeEval t₁ t₂) *
        algebraMap O K (W.formalThirdRootEval t₁ t₂) +
        algebraMap O K (W.formalInterceptEval t₁ t₂) := by
  rw [← map_mul, ← map_add]
  exact congrArg (algebraMap O K) (W.formalWEval_formalThirdRootEval h₁ h₂)

/-- The sum's parameter, in terms of the third root and the inverse denominator, read in `K`. -/
private theorem algebraMap_formalAddEval_eq {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    algebraMap O K (W.formalAddEval t₁ t₂) =
      -(algebraMap O K (W.formalThirdRootEval t₁ t₂) *
        algebraMap O K (W.formalInverseDenomInvEval (W.formalThirdRootEval t₁ t₂))) := by
  rw [W.formalAddEval_eq h₁ h₂, W.formalInverseEval_eq (W.hasEval_formalThirdRootEval h₁ h₂)]
  simp [map_neg, map_mul]

/-- The `w`-value at the sum's parameter, likewise. -/
private theorem algebraMap_formalWEval_formalAddEval {I : Ideal O} (hI : IsAdic I) {t₁ t₂ : O}
    (h₁ : t₁ ∈ I) (h₂ : t₂ ∈ I) :
    algebraMap O K (W.formalWEval (W.formalAddEval t₁ t₂)) =
      -(algebraMap O K (W.formalWEval (W.formalThirdRootEval t₁ t₂)) *
        algebraMap O K (W.formalInverseDenomInvEval (W.formalThirdRootEval t₁ t₂))) := by
  have hE₁ : PowerSeries.HasEval t₁ := hI.isTopologicallyNilpotent_of_mem h₁
  have hE₂ : PowerSeries.HasEval t₂ := hI.isTopologicallyNilpotent_of_mem h₂
  have hTmem : W.formalThirdRootEval t₁ t₂ ∈ I := by
    simpa using W.formalThirdRootEval_mem hI (k := 1) (by simpa using h₁) (by simpa using h₂)
  rw [W.formalAddEval_eq hE₁ hE₂, W.formalWEval_formalInverseEval
    (W.hasEval_formalThirdRootEval hE₁ hE₂) (W.hasEval_formalInverseEval hI hTmem)]
  simp [map_neg, map_mul]

/-- The inverse denominator at the third root is invertible, read in `K`. -/
private theorem algebraMap_formalInverseDenomEval_mul_inv {t₁ t₂ : O}
    (h₁ : PowerSeries.HasEval t₁) (h₂ : PowerSeries.HasEval t₂) :
    algebraMap O K (W.formalInverseDenomEval (W.formalThirdRootEval t₁ t₂)) *
      algebraMap O K (W.formalInverseDenomInvEval (W.formalThirdRootEval t₁ t₂)) = 1 := by
  rw [← map_mul, ← map_one (algebraMap O K)]
  exact congrArg (algebraMap O K)
    (W.formalInverseDenomEval_mul_inv (W.hasEval_formalThirdRootEval h₁ h₂))

/-- The inverse denominator at the third root, written out, read in `K`. -/
private theorem algebraMap_formalInverseDenomEval_eq {t₁ t₂ : O} (h₁ : PowerSeries.HasEval t₁)
    (h₂ : PowerSeries.HasEval t₂) :
    algebraMap O K (W.formalInverseDenomEval (W.formalThirdRootEval t₁ t₂)) =
      1 - (W.baseChange K).a₁ * algebraMap O K (W.formalThirdRootEval t₁ t₂) -
        (W.baseChange K).a₃ *
          algebraMap O K (W.formalWEval (W.formalThirdRootEval t₁ t₂)) := by
  have h := congrArg (algebraMap O K)
    (W.formalInverseDenomEval_eq (W.hasEval_formalThirdRootEval h₁ h₂))
  simpa [baseChange, map_sub, map_mul, map_one, map_a₁, map_a₃] using h

/-- The inverse denominator's inverse at the third root is nonzero. -/
private theorem algebraMap_formalInverseDenomInvEval_ne_zero {t₁ t₂ : O}
    (h₁ : PowerSeries.HasEval t₁) (h₂ : PowerSeries.HasEval t₂) :
    algebraMap O K (W.formalInverseDenomInvEval (W.formalThirdRootEval t₁ t₂)) ≠ 0 := by
  intro h
  have hu := W.algebraMap_formalInverseDenomEval_mul_inv (K := K) h₁ h₂
  rw [h, mul_zero] at hu
  exact one_ne_zero hu.symm

/-! ### The points

`formalPoint` needs the base-changed curve to be elliptic and the structure map to be injective,
and the group law on points needs decidable equality on `K`. -/

variable [DecidableEq K] [(W.baseChange K).IsElliptic] [FaithfulSMul O K]

omit [DecidableEq K] in
/-- The parametrised point of a nonzero parameter, written as the `Affine.Point.some` term that
`chord_point_add` speaks of. The `x`-coordinates agree on the nose; the `y`-coordinates differ
only in the spelling `-(w)⁻¹` against `-1 / w`. -/
private theorem formalPoint_eq_some {I : Ideal O} (hI : IsAdic I) {s : O} (hs : s ∈ I)
    (hs0 : s ≠ 0) (hn : (W.baseChange K).toAffine.Nonsingular
      (algebraMap O K s / algebraMap O K (W.formalWEval s))
      (-1 / algebraMap O K (W.formalWEval s))) :
    W.formalPoint (K := K) hI hs = Affine.Point.some _ _ hn := by
  rw [W.formalPoint_of_param_ne_zero hI hs hs0]
  simp only [Affine.Point.mk, neg_div, one_div]

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] [DecidableEq K] [(W.baseChange K).IsElliptic] in
/-- The numerator of the difference of the two `x`-coordinates is nonzero. -/
private theorem algebraMap_mul_formalWEval_sub_ne_zero {t₁ t₂ : O}
    (hx : t₁ * W.formalWEval t₂ ≠ t₂ * W.formalWEval t₁) :
    algebraMap O K t₁ * algebraMap O K (W.formalWEval t₂) -
      algebraMap O K t₂ * algebraMap O K (W.formalWEval t₁) ≠ 0 := by
  rw [← map_mul, ← map_mul, ← map_sub, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, sub_eq_zero]
  exact hx

/-- **The parametrisation carries the group law**, for two nonzero parameters whose points have
distinct `x`-coordinates: the point of `F(t₁, t₂)` is the sum of the points of `t₁` and `t₂`.

The chord through the two points meets the curve again at the parameter `t₃(t₁, t₂)`, and the
addition series is the formal inverse of that third root, so the group law of `W⁄K` applied to the
two points computes `F(t₁, t₂)`. -/
theorem formalPoint_formalAddEval_of_x_ne {I : Ideal O} (hI : IsAdic I) {t₁ t₂ : O}
    (h₁ : t₁ ∈ I) (h₂ : t₂ ∈ I) (h₁0 : t₁ ≠ 0) (h₂0 : t₂ ≠ 0)
    (hx : t₁ * W.formalWEval t₂ ≠ t₂ * W.formalWEval t₁)
    (hF : W.formalAddEval t₁ t₂ ∈ I) :
    W.formalPoint (K := K) hI h₁ + W.formalPoint (K := K) hI h₂ =
      W.formalPoint (K := K) hI hF := by
  have hne : ∀ {s : O}, s ≠ 0 → algebraMap O K s ≠ 0 := fun hs0 ↦ by simpa using hs0
  have hE₁ : PowerSeries.HasEval t₁ := hI.isTopologicallyNilpotent_of_mem h₁
  have hE₂ : PowerSeries.HasEval t₂ := hI.isTopologicallyNilpotent_of_mem h₂
  have hEF : PowerSeries.HasEval (W.formalAddEval t₁ t₂) := hI.isTopologicallyNilpotent_of_mem hF
  have hTmem : W.formalThirdRootEval t₁ t₂ ∈ I := by
    simpa using W.formalThirdRootEval_mem hI (k := 1) (by simpa using h₁) (by simpa using h₂)
  have hw₁0 := W.algebraMap_formalWEval_ne_zero (S := K) hI h₁ (hne h₁0)
  have hw₂0 := W.algebraMap_formalWEval_ne_zero (S := K) hI h₂ (hne h₂0)
  have hwT0 := W.algebraMap_formalWEval_ne_zero (S := K) hI hTmem
    (hne (W.formalThirdRootEval_ne_zero hE₁ hE₂ hx))
  have hwF0 := W.algebraMap_formalWEval_ne_zero (S := K) hI hF
    (hne (W.formalAddEval_ne_zero hE₁ hE₂ hx))
  have hDelta : (W.baseChange K).Δ ≠ 0 :=
    (W.baseChange K).coe_Δ' ▸ (W.baseChange K).Δ'.ne_zero
  have hn₁ := chord_point_nonsingular _ (W.algebraMap_formalWEval_wEquation hE₁) hw₁0 hDelta
  have hn₂ := chord_point_nonsingular _ (W.algebraMap_formalWEval_wEquation hE₂) hw₂0 hDelta
  have hnF := chord_point_nonsingular _ (W.algebraMap_formalWEval_wEquation hEF) hwF0 hDelta
  have hu := W.algebraMap_formalInverseDenomEval_mul_inv (K := K) hE₁ hE₂
  have hsp0 := W.algebraMap_formalInverseDenomInvEval_ne_zero (K := K) hE₁ hE₂
  -- the group law of `W⁄K`, applied to the two parametrised points
  obtain ⟨h₃, hadd⟩ := chord_point_add (W.baseChange K) (W.algebraMap_formalWEval_wEquation hE₁)
    (W.algebraMap_formalWEval_wEquation hE₂) (W.algebraMap_formalSlopeEval_mul_sub hE₁ hE₂)
    (W.algebraMap_formalInterceptEval_eq hE₁ hE₂)
    (W.algebraMap_formalThirdRootEval_relation hE₁ hE₂)
    (W.algebraMap_formalWEval_formalThirdRootEval hE₁ hE₂)
    (W.algebraMap_thirdRootDenom_ne_zero hI h₁ h₂) hw₁0 hw₂0 hwT0
    (W.algebraMap_mul_formalWEval_sub_ne_zero hx) hn₁ hn₂
  -- the third point's coordinates are those of the parameter `F(t₁, t₂)`, the formal inverse of
  -- the third root
  rw [W.formalPoint_eq_some hI h₁ h₁0 hn₁, W.formalPoint_eq_some hI h₂ h₂0 hn₂, hadd,
    W.formalPoint_eq_some hI hF (W.formalAddEval_ne_zero hE₁ hE₂ hx) hnF]
  simp only [Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩
  · rw [W.algebraMap_formalAddEval_eq (K := K) hE₁ hE₂,
      W.algebraMap_formalWEval_formalAddEval hI h₁ h₂]
    field_simp
  · rw [W.algebraMap_formalWEval_formalAddEval hI h₁ h₂,
      div_eq_div_iff hwT0 (neg_ne_zero.mpr (mul_ne_zero hwT0 hsp0))]
    linear_combination
      (-(algebraMap O K (W.formalWEval (W.formalThirdRootEval t₁ t₂)))) * hu +
        (algebraMap O K (W.formalWEval (W.formalThirdRootEval t₁ t₂)) *
          algebraMap O K (W.formalInverseDenomInvEval (W.formalThirdRootEval t₁ t₂))) *
          W.algebraMap_formalInverseDenomEval_eq (K := K) hE₁ hE₂

end WeierstrassCurve
