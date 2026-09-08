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
# The parametrisation carries the group law, in the chord case

WIP — chord case of `formalPoint_formalAddEval`.
-/

open Polynomial

public section

namespace WeierstrassCurve

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O] (W : WeierstrassCurve O)
variable {K : Type*} [Field K] [DecidableEq K] [Algebra O K]
  [(W.baseChange K).IsElliptic] [FaithfulSMul O K]

/-- **The chord case**: when the two parameters carry points with distinct `x`-coordinates, the
parametrisation sends the group law at parameters to the group law on points. -/
theorem formalPoint_formalAddEval_of_x_ne {I : Ideal O} (hI : IsAdic I) {t₁ t₂ : O}
    (h₁ : t₁ ∈ I) (h₂ : t₂ ∈ I) (h₁0 : t₁ ≠ 0) (h₂0 : t₂ ≠ 0)
    (hx : t₁ * W.formalWEval t₂ ≠ t₂ * W.formalWEval t₁)
    (hF : W.formalAddEval t₁ t₂ ∈ I) (hF0 : W.formalAddEval t₁ t₂ ≠ 0) :
    W.formalPoint (K := K) hI h₁ + W.formalPoint (K := K) hI h₂ =
      W.formalPoint (K := K) hI hF := by
  classical
  set rho := algebraMap O K with hrho
  have hinj : Function.Injective rho := FaithfulSMul.algebraMap_injective O K
  have hE₁ : PowerSeries.HasEval t₁ := hI.isTopologicallyNilpotent_of_mem h₁
  have hE₂ : PowerSeries.HasEval t₂ := hI.isTopologicallyNilpotent_of_mem h₂
  have hET : PowerSeries.HasEval (W.formalThirdRootEval t₁ t₂) :=
    W.hasEval_formalThirdRootEval hE₁ hE₂
  -- the chord identities, read in `K`
  have hslope : rho (W.formalSlopeEval t₁ t₂) * (rho t₂ - rho t₁) =
      rho (W.formalWEval t₂) - rho (W.formalWEval t₁) := by
    rw [← map_sub, ← map_sub, ← map_mul]
    exact congrArg rho (W.formalSlopeEval_mul_sub hE₁ hE₂)
  have hNint : rho (W.formalInterceptEval t₁ t₂) =
      rho (W.formalWEval t₁) - rho (W.formalSlopeEval t₁ t₂) * rho t₁ := by
    rw [← map_mul, ← map_sub]
    exact congrArg rho (W.formalInterceptEval_eq hE₁ hE₂)
  have hwTeq : rho (W.formalWEval (W.formalThirdRootEval t₁ t₂)) =
      rho (W.formalSlopeEval t₁ t₂) * rho (W.formalThirdRootEval t₁ t₂) +
        rho (W.formalInterceptEval t₁ t₂) := by
    rw [← map_mul, ← map_add]
    exact congrArg rho (W.formalWEval_formalThirdRootEval hE₁ hE₂)
  -- Vieta, read in `K`
  have hT3 : (1 + (W.baseChange K).a₂ * rho (W.formalSlopeEval t₁ t₂) +
      (W.baseChange K).a₄ * rho (W.formalSlopeEval t₁ t₂) ^ 2 +
      (W.baseChange K).a₆ * rho (W.formalSlopeEval t₁ t₂) ^ 3) *
        (rho (W.formalThirdRootEval t₁ t₂) + rho t₁ + rho t₂) =
      -((W.baseChange K).a₁ * rho (W.formalSlopeEval t₁ t₂) +
        (W.baseChange K).a₂ * rho (W.formalInterceptEval t₁ t₂) +
        (W.baseChange K).a₃ * rho (W.formalSlopeEval t₁ t₂) ^ 2 +
        2 * (W.baseChange K).a₄ * rho (W.formalSlopeEval t₁ t₂) *
          rho (W.formalInterceptEval t₁ t₂) +
        3 * (W.baseChange K).a₆ * rho (W.formalSlopeEval t₁ t₂) ^ 2 *
          rho (W.formalInterceptEval t₁ t₂)) := by
    have h := congrArg rho (W.formalThirdRootEval_relation hE₁ hE₂)
    simp only [map_add, map_mul, map_neg, map_pow, map_one, map_ofNat] at h
    simpa [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] using h
  -- the leading coefficient is a unit in `O`, hence nonzero in the field `K`
  have hnarch : NonarchimedeanRing O := hI ▸ I.nonarchimedean
  have hslope_nil : IsTopologicallyNilpotent (W.formalSlopeEval t₁ t₂) :=
    hI.isTopologicallyNilpotent_of_mem
      (by simpa using W.formalSlopeEval_mem hI (k := 1) (by simpa using h₁) (by simpa using h₂))
  have hA : (1 + (W.baseChange K).a₂ * rho (W.formalSlopeEval t₁ t₂) +
      (W.baseChange K).a₄ * rho (W.formalSlopeEval t₁ t₂) ^ 2 +
      (W.baseChange K).a₆ * rho (W.formalSlopeEval t₁ t₂) ^ 3) ≠ 0 := by
    have hu := (W.isUnit_thirdRootDenom hslope_nil).map (algebraMap O K)
    have heq : rho (1 + W.a₂ * W.formalSlopeEval t₁ t₂ + W.a₄ * W.formalSlopeEval t₁ t₂ ^ 2 +
        W.a₆ * W.formalSlopeEval t₁ t₂ ^ 3) =
        1 + (W.baseChange K).a₂ * rho (W.formalSlopeEval t₁ t₂) +
          (W.baseChange K).a₄ * rho (W.formalSlopeEval t₁ t₂) ^ 2 +
          (W.baseChange K).a₆ * rho (W.formalSlopeEval t₁ t₂) ^ 3 := by
      simp [hrho, baseChange, map_add, map_mul, map_one, map_pow, map_a₂, map_a₄, map_a₆]
    rw [← heq]
    exact hu.ne_zero
  -- nonvanishing, transported through the injective structure map
  have hK₁ : rho t₁ ≠ 0 := fun h ↦ h₁0 (hinj (by rw [h, map_zero]))
  have hK₂ : rho t₂ ≠ 0 := fun h ↦ h₂0 (hinj (by rw [h, map_zero]))
  have hw₁0 : rho (W.formalWEval t₁) ≠ 0 := W.algebraMap_formalWEval_ne_zero hI h₁ hK₁
  have hw₂0 : rho (W.formalWEval t₂) ≠ 0 := W.algebraMap_formalWEval_ne_zero hI h₂ hK₂
  have hTmem : W.formalThirdRootEval t₁ t₂ ∈ I := by
    simpa using W.formalThirdRootEval_mem hI (k := 1) (by simpa using h₁) (by simpa using h₂)
  have hT0 : W.formalThirdRootEval t₁ t₂ ≠ 0 := W.formalThirdRootEval_ne_zero hE₁ hE₂ hx
  have hKT : rho (W.formalThirdRootEval t₁ t₂) ≠ 0 := fun h ↦ hT0 (hinj (by rw [h, map_zero]))
  have hwT0 : rho (W.formalWEval (W.formalThirdRootEval t₁ t₂)) ≠ 0 :=
    W.algebraMap_formalWEval_ne_zero hI hTmem hKT
  have hxK : rho t₁ * rho (W.formalWEval t₂) - rho t₂ * rho (W.formalWEval t₁) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact fun h ↦ sub_ne_zero.mpr hx (hinj (by rw [h, map_zero]))
  have hDelta : (W.baseChange K).Δ ≠ 0 :=
    (W.baseChange K).coe_Δ' ▸ (W.baseChange K).Δ'.ne_zero
  -- the `(z, w)`-chart Weierstrass equation at each parameter, read in `K`
  have hwq : ∀ {s : O}, PowerSeries.HasEval s →
      rho (W.formalWEval s) = rho s ^ 3 + (W.baseChange K).a₁ * rho s * rho (W.formalWEval s) +
        (W.baseChange K).a₂ * rho s ^ 2 * rho (W.formalWEval s) +
        (W.baseChange K).a₃ * rho (W.formalWEval s) ^ 2 +
        (W.baseChange K).a₄ * rho s * rho (W.formalWEval s) ^ 2 +
        (W.baseChange K).a₆ * rho (W.formalWEval s) ^ 3 := by
    intro s hs
    have hkey := congrArg rho (W.formalWEval_wEquation hs)
    rw [wEquationRHS_def] at hkey
    simpa [hrho, baseChange, map_add, map_mul, map_pow, map_a₁, map_a₂, map_a₃, map_a₄,
      map_a₆] using hkey
  -- the honest group law of the base-changed curve, applied to the two parametrised points
  obtain ⟨h₃, hadd⟩ := chord_point_add (W.baseChange K) (hwq hE₁) (hwq hE₂) hslope hNint hT3
    hwTeq hA hw₁0 hw₂0 hwT0 hxK
    (chord_point_nonsingular (W.baseChange K) (hwq hE₁) hw₁0 hDelta)
    (chord_point_nonsingular (W.baseChange K) (hwq hE₂) hw₂0 hDelta)
  -- identify each parametrised point with the `.some` term `chord_point_add` speaks of; the
  -- `x`-coordinates agree on the nose and the `y`-coordinates differ only in spelling
  have key : ∀ {s : O} (hs : s ∈ I) (hs0 : s ≠ 0)
      (hn : (W.baseChange K).toAffine.Nonsingular (rho s / rho (W.formalWEval s))
        (-1 / rho (W.formalWEval s))),
      W.formalPoint (K := K) hI hs = Affine.Point.some _ _ hn := by
    intro s hs hs0 hn
    rw [W.formalPoint_of_param_ne_zero hI hs hs0]
    simp only [Affine.Point.mk, hrho, neg_div, one_div]
  -- the sum's parameter is the formal inverse of the third root, so its coordinates are the
  -- reflected ones that `chord_point_add` produced
  set sp := W.formalInverseDenomInvEval (W.formalThirdRootEval t₁ t₂) with hsp'
  have hEF : PowerSeries.HasEval (W.formalAddEval t₁ t₂) := hI.isTopologicallyNilpotent_of_mem hF
  have hKF : rho (W.formalAddEval t₁ t₂) ≠ 0 := fun h ↦ hF0 (hinj (by rw [h, map_zero]))
  have hwF0 : rho (W.formalWEval (W.formalAddEval t₁ t₂)) ≠ 0 :=
    W.algebraMap_formalWEval_ne_zero hI hF hKF
  have hFeq : rho (W.formalAddEval t₁ t₂) = -(rho (W.formalThirdRootEval t₁ t₂) * rho sp) := by
    rw [W.formalAddEval_eq hE₁ hE₂, W.formalInverseEval_eq hET, hsp']
    simp [map_neg, map_mul]
  have hwFeq : rho (W.formalWEval (W.formalAddEval t₁ t₂)) =
      -(rho (W.formalWEval (W.formalThirdRootEval t₁ t₂)) * rho sp) := by
    rw [W.formalAddEval_eq hE₁ hE₂,
      W.formalWEval_formalInverseEval hET (W.hasEval_formalInverseEval hI hTmem), hsp']
    simp [map_neg, map_mul]
  have hu : rho (W.formalInverseDenomEval (W.formalThirdRootEval t₁ t₂)) * rho sp = 1 := by
    rw [← map_mul, hsp', ← map_one rho]
    exact congrArg rho (W.formalInverseDenomEval_mul_inv hET)
  have hsp0 : rho sp ≠ 0 := fun h ↦ by rw [h, mul_zero] at hu; exact one_ne_zero hu.symm
  have hueq : rho (W.formalInverseDenomEval (W.formalThirdRootEval t₁ t₂)) =
      1 - (W.baseChange K).a₁ * rho (W.formalThirdRootEval t₁ t₂) -
        (W.baseChange K).a₃ * rho (W.formalWEval (W.formalThirdRootEval t₁ t₂)) := by
    have h := congrArg rho (W.formalInverseDenomEval_eq hET)
    simpa [hrho, baseChange, map_sub, map_mul, map_one, map_a₁, map_a₃] using h
  rw [key h₁ h₁0 (chord_point_nonsingular (W.baseChange K) (hwq hE₁) hw₁0 hDelta),
    key h₂ h₂0 (chord_point_nonsingular (W.baseChange K) (hwq hE₂) hw₂0 hDelta), hadd,
    key hF hF0 (chord_point_nonsingular (W.baseChange K) (hwq hEF) hwF0 hDelta)]
  simp only [Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩
  · rw [hFeq, hwFeq]
    field_simp
  · rw [hwFeq, div_eq_div_iff hwT0 (neg_ne_zero.mpr (mul_ne_zero hwT0 hsp0))]
    linear_combination (-(rho (W.formalWEval (W.formalThirdRootEval t₁ t₂)))) * hu +
      (rho (W.formalWEval (W.formalThirdRootEval t₁ t₂)) * rho sp) * hueq

end WeierstrassCurve
