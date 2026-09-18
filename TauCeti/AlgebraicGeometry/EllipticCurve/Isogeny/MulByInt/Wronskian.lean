/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability

/-!
# The division-polynomial Wronskian at the generic point

Multiplication by `n` scales the invariant differential, `[n]*ω = n ω` (Silverman III.5.3). Read
through `ω = dx / u` with `u = 2y + a₁x + a₃`, and through `[n]*x = Φₙ / ΨSqₙ`, that single
differential identity becomes an identity between division polynomials: the quotient rule turns
`d([n]*x)` into the **Wronskian** `Φₙ' ΨSqₙ - Φₙ ΨSqₙ'` over `ΨSqₙ²`, and comparing coefficients
of `dx` gives

`(Φₙ' ΨSqₙ - Φₙ ΨSqₙ') u = n ΨSqₙ² ([n]*u)`

at the generic point. This is the function-field half of the classical Wronskian formula; the
other half rewrites `ΨSqₙ² ([n]*u)` as `preΨ_{2n} u`, which is not proved here.

## Main results

* `TauCeti.Isogeny.wronskian_Φ_ΨSq_mul_invariantDifferentialDenom`: the identity above.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5.3.

## Provenance

AINTLIB (Chris Birkbeck), Apache-2.0, at commit `a302aeacd86053f9d5f991fbbf664e1cc1051d08`,
proves the same identity as `divPoly_wronskian_identity_of_omega`, at
`projects/HasseWeil/HasseWeil/Foundation/OmegaPullbackCoeff.lean:776`. There it is stated over a
packaging of the scaling factor as `omegaPullbackCoeff`, and takes `a_{[n]} = n` as a hypothesis;
TauCeti already proves the scaling identity itself
(`pullbackDifferential_mulByIntIsogeny_invariantDifferential`), so no packaging is needed and the
hypothesis is discharged. Only the quotient-rule computation is carried over.
-/

public section

open Polynomial

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- The pullback of `[n]` sends the generic coordinate to `[n]*x = Φₙ/ΨSqₙ`. -/
private theorem fieldPullback_mulByIntIsogeny_genericX [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    (mulByIntIsogeny W hn).fieldPullback (genericX W) = mulByIntX W n := by
  rw [genericX_def, fieldPullback_algebraMap, mulByIntIsogeny_pullback]
  exact mulByIntPullback_X W hn

/-- **The division-polynomial Wronskian at the generic point**:

`(Φₙ' ΨSqₙ - Φₙ ΨSqₙ') u = n ΨSqₙ² ([n]*u)`,

where `u = 2y + a₁x + a₃` is the denominator of the invariant differential. It is `[n]*ω = n ω`
with `ω = dx/u` unfolded on both sides, the quotient rule applied to `[n]*x = Φₙ/ΨSqₙ`, and the
common factor `dx` cancelled. -/
theorem wronskian_Φ_ΨSq_mul_invariantDifferentialDenom [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    (aeval (genericX W) (derivative (W.Φ n)) * aeval (genericX W) (W.ΨSq n) -
          aeval (genericX W) (W.Φ n) * aeval (genericX W) (derivative (W.ΨSq n))) *
        invariantDifferentialDenom W =
      n * aeval (genericX W) (W.ΨSq n) ^ 2 *
        (mulByIntIsogeny W hn).fieldPullback (invariantDifferentialDenom W) := by
  have hΨ : aeval (genericX W) (W.ΨSq n) ≠ 0 := by
    rw [aeval_genericX_ΨSq]
    exact pow_ne_zero 2 hn
  have hu : invariantDifferentialDenom W ≠ 0 := invariantDifferentialDenom_ne_zero W
  have hpu : (mulByIntIsogeny W hn).fieldPullback (invariantDifferentialDenom W) ≠ 0 := fun h ↦
    hu ((mulByIntIsogeny W hn).fieldPullback.toRingHom.injective (by rw [map_zero]; exact h))
  have hDx : KaehlerDifferential.D F W.FunctionField (genericX W) ≠ 0 :=
    TauCeti.D_ne_zero_of_separating (transcendental_genericX W)
  have hdiv : mulByIntX W n =
      aeval (genericX W) (W.Φ n) / aeval (genericX W) (W.ΨSq n) := by
    rw [aeval_genericX_Φ, aeval_genericX_ΨSq, mulByIntX_def]
  have hω := pullbackDifferential_mulByIntIsogeny_invariantDifferential W hn
  rw [invariantDifferential_def, pullbackDifferential_smul, pullbackDifferential_D, map_inv₀,
    fieldPullback_mulByIntIsogeny_genericX W hn, hdiv, Derivation.leibniz_div,
    Derivation.map_aeval, Derivation.map_aeval] at hω
  -- both sides are now scalar multiples of `dx`; cancel it and clear the denominators
  simp only [smul_smul] at hω
  rw [← sub_smul, smul_smul, ← Int.cast_smul_eq_zsmul W.FunctionField n, smul_smul] at hω
  have hscal := smul_left_injective W.FunctionField hDx hω
  field_simp at hscal
  linear_combination hscal

end TauCeti.Isogeny

end
