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

at the generic point. The other half rewrites `ΨSqₙ² ([n]*u)` as `preΨ_{2n} u`, through the two
identities `ψc` is defined by, and the two together give the classical polynomial identity

`Φₙ' ΨSqₙ - Φₙ ΨSqₙ' = n · preΨ_{2n}`  in  `F[X]`,

by cancelling `u` and descending along the injective `algebraMap F[X] → F(W)`.

That identity is what supplies the multiplicity-one step in the unramifiedness of `[n]`
(Silverman III.4.10(c)): the fibre polynomial `Φₙ - x_Q · ΨSqₙ` has a simple root at the
`x`-coordinate of each preimage, because its derivative there is `n · preΨ_{2n} / ΨSqₙ ≠ 0`.
Unramifiedness is in turn what counts `E[N]` as the fibre of `[N]` over `O` once the fundamental
identity is applied, so this is a prerequisite of the separable-implies-unramified milestone
rather than a self-contained curiosity.

## Main results

* `TauCeti.Isogeny.wronskian_Φ_ΨSq_mul_invariantDifferentialDenom`: the identity above.
* `TauCeti.Isogeny.psiFunctionField_cube_mul_fieldPullback_invariantDifferentialDenom`:
  `ψₙ³ ([n]*u) = ψcₙ`, the first half of the `preΨ` bridge, and
  `TauCeti.Isogeny.aeval_ΨSq_sq_mul_fieldPullback_invariantDifferentialDenom`:
  `ΨSqₙ² ([n]*u) = preΨ_{2n} u`, the bridge itself.
* `TauCeti.Isogeny.wronskian_Φ_ΨSq`: **the classical polynomial identity**
  `Φₙ' ΨSqₙ - Φₙ ΨSqₙ' = n · preΨ_{2n}`, for every integer `n`.

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

/-! ### The `ψc` bridge

`[n]*u` is `u` read at the image point `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)`, so clearing `ψₙ³` turns it into the
left-hand side of `ω_spec`, the identity `ψc` is defined by. -/

/-- The pullback of `[n]` sends the generic `y` to `[n]*y = ωₙ/ψₙ³`. -/
private theorem fieldPullback_mulByIntIsogeny_genericY [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    (mulByIntIsogeny W hn).fieldPullback (genericY W) = mulByIntY W n := by
  rw [genericY_def, fieldPullback_algebraMap, mulByIntIsogeny_pullback]
  exact mulByIntPullback_Y W hn

/-- **The defining identity for `ψc` at the generic point**: `2 ωₙ + a₁ φₙ ψₙ + a₃ ψₙ³ = ψcₙ`. -/
private theorem two_mul_omega_add_eq_psic (n : ℤ) :
    2 * omegaFunctionField W n +
        algebraMap F W.FunctionField W.a₁ * phiFunctionField W n * psiFunctionField W n +
        algebraMap F W.FunctionField W.a₃ * psiFunctionField W n ^ 3 =
      psicFunctionField W n := by
  have hC : ∀ a : F, algebraMap F[X] W.FunctionField (C a) = algebraMap F W.FunctionField a :=
    fun a ↦ by rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  have h := congrArg (fun p ↦ algebraMap W.CoordinateRing W.FunctionField
    (CoordinateRing.mk W p)) (W.ω_spec n)
  simpa only [map_add, map_mul, map_pow, map_ofNat,
    CoordinateRing.mk_C_eq_algebraMap, ← IsScalarTower.algebraMap_apply, hC,
    omegaFunctionField_def, phiFunctionField_def, psiFunctionField_def,
    psicFunctionField_def] using h

/-- **`ψₙ³ · ([n]*u) = ψcₙ`.** The pullback of `u = 2y + a₁x + a₃` along `[n]` is `u` read at the
image point `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)`, so clearing `ψₙ³` turns it into `2 ωₙ + a₁ φₙ ψₙ + a₃ ψₙ³`, which
is the left-hand side of `ω_spec` — the identity `ψc` is defined by.

This is the first half of the bridge from `[n]*u` to the division polynomials: combined with the
complement identity `ψₙ ψcₙ = ψ_{2n}` it rewrites `ΨSqₙ² ([n]*u)` as `preΨ_{2n} u`, which is what
turns the Wronskian above into the polynomial identity
`Φₙ' ΨSqₙ - Φₙ ΨSqₙ' = n · preΨ_{2n}`. -/
theorem psiFunctionField_cube_mul_fieldPullback_invariantDifferentialDenom [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    psiFunctionField W n ^ 3 *
        (mulByIntIsogeny W hn).fieldPullback (invariantDifferentialDenom W) =
      psicFunctionField W n := by
  simp only [invariantDifferentialDenom_def, map_add, map_mul, map_ofNat, AlgHom.commutes]
  rw [fieldPullback_mulByIntIsogeny_genericX W hn, fieldPullback_mulByIntIsogeny_genericY W hn,
    mulByIntX_def, mulByIntY_def, ← two_mul_omega_add_eq_psic]
  field_simp

/-- **`ψₙ ψcₙ = ψ_{2n}` at the generic point**, the complement identity `ψc` is named for. -/
private theorem psi_mul_psic (n : ℤ) :
    psiFunctionField W n * psicFunctionField W n = psiFunctionField W (2 * n) := by
  have h := congrArg (fun p ↦ algebraMap W.CoordinateRing W.FunctionField
    (CoordinateRing.mk W p)) (W.ψ_mul_ψc n)
  simpa only [map_mul, psiFunctionField_def, psicFunctionField_def] using h

/-- **`ψ₂` at the generic point is `u`.** Mathlib defines `ψ₂` as `polynomialY`, whose value at
the generic point is `2y + a₁x + a₃`. -/
private theorem algebraMap_mk_psi_two :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W W.ψ₂) =
      invariantDifferentialDenom W := by
  have hC : ∀ a : F, algebraMap F[X] W.FunctionField (C a) = algebraMap F W.FunctionField a :=
    fun a ↦ by rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  rw [invariantDifferentialDenom_def, WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY,
    genericX_def, genericY_def]
  simp only [map_add, map_mul, map_ofNat, CoordinateRing.mk_C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply, hC]
  ring

/-- **`ψ_{2n}` at the generic point is `preΨ_{2n} · u`**: `Ψ` at an even argument is
`C (preΨ) * ψ₂`, and `ψ` and `Ψ` agree in the coordinate ring. -/
private theorem psiFunctionField_two_mul (n : ℤ) :
    psiFunctionField W (2 * n) =
      algebraMap F[X] W.FunctionField (W.preΨ (2 * n)) * invariantDifferentialDenom W := by
  rw [psiFunctionField_def, CoordinateRing.mk_ψ, WeierstrassCurve.Ψ]
  simp only [even_two_mul, ite_true, map_mul, CoordinateRing.mk_C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply, algebraMap_mk_psi_two]

/-- **The `preΨ` bridge**: `ΨSqₙ² ([n]*u) = preΨ_{2n} u`.

This is what turns the Wronskian above into the polynomial identity
`Φₙ' ΨSqₙ - Φₙ ΨSqₙ' = n · preΨ_{2n}`: `ΨSqₙ² = ψₙ⁴`, so the left-hand side is
`ψₙ · (ψₙ³ ([n]*u)) = ψₙ ψcₙ = ψ_{2n}`, and `ψ_{2n}` is `preΨ_{2n} · ψ₂ = preΨ_{2n} · u`. -/
theorem aeval_ΨSq_sq_mul_fieldPullback_invariantDifferentialDenom [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    aeval (genericX W) (W.ΨSq n) ^ 2 *
        (mulByIntIsogeny W hn).fieldPullback (invariantDifferentialDenom W) =
      algebraMap F[X] W.FunctionField (W.preΨ (2 * n)) * invariantDifferentialDenom W := by
  rw [← psiFunctionField_two_mul, ← psi_mul_psic,
    ← psiFunctionField_cube_mul_fieldPullback_invariantDifferentialDenom W hn,
    aeval_genericX_ΨSq]
  ring

/-- **The division-polynomial Wronskian**, in its classical polynomial form:

`Φₙ' ΨSqₙ - Φₙ ΨSqₙ' = n · preΨ_{2n}`  in  `F[X]`,

for **every** integer `n`. The function-field route below needs `ψₙ` to be invertible there, but
that is no restriction on the statement: on an elliptic curve `ψₙ` vanishes at the generic point
only for `n = 0` (`psiFunctionField_ne_zero_of_Δ_ne_zero`), and at `n = 0` both sides are `0`
because `ΨSq₀ = 0` and `preΨ₀ = 0`.

Away from `0` the two halves above give it over `F(W)` after cancelling `u`, and
`algebraMap F[X] → F(W)` is injective because the generic coordinate is transcendental. -/
theorem wronskian_Φ_ΨSq [W.IsElliptic] (n : ℤ) :
    derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n) =
      C ((n : ℤ) : F) * W.preΨ (2 * n) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have hn : psiFunctionField W n ≠ 0 :=
    psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero hn0
  refine FaithfulSMul.algebraMap_injective F[X] W.FunctionField ?_
  have hu : invariantDifferentialDenom W ≠ 0 := invariantDifferentialDenom_ne_zero W
  have hA := wronskian_Φ_ΨSq_mul_invariantDifferentialDenom W hn
  rw [mul_assoc, aeval_ΨSq_sq_mul_fieldPullback_invariantDifferentialDenom W hn,
    ← mul_assoc] at hA
  have hcancel := mul_right_cancel₀ hu hA
  simpa only [map_sub, map_mul, W.algebraMap_eq_aeval_genericX, Polynomial.aeval_C,
    map_intCast] using hcancel

end TauCeti.Isogeny

end
