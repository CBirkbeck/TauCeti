/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic
-- `ΨSq_ne_zero` is used only inside the proof of `psiFunctionField_ne_zero` below, so private.
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

/-!
# The coordinate pullback of multiplication by `n`, for `n` invertible in the base field

`Isogeny/Basic.lean` gives the identity coordinate pullback and `Isogeny/Frobenius.lean` gives
the Frobenius one. This file gives `[n]`, for `n` invertible in `F`: multiplication by such an
`n` pulls back to a map `W.CoordinateRing →ₐ[F] W.FunctionField`.

**The hypothesis is `(n : F) ≠ 0`, not `n ≠ 0`**, so in characteristic `p` this file does not
construct `[p]`. That is a genuine limitation and not a convention: see "What is not here".

The construction is the division-polynomial formula read at the *generic* point. The coordinate
ring `W.CoordinateRing` is `F[X][Y]` modulo the Weierstrass relation, so the pair `(X, Y)` is
itself a point of `W` over the function field `W.FunctionField` — the generic point. `n` times
it has coordinates `φₙ / ψₙ²` and `ωₙ / ψₙ³` by the division-polynomial formulas, and sending
`X` and `Y` there is exactly a coordinate pullback.

## What is not here

`[p]` in characteristic `p`. Everything below asks that `n` be invertible in `F`, because the
non-vanishing of `ψₙ` at the generic point is derived from `Mathlib.ΨSq_ne_zero`, which reads
the degree off the leading coefficient `n ^ 2` — exactly what vanishes when `p ∣ n`. Every
non-vanishing lemma in Mathlib's division-polynomial development is conditional in the same way
(`preΨ_ne_zero`, `ΨSq_ne_zero`, `Ψ₃_ne_zero`, `preΨ₄_ne_zero`). The characteristic-free route
needs `IsCoprime (W.Φ n) (W.ΨSq n)` (Silverman, Exercise III.3.7), which is in neither Mathlib
nor `main` and which belongs beside the division polynomials rather than here. When it lands,
`mulByIntPullback` generalises by weakening its hypothesis to `n ≠ 0`; no statement below
changes shape.

The `MapsInfinity` condition, and so `[n]` as an `Isogeny W W`, are not proved here. Neither
criterion `Isogeny/Basic.lean` offers applies directly: `mapsInfinity_of_pow` wants a fixed
power of every coordinate function to be pulled back, which is the Frobenius shape and not this
one, and `mapsInfinity_iff_isEquiv_comap_infinityPlace` wants the induced map of *function
fields*, which is available only after the pullback below is known injective. That chain —
injectivity, the function-field map, then the place comparison — is its own topic and its own
file. Note the order of dependence: `Isogeny/FunctionField.lean` proves transcendence,
injectivity and the field pullback for *any* isogeny, but each of those consumes
`mapsInfinity`, so none of them can be used to establish it.

Two facts are the whole content here, and both are about the generic point rather than about
`n`:

* `equation_genericPoint` — the generic point satisfies the equation of the base-changed curve.
  This is the affine shadow of `AdjoinRoot.eval₂_root`: the Weierstrass polynomial is what is
  quotiented out, so it vanishes at the class of `Y`.
* `eval₂_mulByIntXHom_polynomial_eq_zero` — the pair `(φₙ/ψₙ², ωₙ/ψₙ³)` satisfies it too. This is
  *not* a polynomial identity to be checked; it holds because `n • P` is a point of the curve
  whenever `P` is, which is `WeierstrassCurve.zsmul_point_eq_smulEval` at the generic point.

## Main definitions

* `TauCeti.Isogeny.genericX`, `TauCeti.Isogeny.genericY`: the generic point of `W`.
* `TauCeti.Isogeny.mulByIntX`, `TauCeti.Isogeny.mulByIntY`: the coordinates of `[n]` there.
* `TauCeti.Isogeny.mulByIntPullback`: the coordinate pullback of `[n]`.

## Main results

* `TauCeti.Isogeny.equation_genericPoint`: the generic point is a point of `W` over the function
  field.
* `TauCeti.Isogeny.eval₂_mulByIntXHom_polynomial_eq_zero`: so is `[n]` of it.
* `TauCeti.Isogeny.psiFunctionField_ne_zero`: `ψₙ` does not vanish there when `n` is invertible
  in `F`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and the
  division-polynomial formulas of Exercise 3.7.
* Adapted from the AINTLIB `HasseWeil` project (Chris Birkbeck),
  [`HasseWeil/MulByIntPullback.lean`](https://github.com/CBirkbeck/AINTLIB), Apache-2.0, at commit
  `513e83879e2f8cbc626eb9e04d660e92be16ccba`, declarations `x_gen`, `y_gen`, `W_KE`,
  `generic_equation`, `Φ_ff`, `ΨSq_ff`, `ψ_ff`, `ω_ff`, `mulByInt_x`, `mulByInt_y`,
  `mulByInt_xHom`, `mulByInt_weierstrass` and `mulByInt_coordHom`. The source stops at a
  `RingHom` out of the coordinate ring and then builds its own function-field pullback,
  injectivity and transcendence statements by hand; here the ring hom is upgraded to the
  `AlgHom` that `TauCeti.CoordinatePullback` already asks for, and those three consequences are
  read off `Isogeny/FunctionField.lean` instead of being reproved.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate

namespace TauCeti

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

namespace Isogeny

/-- The generic `x`-coordinate: the class of `X` in the function field. -/
noncomputable def genericX : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (algebraMap F[X] W.CoordinateRing X)

/-- The generic `y`-coordinate: the class of `Y` in the function field. -/
noncomputable def genericY : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.root W.polynomial)

/-- `W` base-changed to its own function field. The generic point is a point of it. -/
noncomputable abbrev functionFieldCurve : WeierstrassCurve.Affine W.FunctionField :=
  W.map (algebraMap F W.FunctionField)

/-- The composite `F → W.FunctionField` factors through the coordinate ring. Used to turn
statements about the base-changed curve into statements about images under
`algebraMap W.CoordinateRing W.FunctionField`. -/
theorem algebraMap_functionField_eq_comp :
    (algebraMap F W.FunctionField : F →+* W.FunctionField) =
      (algebraMap W.CoordinateRing W.FunctionField).comp (algebraMap F W.CoordinateRing) :=
  (IsScalarTower.algebraMap_eq F W.CoordinateRing W.FunctionField).symm

/-- **Evaluating at the generic point is reduction modulo the Weierstrass relation.** A bivariate
polynomial over `F`, pushed to the function field and evaluated at `(genericX, genericY)`, is the
image of its class in the coordinate ring.

This is the workhorse: it converts every division-polynomial value at the generic point into the
image of a coordinate-ring element, where the ring's own API applies. -/
theorem evalEval_genericPoint (p : F[X][Y]) :
    (p.map (mapRingHom (algebraMap F W.FunctionField))).evalEval (genericX W) (genericY W) =
      algebraMap W.CoordinateRing W.FunctionField (Affine.CoordinateRing.mk W p) := by
  conv_lhs =>
    rw [algebraMap_functionField_eq_comp W, ← mapRingHom_comp, ← Polynomial.map_map]
  set g := algebraMap W.CoordinateRing W.FunctionField
  set q := Polynomial.map (mapRingHom (algebraMap F W.CoordinateRing)) p with hq
  -- `genericX` and `genericY` are already of the form `g _`; say so, or the rewrite below
  -- cannot see its own pattern `evalEval (g _) (g _) (map (mapRingHom g) _)`.
  change (q.map (mapRingHom g)).evalEval (g _) (g _) = g _
  rw [Polynomial.map_mapRingHom_evalEval]
  congr 1
  rw [hq]
  rw [← Polynomial.eval₂_eval₂RingHom_apply]
  have hinner : eval₂RingHom (algebraMap F W.CoordinateRing) (algebraMap F[X] W.CoordinateRing X) =
      algebraMap F[X] W.CoordinateRing := by
    ext x
    · simp [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing]
    · simp
  rw [hinner, ← Polynomial.aeval_def]
  exact AdjoinRoot.aeval_eq p

/-- **The generic point is a point of the curve.** `(X, Y)` satisfies the equation of `W`
base-changed to the function field, because the Weierstrass polynomial is precisely what the
coordinate ring quotients out. -/
theorem equation_genericPoint : (functionFieldCurve W).Equation (genericX W) (genericY W) := by
  change (W.map (algebraMap F W.FunctionField)).polynomial.evalEval _ _ = 0
  rw [Affine.map_polynomial, evalEval_genericPoint W W.polynomial,
    AdjoinRoot.mk_self, map_zero]

/-- The generic point is nonsingular, so it is an affine point of the base-changed curve. -/
theorem nonsingular_genericPoint [W.IsElliptic] :
    (functionFieldCurve W).Nonsingular (genericX W) (genericY W) :=
  Affine.equation_iff_nonsingular.mp (equation_genericPoint W)

/-- The image of `ψₙ` in the function field. -/
noncomputable def psiFunctionField (n : ℤ) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (Affine.CoordinateRing.mk W (W.ψ n))

/-- The image of `ωₙ` in the function field. -/
noncomputable def omegaFunctionField (n : ℤ) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (Affine.CoordinateRing.mk W (W.ω n))

/-- The image of `φₙ` in the function field. -/
noncomputable def phiFunctionField (n : ℤ) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (Affine.CoordinateRing.mk W (W.φ n))

/-- The `x`-coordinate of `[n]` at the generic point, `φₙ / ψₙ²`. -/
noncomputable def mulByIntX (n : ℤ) : W.FunctionField :=
  phiFunctionField W n / psiFunctionField W n ^ 2

/-- The `y`-coordinate of `[n]` at the generic point, `ωₙ / ψₙ³`. -/
noncomputable def mulByIntY (n : ℤ) : W.FunctionField :=
  omegaFunctionField W n / psiFunctionField W n ^ 3

/-- The ring hom `F[X] → W.FunctionField` sending `X` to the `x`-coordinate of `[n]`. -/
noncomputable def mulByIntXHom (n : ℤ) : F[X] →+* W.FunctionField :=
  eval₂RingHom (algebraMap F W.FunctionField) (mulByIntX W n)

/-- The `Z`-coordinate of the Jacobian triple of `[n]` at the generic point is `ψₙ`. -/
theorem smulEval_genericPoint_two (n : ℤ) :
    smulEval (functionFieldCurve W) (genericX W) (genericY W) n 2 = psiFunctionField W n := by
  change ((W.map (algebraMap F W.FunctionField)).ψ n).evalEval _ _ = _
  rw [map_ψ, psiFunctionField]
  exact evalEval_genericPoint W (W.ψ n)

/-- The `X`-coordinate of the Jacobian triple of `[n]` at the generic point is `φₙ`. -/
theorem smulEval_genericPoint_zero (n : ℤ) :
    smulEval (functionFieldCurve W) (genericX W) (genericY W) n 0 = phiFunctionField W n := by
  change ((W.map (algebraMap F W.FunctionField)).φ n).evalEval _ _ = _
  rw [map_φ, phiFunctionField]
  exact evalEval_genericPoint W (W.φ n)

/-- The `Y`-coordinate of the Jacobian triple of `[n]` at the generic point is `ωₙ`. -/
theorem smulEval_genericPoint_one (n : ℤ) :
    smulEval (functionFieldCurve W) (genericX W) (genericY W) n 1 = omegaFunctionField W n := by
  change ((W.map (algebraMap F W.FunctionField)).ω n).evalEval _ _ = _
  rw [map_ω, omegaFunctionField]
  exact evalEval_genericPoint W (W.ω n)

/-- `ψₙ² = ΨSqₙ` in the function field: the division polynomial's square is the univariate
`ΨSq`, already known in the coordinate ring as `mk_ψ` followed by `mk_Ψ_sq`. -/
theorem psiFunctionField_sq (n : ℤ) : psiFunctionField W n ^ 2 =
      algebraMap W.CoordinateRing W.FunctionField (Affine.CoordinateRing.mk W (C (W.ΨSq n))) := by
  rw [psiFunctionField, ← map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]

/-- **The generic point of `[n]` satisfies the Weierstrass equation.**

This is the fact that makes `[n]` a coordinate pullback at all, and it is *not* a polynomial
identity: it holds because `n • P` is again a point of the curve whenever `P` is. Concretely,
`zsmul_point_eq_smulEval` identifies `n • (generic point)` with the Jacobian class of
`(φₙ : ωₙ : ψₙ)`, that class is nonsingular because it is a point, and `ψₙ ≠ 0` lets it be read
in affine coordinates — where it becomes exactly this equation. -/
theorem eval₂_mulByIntXHom_polynomial_eq_zero [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    eval₂ (mulByIntXHom W n) (mulByIntY W n) W.polynomial = 0 := by
  have hns := nonsingular_genericPoint W
  change eval₂ (eval₂RingHom (algebraMap F W.FunctionField) (mulByIntX W n)) _ _ = 0
  rw [eval₂_eval₂RingHom_apply,
    show Polynomial.map (mapRingHom (algebraMap F W.FunctionField)) W.polynomial =
      (functionFieldCurve W).polynomial from (Affine.map_polynomial W _).symm]
  have hsmul : Jacobian.Nonsingular (functionFieldCurve W).toJacobian
      (smulEval (functionFieldCurve W) (genericX W) (genericY W) n) := by
    rw [← Jacobian.nonsingularLift_iff, ← zsmul_point_eq_smulEval _ hns n]
    exact (n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)).nonsingular
  have hZ : smulEval (functionFieldCurve W) (genericX W) (genericY W) n 2 ≠ 0 := by
    rw [smulEval_genericPoint_two]; exact hn
  have hJ := (Jacobian.equation_of_Z_ne_zero hZ).mp hsmul.1
  rwa [smulEval_genericPoint_zero, smulEval_genericPoint_one, smulEval_genericPoint_two,
    show phiFunctionField W n / psiFunctionField W n ^ 2 = mulByIntX W n from rfl,
    show omegaFunctionField W n / psiFunctionField W n ^ 3 = mulByIntY W n from rfl] at hJ

/-- **`ψₙ` does not vanish at the generic point** when `n` is invertible in `F`.

The hypothesis is on `n` in `F`, not on `n` in `ℤ`: in characteristic `p` it excludes `n = p`.
That case is true too, but it is not reachable from what is currently available. Every
non-vanishing lemma in Mathlib's division-polynomial development is characteristic-conditional
in the same way — `preΨ_ne_zero`, `ΨSq_ne_zero`, `Ψ₃_ne_zero`, `preΨ₄_ne_zero` — because each
is proved from a leading coefficient (`(W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2`), and that
is exactly what vanishes when `p ∣ n`. The char-free route instead needs
`IsCoprime (W.Φ n) (W.ΨSq n)` (Silverman, Exercise III.3.7), which is in neither Mathlib nor
`main`; proving it goes through an algebraically closed base change and belongs beside the
division polynomials rather than here.

So `mulByIntPullback` takes the non-vanishing as a *hypothesis* rather than deriving it, and
this lemma discharges that hypothesis in the case that is available. The construction itself
carries no characteristic restriction, so when the coprimality lands the general case follows
with nothing here restated — only a second discharge lemma beside this one. -/
theorem psiFunctionField_ne_zero {n : ℤ} (hn : (n : F) ≠ 0) : psiFunctionField W n ≠ 0 := by
  intro h
  have hΨ : W.ΨSq n ≠ 0 := WeierstrassCurve.ΨSq_ne_zero W hn
  refine hΨ ?_
  have hzero : algebraMap W.CoordinateRing W.FunctionField
      (Affine.CoordinateRing.mk W (C (W.ΨSq n))) = 0 := by
    rw [← psiFunctionField_sq, h, zero_pow two_ne_zero]
  rw [show Affine.CoordinateRing.mk W (C (W.ΨSq n)) =
    algebraMap F[X] W.CoordinateRing (W.ΨSq n) from rfl] at hzero
  exact FaithfulSMul.algebraMap_injective F[X] W.CoordinateRing
    ((FaithfulSMul.algebraMap_injective W.CoordinateRing W.FunctionField
      (hzero.trans (map_zero _).symm)).trans (map_zero _).symm)

/-- **The coordinate pullback of `[n]`.** The coordinate ring is `F[X]` with a root of the
Weierstrass polynomial adjoined, so a map out of it is exactly a value for `X` together with a
value for `Y` satisfying that polynomial — here `φₙ/ψₙ²` and `ωₙ/ψₙ³`, which satisfy it by
`eval₂_mulByIntXHom_polynomial_eq_zero`.

`AdjoinRoot.lift` produces a ring hom; `CoordinatePullback` asks for an `F`-algebra hom, and the
two agree because the lift sends a constant to itself.

Defined only for `n` invertible in `F`. In characteristic `p` this does not give `[p]`; the
obstruction is `psiFunctionField_ne_zero`, and the file header says what closing it needs. -/
noncomputable def mulByIntPullback [W.IsElliptic] {n : ℤ} (hnF : (n : F) ≠ 0) :
    CoordinatePullback W W :=
  { AdjoinRoot.lift (mulByIntXHom W n) (mulByIntY W n)
      (eval₂_mulByIntXHom_polynomial_eq_zero W (psiFunctionField_ne_zero W hnF)) with
    commutes' := fun r ↦ by
      rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing]
      simp [mulByIntXHom] }

/-- The pullback of `[n]` sends the class of `X` to `φₙ/ψₙ²`.

Stated with `AdjoinRoot.of`, not `algebraMap F[X] W.CoordinateRing`, because
`AdjoinRoot.algebraMap_eq` is itself a `simp` lemma: a goal mentioning the class of `X` is
already normalised this way by the time this fires. -/
@[simp]
theorem mulByIntPullback_genericX [W.IsElliptic] {n : ℤ} (hnF : (n : F) ≠ 0) :
    mulByIntPullback W hnF (AdjoinRoot.of W.polynomial X) = mulByIntX W n := by
  simp [mulByIntPullback, mulByIntXHom]

/-- The pullback of `[n]` sends the class of `Y` to `ωₙ/ψₙ³`. -/
@[simp]
theorem mulByIntPullback_genericY [W.IsElliptic] {n : ℤ} (hnF : (n : F) ≠ 0) :
    mulByIntPullback W hnF (AdjoinRoot.root W.polynomial) = mulByIntY W n := by
  simp [mulByIntPullback]

end Isogeny

end TauCeti
