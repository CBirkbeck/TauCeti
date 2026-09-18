/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm

/-!
# Pulling a divisor back along an isogeny

An isogeny embeds `F(W₂)` in `F(W₁)` as a finite extension, and the conorm of that extension is
the pullback of divisors: the coefficient of `φ* D` at a place `P'` is `e(P' ∣ P)` times the
coefficient of `D` at the place below it. Nothing about curves enters beyond the embedding being
finite, which is what the degree of an isogeny says.

The one fact the divisor construction of the Weil pairing needs of this is that it carries
principal divisors to principal divisors: `φ*(div z)` is the divisor of the pulled-back function.
That is what lets a function with a prescribed divisor be pulled back and its divisor read off.

## Conventions

The algebra structure on `F(W₁)` over `F(W₂)` is not an instance — it depends on `φ` — so it is
taken as a parameter together with the hypothesis that its structure map is `fieldPullback`, the
form `TauCeti.Isogeny.degree_eq_finrank` and `TauCeti.Isogeny.finiteDimensional_functionField`
already use. A caller supplies it with `let _ := φ.fieldPullback.toRingHom.toAlgebra`.

## Main definitions

* `TauCeti.Isogeny.divisorPullback`: **the pullback of a divisor along an isogeny**.

## Main results

* `TauCeti.Isogeny.divisorPullback_principal`: **it carries `div z` to the divisor of the
  pulled-back function.**

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Definition 3.1.8 and
  Proposition 3.1.9.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3.
-/

public section

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} (φ : Isogeny W₁ W₂)
  [Algebra W₂.FunctionField W₁.FunctionField]
  (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z)

include h in
/-- The pullback is a tower map over the base field: `fieldPullback` is an `F`-algebra map. -/
private theorem isScalarTower_of_algebraMap_eq_fieldPullback :
    IsScalarTower F W₂.FunctionField W₁.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun c ↦
    ((h _).trans (φ.fieldPullback.commutes c)).symm

/-- **The pullback of a divisor along an isogeny**: the conorm of the finite extension of function
fields that the isogeny induces. -/
noncomputable def divisorPullback :
    Divisor F W₂.FunctionField →+ Divisor F W₁.FunctionField :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conorm F W₁.FunctionField

/-- **An isogeny carries `div z` to the divisor of the pulled-back function** (Stichtenoth,
Proposition 3.1.9). This is the step the divisor construction of the Weil pairing runs on: a
function with a prescribed divisor pulls back to one whose divisor is the pullback. -/
theorem divisorPullback_principal (z : W₂.FunctionFieldˣ) :
    φ.divisorPullback h (Divisor.principal W₂.isFunctionField z) =
      Divisor.principal W₁.isFunctionField
        (Units.map (algebraMap W₂.FunctionField W₁.FunctionField : _ →* _) z) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conorm_principal F W₁.FunctionField W₂.isFunctionField W₁.isFunctionField z

end TauCeti.Isogeny

end
