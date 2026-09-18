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

* `TauCeti.Isogeny.coeff_divisorPullback` and `TauCeti.Isogeny.mem_support_divisorPullback_iff`:
  the coefficient formula and the support, the characteristic API of the pullback.
* `TauCeti.Isogeny.divisorPullback_ofPoint`: the pullback of a point divisor is its fibre,
  weighted by the ramification indices.
* `TauCeti.Isogeny.divisorPullback_mono`, `TauCeti.Isogeny.isEffective_divisorPullback` and
  `TauCeti.Isogeny.divisorPullback_injective`: it is monotone, preserves effectivity, and is
  injective.
* `TauCeti.Isogeny.divisorPullback_principal`: **it carries `div z` to the divisor of the
  pulled-back function**, and `TauCeti.Isogeny.linearlyEquivalent_divisorPullback` that it
  respects linear equivalence.

Each is the corresponding `TauCeti.Divisor.conorm` result read through the isogeny; the definition
is opaque outside this module, so the wrappers are what a consumer has.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Definition 3.1.8 and
  Proposition 3.1.9.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3.
-/

public section

namespace TauCeti.Isogeny

open AlgebraicGeometry

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} (φ : Isogeny W₁ W₂)
  [Algebra W₂.FunctionField W₁.FunctionField]
  (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z)

include h in
/-- The pullback is a tower map over the base field: `fieldPullback` is an `F`-algebra map, so
`F(W₁)` is an `F(W₂)`-algebra over `F`. This is not an instance — like the algebra structure it
refines, it depends on `φ` — so a consumer of the characteristic lemmas below supplies it with
`haveI := φ.isScalarTower_of_algebraMap_eq_fieldPullback h`. -/
theorem isScalarTower_of_algebraMap_eq_fieldPullback :
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

/-! ### The coefficients and the support

These three read the place below `P'`, so their statements need the base-field tower and the
finiteness that `h` supplies; the results after them do not. -/

section Coefficients

variable [IsScalarTower F W₂.FunctionField W₁.FunctionField]
  [FiniteDimensional W₂.FunctionField W₁.FunctionField]

/-- **The defining coefficient formula**: the coefficient of `φ* D` at a place `P'` of `F(W₁)` is
`e(P' ∣ P)` times the coefficient of `D` at the place `P` below it. -/
@[simp]
theorem coeff_divisorPullback (D : Divisor F W₂.FunctionField)
    (P' : Place F W₁.FunctionField) :
    (φ.divisorPullback h D).coeff P' =
      Place.ramificationIdx W₂.FunctionField P' *
        D.coeff (P'.restrict F W₂.FunctionField) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.coeff_conorm ..

/-- A place of `F(W₁)` lies in the support of `φ* D` exactly when the place below it lies in the
support of `D`: the ramification indices are positive, so nothing cancels. -/
theorem mem_support_divisorPullback_iff {D : Divisor F W₂.FunctionField}
    {P' : Place F W₁.FunctionField} :
    P' ∈ (φ.divisorPullback h D).support ↔ P'.restrict F W₂.FunctionField ∈ D.support :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.mem_support_conorm_iff ..

/-- **The pullback of a point divisor is its fibre**, the places above `P` weighted by their
ramification indices — geometrically `φ⁻¹(P)` with multiplicity. -/
theorem divisorPullback_ofPoint (P : Place F W₂.FunctionField) :
    φ.divisorPullback h (WeilDivisor.ofPoint P) =
      WeilDivisor.ofFinsetWithMultiplicity
        (Place.finite_setOf_restrict_eq (k' := F) (F' := W₁.FunctionField) F
          W₂.FunctionField P).toFinset
        (Place.ramificationIdx W₂.FunctionField) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conorm_ofPoint ..

end Coefficients

/-- The pullback is monotone: it multiplies coefficients by positive ramification indices. -/
theorem divisorPullback_mono : Monotone (φ.divisorPullback h) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conorm_mono ..

/-- The pullback of an effective divisor is effective. -/
theorem isEffective_divisorPullback {D : Divisor F W₂.FunctionField} (hD : D.IsEffective) :
    (φ.divisorPullback h D).IsEffective :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.isEffective_conorm F W₁.FunctionField hD

/-- **The pullback is injective**: every place of `F(W₂)` is the restriction of a place of
`F(W₁)`, and the ramification indices are nonzero. -/
theorem divisorPullback_injective : Function.Injective (φ.divisorPullback h) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conorm_injective F W₁.FunctionField W₁.isFunctionField

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

/-- **The pullback respects linear equivalence** (Stichtenoth, Proposition 3.1.9), so it descends
to divisor classes. -/
theorem linearlyEquivalent_divisorPullback {A B : Divisor F W₂.FunctionField}
    (hAB : (Place.orderSystem W₂.isFunctionField).LinearlyEquivalent A B) :
    (Place.orderSystem W₁.isFunctionField).LinearlyEquivalent
      (φ.divisorPullback h A) (φ.divisorPullback h B) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.linearlyEquivalent_conorm F W₁.FunctionField W₂.isFunctionField W₁.isFunctionField hAB

end TauCeti.Isogeny

end
