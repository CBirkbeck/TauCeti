/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.DivisorClass

/-!
# The sum of a degree-zero divisor as a point

A degree-zero divisor of `F(W)` has a divisor class, and `DivisorClass.lean` identifies the
degree-zero classes with the points of `W`. Composing the two gives the sum map `σ`, which reads a
degree-zero divisor as a point, and the principal divisors are exactly those it sends to `O`.

That last statement is the principal-divisor characterisation: `Σ nᵢ (Pᵢ)` is the divisor of a
function exactly when `Σ nᵢ = 0` and `Σ [nᵢ] Pᵢ = O`. It is where the divisor calculus meets the
group law, and it is the existence criterion the divisor construction of the Weil pairing uses to
produce its functions.

## Main definitions

* `WeierstrassCurve.Affine.divisorSum`: **the sum of a degree-zero divisor**, as a point of `W`.

## Main results

* `WeierstrassCurve.Affine.mem_ker_degree_pointPlace_sub_infinity`: `(P) - (O)` has degree zero.
* `WeierstrassCurve.Affine.divisorSum_pointPlace_sub_infinity`: `σ((P) - (O)) = P`, the computation
  rule that fixes `divisorSum` on the divisors it is read off from.
* `WeierstrassCurve.Affine.divisorSum_eq_zero_iff`: **a degree-zero divisor is principal exactly
  when its sum is `O`.**

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3.4 and III.3.5.
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], I.4.
-/

public section

namespace WeierstrassCurve.Affine

open TauCeti AlgebraicGeometry IsDedekindDomain

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
  [IsDedekindDomain W.CoordinateRing] [DecidableEq F]

/-- The divisor class of a degree-zero divisor, as a degree-zero class. -/
private noncomputable def divisorClassDegreeZero :
    (Divisor.degree (k := F) (F := W.FunctionField)).ker →+
      (Divisor.degreeClass W.isFunctionField).ker :=
  AddMonoidHom.codRestrict
    (((Place.orderSystem W.isFunctionField).divisorClass).comp (AddSubgroup.subtype _)) _
    fun D ↦ by
      simpa only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        AddSubgroup.coe_subtype, Divisor.degreeClass_divisorClass] using D.2

/-- **The sum of a degree-zero divisor**, as a point of `W`: the point whose class is the class of
the divisor. On `(P) - (O)` it is `P`, and it is additive, so on `Σ nᵢ (Pᵢ)` it is `Σ [nᵢ] Pᵢ`. -/
noncomputable def divisorSum :
    (Divisor.degree (k := F) (F := W.FunctionField)).ker →+ W.Point :=
  (W.pointEquivDegreeZeroDivisorClass.symm.toAddMonoidHom).comp W.divisorClassDegreeZero

omit [DecidableEq F] in
/-- **`(P) - (O)` has degree zero**: both places are rational. -/
theorem mem_ker_degree_pointPlace_sub_infinity {x y : F} (h : W.Equation x y) :
    WeilDivisor.ofPoint (Place.ofPrime F W.FunctionField (CoordinateRing.pointPlace h)) -
        WeilDivisor.ofPoint (Place.infinity W) ∈
      (Divisor.degree (k := F) (F := W.FunctionField)).ker := by
  simp [AddMonoidHom.mem_ker, Place.degree_ofPrime,
    CoordinateRing.pointPlace.finrank_residueField_eq_one]

/-- **`σ((P) - (O)) = P`.** -/
@[simp]
theorem divisorSum_pointPlace_sub_infinity {x y : F} (h : W.Nonsingular x y) :
    W.divisorSum ⟨_, W.mem_ker_degree_pointPlace_sub_infinity h.left⟩ = Point.some x y h := by
  rw [divisorSum, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_eq]
  exact Subtype.ext (W.val_pointEquivDegreeZeroDivisorClass_some h).symm

/-- **A degree-zero divisor is principal exactly when its sum is `O`** (Silverman III.3.5). -/
theorem divisorSum_eq_zero_iff {D : (Divisor.degree (k := F) (F := W.FunctionField)).ker} :
    W.divisorSum D = 0 ↔ ∃ z : W.FunctionFieldˣ,
      Divisor.principal W.isFunctionField z = (D : Divisor F W.FunctionField) := by
  rw [← Divisor.divisorClass_eq_zero_iff, divisorSum, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_eq, map_zero]
  exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩

end WeierstrassCurve.Affine

end
