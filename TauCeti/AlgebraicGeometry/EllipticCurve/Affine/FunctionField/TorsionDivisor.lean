/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Sum

/-!
# Two principal divisors from the group law

A degree-zero divisor on an elliptic curve is principal exactly when its sum is `O`
(`WeierstrassCurve.Affine.divisorSum_eq_zero_iff`), and the sum of `(P) - (Q)` is `P - Q`
(`WeierstrassCurve.Affine.divisorSum_ofPoint_sub_ofPoint`). This file records the two instances the
divisor construction of the Weil pairing (Silverman III.8.1) uses:

* at an `n`-torsion point `T`, the divisor `n(T) - n(O)` is principal, its sum being `n • T`;
* for any points `P` and `Q`, the divisor `(P + Q) - (P) - ((Q) - (O))` is principal, its sum being
  `O`. This is the divisor of the line function relating `P`, `Q` and `P + Q`.

Points are read as places through `WeierstrassCurve.Affine.pointEquivDegreeOnePlace`, which sends
`O` to the place at infinity.

## Main results

* `WeierstrassCurve.Affine.exists_principal_zsmul_ofPoint_sub_infinity`: at an `n`-torsion point
  `T`, the divisor `n(T) - n(O)` is the divisor of a function.
* `WeierstrassCurve.Affine.exists_principal_eq_ofPoint_add_sub`: `(P + Q) - (P) - ((Q) - (O))` is
  the divisor of a function.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3.5, III.8.1.
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], I.4.
-/

public section

namespace WeierstrassCurve.Affine

open TauCeti AlgebraicGeometry IsDedekindDomain

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
  [IsDedekindDomain W.CoordinateRing] [DecidableEq F] [W.IsElliptic]

/-- **At an `n`-torsion point, `n(T) - n(O)` is the divisor of a function** (Silverman III.8.1). -/
theorem exists_principal_zsmul_ofPoint_sub_infinity {n : ℤ} {T : W.Point} (hT : n • T = 0) :
    ∃ z : W.FunctionFieldˣ, Divisor.principal W.isFunctionField z =
      n • (WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace T).1 -
        WeilDivisor.ofPoint (Place.infinity W)) := by
  rw [← coe_pointEquivDegreeOnePlace_zero]
  exact W.divisorSum_eq_zero_iff (D := n • ⟨_, W.ofPoint_sub_ofPoint_mem_ker_degree T .zero⟩) |>.1
    (by rw [map_zsmul, divisorSum_ofPoint_sub_ofPoint, ← Point.zero_def, sub_zero, hT])

/-- **The line function**: `(P + Q) - (P) - ((Q) - (O))` is the divisor of a function, its sum
being `(P + Q) - P - Q = O` (Silverman III.3.5). -/
theorem exists_principal_eq_ofPoint_add_sub (P Q : W.Point) :
    ∃ z : W.FunctionFieldˣ, Divisor.principal W.isFunctionField z =
      WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace (P + Q)).1 -
        WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace P).1 -
        (WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace Q).1 -
          WeilDivisor.ofPoint (Place.infinity W)) := by
  rw [← coe_pointEquivDegreeOnePlace_zero]
  exact W.divisorSum_eq_zero_iff (D := ⟨_, W.ofPoint_sub_ofPoint_mem_ker_degree (P + Q) P⟩ -
    ⟨_, W.ofPoint_sub_ofPoint_mem_ker_degree Q .zero⟩) |>.1
    (by rw [map_sub, divisorSum_ofPoint_sub_ofPoint, divisorSum_ofPoint_sub_ofPoint,
      ← Point.zero_def, sub_zero, add_sub_cancel_left, sub_self])

end WeierstrassCurve.Affine

end
