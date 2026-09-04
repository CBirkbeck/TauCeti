/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The free quotient of the Mordell-Weil group, and the pairing on it

The Néron-Tate pairing vanishes as soon as either argument is torsion, so it descends to the
quotient of the points by their torsion submodule. That quotient is the free part of the
Mordell-Weil group — free of finite rank once the points are finitely generated — and it is
where the regulator is defined.

## Main definitions

* `WeierstrassCurve.Affine.FreePoint`: the points modulo torsion.
* `WeierstrassCurve.Affine.neronTatePairingFree`: the Néron-Tate pairing on that quotient.

## Main results

* `WeierstrassCurve.Affine.torsion_le_ker_neronTatePairing`: the pairing kills the torsion
  submodule, which is what the descent consumes.
* `WeierstrassCurve.Affine.neronTatePairingFree_mk`: the descended pairing agrees with the
  original on representatives.
-/

public section

open Height

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [AdmissibleAbsValues F] [DecidableEq F]

variable (W) in
/-- **The free quotient of the points**, the Mordell-Weil group modulo torsion. -/
abbrev FreePoint := W.Point ⧸ Submodule.torsion ℤ W.Point

/-- The pairing vanishes on the torsion submodule, in the form `Submodule.liftQ` consumes. -/
theorem torsion_le_ker_neronTatePairing [W.toAffine.IsElliptic] :
    Submodule.torsion ℤ W.Point ≤ (neronTatePairing W).ker := by
  intro P hP
  refine LinearMap.ext fun Q ↦ neronTatePairing_eq_zero_of_isOfFinAddOrder_left ?_ Q
  -- `Submodule.torsion_int` identifies the module-theoretic torsion with the group-theoretic one
  rwa [← AddCommGroup.mem_torsion, ← Submodule.torsion_int]

/-- The pairing is reflexive, being symmetric. -/
theorem isRefl_neronTatePairing [W.toAffine.IsElliptic] : (neronTatePairing W).IsRefl :=
  fun P Q h ↦ by rwa [neronTatePairing_comm]

variable (W) in
/-- **The Néron-Tate pairing on the free quotient.** -/
noncomputable def neronTatePairingFree [W.toAffine.IsElliptic] :
    LinearMap.BilinMap ℤ (FreePoint W) ℝ :=
  LinearMap.IsRefl.liftQ₂ (neronTatePairing W) (Submodule.torsion ℤ W.Point)
    isRefl_neronTatePairing torsion_le_ker_neronTatePairing

/-- The descended pairing agrees with the pairing on representatives. -/
@[simp]
theorem neronTatePairingFree_mk [W.toAffine.IsElliptic] (P Q : W.Point) :
    neronTatePairingFree W (Submodule.Quotient.mk P) (Submodule.Quotient.mk Q)
      = neronTatePairing W P Q := by
  simp [neronTatePairingFree]

/-- **The descended pairing is symmetric.** -/
theorem neronTatePairingFree_comm [W.toAffine.IsElliptic] (x y : FreePoint W) :
    neronTatePairingFree W x y = neronTatePairingFree W y x := by
  -- Both arguments are classes of representatives, where symmetry is `neronTatePairing_comm`.
  -- The `show` is doing real work: `Submodule.Quotient.mk` is not reducible, so the `⟦·⟧` the
  -- induction produces does not match `neronTatePairingFree_mk` syntactically, only definitionally.
  induction x, y using Quotient.inductionOn₂ with
  | _ P Q =>
    change neronTatePairingFree W (Submodule.Quotient.mk P) (Submodule.Quotient.mk Q)
      = neronTatePairingFree W (Submodule.Quotient.mk Q) (Submodule.Quotient.mk P)
    simpa using neronTatePairing_comm P Q

/-! ### The Gram matrix -/

variable (W) in
/-- **The Gram matrix of the Néron-Tate pairing** in a basis of the free quotient. -/
-- Built with `Matrix.of` rather than `LinearMap.BilinForm.toMatrixAux`, which needs the form's
-- target to be the scalar ring; here the scalars are `ℤ` and the values real.
noncomputable def gramMatrix [W.toAffine.IsElliptic] {ι : Type*}
    (b : Module.Basis ι ℤ (FreePoint W)) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ neronTatePairingFree W (b i) (b j)

@[simp]
theorem gramMatrix_apply [W.toAffine.IsElliptic] {ι : Type*}
    (b : Module.Basis ι ℤ (FreePoint W)) (i j : ι) :
    gramMatrix W b i j = neronTatePairingFree W (b i) (b j) := by
  simp [gramMatrix]

/-- **The Gram matrix is symmetric**, the pairing being so. -/
theorem gramMatrix_isSymm [W.toAffine.IsElliptic] {ι : Type*}
    (b : Module.Basis ι ℤ (FreePoint W)) : (gramMatrix W b).IsSymm := by
  ext i j
  simpa using neronTatePairingFree_comm (b j) (b i)

end WeierstrassCurve.Affine
