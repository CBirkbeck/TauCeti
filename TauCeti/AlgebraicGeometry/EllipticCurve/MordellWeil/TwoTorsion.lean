/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT

/-!
# The `2`-torsion of the group of points of a Weierstrass curve

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a field `K`. In that normal form negation is `-(x, y) = (x, -y)`, so a point is its own
negative exactly when `y = 0`, and the `2`-torsion of `W(K)` is the origin together with the
points `(x, 0)` at the roots of `f`.

The counting statement `card_ker_nsmul_two` is what turns a root count into a torsion count. It
is one side of the archimedean local-image formula of explicit `2`-descent, which reads
`#(im μ_v) = #E(ℝ)[2] / 2` at a real place.

## Main statements

* `WeierstrassCurve.Affine.card_ker_nsmul_two`: `#W(K)[2]` is the number of roots of `f` in `K`,
  plus one for the origin.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeakMordellWeil.lean` lines 806-868 — the `2`-torsion section, which sits after
the range that `TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/XSubT.lean` ported.

This advances `TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (README:813-820), whose
"Explicit `2`-descent (core, this layer)" bullet names the local conditions and the rank bound;
the archimedean local-image count needs this torsion count.
-/

public section

open Polynomial

namespace WeierstrassCurve

namespace Affine

variable {K : Type*} [Field K] (W : Affine K) [W.IsCharNeTwoNF] [W.IsElliptic] [DecidableEq K]

variable {W} in
/-- A point `(x, 0)` at a root of `f` is killed by `2`: in a characteristic `≠ 2` normal form its
negative is `(x, -0) = (x, 0)`. -/
lemma two_nsmul_some_eq_zero {x : K} (hx : W.f.eval x = 0) :
    (2 : ℕ) • (Point.some _ _ (W.nonsingular_of_eval_f_eq_zero hx) : W.Point) = 0 := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq]
  refine ⟨rfl, ?_⟩
  rw [negY_of_isCharNeTwoNF, neg_zero]

variable {W} in
/-- Conversely, an affine `2`-torsion point has `y = 0`: `(x, y) = -(x, y) = (x, -y)` forces
`2y = 0`, and `2 ≠ 0` in the base field. -/
lemma y_eq_zero_of_two_nsmul_eq_zero {x y : K}
    (h : W.Nonsingular x y) (h2 : (2 : ℕ) • (Point.some _ _ h : W.Point) = 0) : y = 0 := by
  have h20 : (2 : K) ≠ 0 := Ring.two_ne_zero <| ringChar_ne_two W
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq] at h2
  have hy : 2 * y = 0 := by linear_combination h2.2.trans (negY_of_isCharNeTwoNF ..)
  rcases mul_eq_zero.mp hy with h' | h'
  · exact absurd h' h20
  · exact h'

/-- **The `2`-torsion of `W(K)` is the origin together with the points `(x, 0)` at the roots of
`f`**, so its order is the number of roots of `f` in `K` plus one. -/
theorem card_ker_nsmul_two : Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker =
    Nat.card {x : K // W.f.eval x = 0} + 1 := by
  have hfin : Finite {x : K | W.f.eval x = 0} :=
    Set.Finite.to_subtype (Polynomial.finite_setOfPred_isRoot W.f_ne_zero)
  set pt : {x : K | W.f.eval x = 0} → W.Point :=
    fun x ↦ Point.some _ _ (W.nonsingular_of_eval_f_eq_zero x.2)
  have hinj : Function.Injective pt := by
    intro a b hab
    exact Subtype.ext ((Point.some.injEq _ _ _ _ _ _).mp hab).1
  have hset : ((nsmulAddMonoidHom (α := W.Point) 2).ker : Set W.Point) =
      insert 0 (Set.range pt) := by
    ext P
    constructor
    · intro hP
      induction P with
      | zero => exact Set.mem_insert _ _
      | some x y h =>
        have hy := y_eq_zero_of_two_nsmul_eq_zero h hP
        subst hy
        have hx : W.f.eval x = 0 := by
          have := (W.equation_iff_eval_f_eq_sq x 0).mp h.1
          simpa using this
        exact Set.mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
    · intro hP
      rcases Set.mem_insert_iff.mp hP with rfl | ⟨x, rfl⟩
      · exact zero_mem _
      · exact two_nsmul_some_eq_zero x.2
  calc Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker
      = ((nsmulAddMonoidHom (α := W.Point) 2).ker : Set W.Point).ncard := Nat.card_coe_set_eq _
    _ = (insert 0 (Set.range pt)).ncard := by rw [hset]
    _ = (Set.range pt).ncard + 1 :=
        Set.ncard_insert_of_notMem (by intro ⟨x, hx⟩; exact Point.some_ne_zero _ hx)
    _ = Nat.card {x : K // W.f.eval x = 0} + 1 := by
        rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
        rfl

end Affine

end WeierstrassCurve

end
