/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.EllipticCurve
public import Mathlib.NumberTheory.Height.Northcott
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Duplication

/-!
# The naïve height on an elliptic curve, and the approximate parallelogram law

For an affine point `P` of a Weierstrass curve over a field `K` with a theory of heights, the
*naïve height* is `h(P) = logHeight (x(P))`, the logarithmic height of the projective
`x`-coordinate `P.xRep`. The main result is the **approximate parallelogram law**,

```text
∃ C, ∀ P Q, |h(P + Q) + h(P - Q) - 2 * (h(P) + h(Q))| ≤ C,
```

which is the height half of the descent proving the Mordell–Weil theorem. Together with the
Northcott property it gives finiteness of the sets of points of bounded naïve height.

The route is the one the source takes: the unordered pair `{P, Q}` is recorded by the symmetric
function `sym2x P Q` of the two `x`-coordinates, the map `{P, Q} ↦ {P + Q, P - Q}` is induced on
those symmetric functions by the quadratic `addSubMap`, and the height of a value of a
homogeneous polynomial map is controlled by the height of its argument. The commuting square
holds only up to a nonzero scalar, which is harmless because `logHeight` is scale-invariant.

The affine-coordinate arithmetic it runs on — the duplication formulae, the `x`-coordinate
addition formulae, their transport to `Point.xRep`, and finiteness of the fibres of `xRep` —
mentions no height and lives in
`TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Duplication`.

The `sym2x` section below stays here rather than moving beside it because
`Point.sym2x_eq_xRep` is `private`: it is shared by the commuting square and by
`abs_logHeight_sym2x_sub_le`, and `private` does not cross a module boundary, so separating them
would require making that bridge public again — which is exactly the duplication of Mathlib's
`sym2x` that the review asked to remove.

## Main results

* `WeierstrassCurve.Affine.Point.naiveHeight` : the naïve height `logHeight P.xRep`.
* `WeierstrassCurve.Affine.Point.exists_smul_sym2x_add_sub_eq_addSubMap_sym2x` : the commuting
  square, up to a nonzero scalar.
* `WeierstrassCurve.Affine.approx_parallelogram_law` : the approximate parallelogram law.
* `WeierstrassCurve.Affine.finite_naiveHeight_le` : finiteness of points of bounded naïve height.

## Relation to Mathlib, and the duplication risk, weighed

The infrastructure this rests on is Mathlib's and is *consumed*, not restated: `Point.xRep`,
`addSubMap`, `addSubMapCoeff`, `isHomogeneous_addSubMap` and `sym2x`, the height API, and in
particular `abs_logHeight_addSubMap_sub_two_mul_logHeight_le`, the polynomial-map height bound the
parallelogram law consumes.

That last lemma lives in `Mathlib/NumberTheory/Height/EllipticCurve.lean`, a file by the same
author as this development's source, whose module docstring is titled "The naïve height and the
approximate parallelogram law" and whose `TODO` list names three items: define the naïve height,
add the further ingredients for the approximate parallelogram law, and add the law itself. The
source also brackets the duplication block with a reference to Mathlib PR `#40303`. So the
material here is work the upstream author has slotted but not landed: at the Mathlib version this
repository pins, all of these declarations are absent, which is why they are stated here rather
than imported.

This is a deliberate, temporary duplication with a defined end. If a later pin bump lands that
upstream work, the superseded declarations here must be deleted and their uses repointed at
Mathlib in the same pull request, per this repository's no-compatibility-shims rule.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/MordellWeil.lean`, Apache-2.0.
-/

public section

open Height MvPolynomial Nat

namespace WeierstrassCurve

namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ### `sym2x` and the addition-and-multiplication map -/

/-- `sym2x` written out in the projective `xRep` coordinates.

`private`, and stated rather than unfolded, because Mathlib's `sym2x` is **not exposed**:
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/AddSubMap.lean` opens a plain `public section`, so
across the module boundary the body is unavailable and both `simp [Point.sym2x]` and
`rw [Point.sym2x]` are rejected outright — `Invalid simp theorem \`sym2x\`: Expected a definition
with an exposed body`, and `Invalid rewrite argument`. Mathlib exports only the four
per-constructor `@[simp]` lemmas, so the general equation is recovered here by matching on those
four cases. It is private because it is a local proof bridge, not API: the canonical `sym2x`
remains Mathlib's. -/
private lemma Point.sym2x_eq_xRep (P Q : W.Point) :
    P.sym2x Q = ![P.xRep 0 * Q.xRep 0, P.xRep 0 * Q.xRep 1 + P.xRep 1 * Q.xRep 0,
      P.xRep 1 * Q.xRep 1] := by
  match P, Q with
  | 0, 0 => simp [Point.xRep_zero]
  | 0, .some x y h => simp [Point.xRep_zero, Point.xRep_some]
  | .some x y h, 0 => simp [Point.xRep_zero, Point.xRep_some]
  | .some x y h, .some x' y' h' => simp [Point.xRep_some]

private lemma Point.sym2x_P_P_eq_addSubMap (P : W.Point) :
    sym2x P P = fun i ↦ (addSubMap W i).eval <| P.sym2x 0 := by
  match P with
  | 0 =>
    simp only [sym2x_zero_zero, succ_eq_add_one, reduceAdd, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp
  | some .. =>
    simp only [sym2x_some_some, succ_eq_add_one, reduceAdd, sym2x_some_zero, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp [pow_two, two_mul]

section Decidable

variable [DecidableEq F]

private lemma Point.sym2x_P_add_P_zero (P : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + P) 0 = fun i ↦ (addSubMap W i).eval <| P.sym2x P := by
  match P with
  | 0 =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [add_zero, sym2x_zero_zero, one_smul, addSubMap]
    ext i : 1
    fin_cases i <;> simp
  | some x y h =>
    have Heq := (W.equation_iff x y).mp h.1
    have Hrs : (fun i ↦ (addSubMap W i).eval <| (some x y h).sym2x (some x y h)) =
          ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
            4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
      ext i : 1
      fin_cases i <;> simp [addSubMap] <;> ring
    rw [Hrs]
    by_cases! H : y = W.negY x y
    · have H' := (den_duplication_eq_zero_iff h.1).mpr H
      rw [H', add_self_of_Y_eq H, sym2x_zero_zero]
      refine ⟨_, den_duplication_ne_zero_or_num_duplication_ne_zero h |>.neg_resolve_left H', ?_⟩
      simp
    · have H' := (den_duplication_eq_zero_iff h.1).not.mpr H
      refine ⟨_, H', ?_⟩
      simp [Point.sym2x_eq_xRep, Point.xRep_add_self_of_Y_ne h H, mul_div_cancel₀ _ H']

/-- `sym2x (P + Q) (P - Q)` is equal, up to scaling by a nonzero constant, to `addSubMap W`
applied to `sym2x P Q`. -/
lemma Point.exists_smul_sym2x_add_sub_eq_addSubMap_sym2x (P Q : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) = fun i ↦ (addSubMap W i).eval <| sym2x P Q := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_P_add_P_zero
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [sym2x_neg_right, Point.sym2x_comm 0] using P.sym2x_P_add_P_zero
  match P, Q with
  | P, 0 =>  exact ⟨1, one_ne_zero, by simpa using P.sym2x_P_P_eq_addSubMap⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [sym2x_neg_right, sym2x_comm _ Q] using Q.sym2x_P_P_eq_addSubMap
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := fun Heq ↦ by grind only [X_eq_iff.mp Heq]
    have Hrs : (fun i ↦ (addSubMap W i).eval <| (some xP yP hP).sym2x (some xQ yQ hQ)) =
        ![(xP * xQ) ^ 2 - W.b₄ * (xP * xQ) - W.b₆ * (xP + xQ) - W.b₈,
          2 * (xP + xQ) * (xP * xQ) + W.b₂ * (xP * xQ) + W.b₄ * (xP + xQ) + W.b₆,
          (xP - xQ) ^ 2] := by
      ext i : 1
      fin_cases i <;> simp [addSubMap]
      ring
    have : xP - xQ ≠ 0 := sub_ne_zero_of_ne hxPQ
    refine ⟨(xP - xQ) ^ 2, pow_ne_zero 2 this, ?_⟩
    -- The following relations are needed for the `grobner` calls below.
    have HeqP := (W.equation_iff xP yP).mp hP.1
    have HeqQ := (W.equation_iff xQ yQ).mp hQ.1
    rw [Hrs, Point.sym2x_eq_xRep, Point.xRep_add_of_X_ne hP hQ hxPQ,
      Point.xRep_sub_of_X_ne hP hQ hxPQ,
      b₂, b₄, b₆, b₈]
    ext i : 1
    fin_cases i <;> simp [field] <;> grobner

end Decidable

/-! ### The naïve height -/

section AAV

variable [AdmissibleAbsValues F]

/-- The naïve logarithmic height of an affine point on `W`. -/
noncomputable def Point.naiveHeight (P : W.Point) : ℝ :=
  logHeight P.xRep

@[simp]
lemma Point.naiveHeight_eq_logHeight (P : W.Point) : P.naiveHeight = logHeight P.xRep := by
  simp [Point.naiveHeight]

lemma Point.naiveHeight_eq_logHeight₁ {P : W.Point} :
    P.naiveHeight = logHeight₁ (P.xRep 0) := by
  match P with
  | 0 => simp [naiveHeight, xRep]
  | some .. => simpa [naiveHeight] using (logHeight₁_eq_logHeight _).symm

variable (W)

/-- The height of `sym2x P Q` differs from `h(P) + h(Q)` by a bounded amount. -/
lemma abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.Point, |logHeight (P.sym2x Q) - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le F
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [P.naiveHeight_eq_logHeight, Q.naiveHeight_eq_logHeight, Point.sym2x_eq_xRep]
  have H₁ := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
  have H (v : Fin 2 → F) : ![v 0, v 1] = v := by ext i : 1; fin_cases i <;> simp
  have h₀ (P : W.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 := H P.xRep ▸ P.xRep_ne_zero
  specialize hC (h₀ P) (h₀ Q)
  rw [H P.xRep, H Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

variable [W.toAffine.IsElliptic]

/-- **The approximate parallelogram law** for the naïve height on an elliptic curve. -/
theorem approx_parallelogram_law [DecidableEq F] :
    ∃ C, ∀ (P Q : W.Point),
      |(P + Q).naiveHeight + (P - Q).naiveHeight - 2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, hC₂⟩ := abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ := Point.exists_smul_sym2x_add_sub_eq_addSubMap_sym2x P Q
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ P Q
  have haddsub := hC₁ (P + Q) (P - Q)
  have hC := ht ▸ hC₂ (P.sym2x Q)
  -- Reduce to the essentials before `grind`.
  generalize (P + Q).naiveHeight + (P - Q).naiveHeight = A at haddsub ⊢
  generalize logHeight ((P + Q).sym2x (P - Q)) = B at hC haddsub
  generalize logHeight (P.sym2x Q) = B' at hPQ hC
  generalize P.naiveHeight + Q.naiveHeight = A' at hPQ ⊢
  grind only [= abs.eq_1, = max_def]

end AAV

/-! ### Northcott finiteness -/

section Northcott

variable [AdmissibleAbsValues F]

instance [Northcott (logHeight₁ (K := F))] : Northcott (Point.naiveHeight (F := F) (W := W)) := by
  eta_expand
  simp only [Point.naiveHeight_eq_logHeight₁]
  rw [← Function.comp_def]
  have : Filter.TendstoCofinite fun P : W.Point ↦ P.xRep 0 :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).mpr finite_preimage_xRep0
  exact Northcott.comp_of_finite_fibers ..

variable [Northcott (logHeight₁ (K := F))]

variable (W) in
/-- The set of `K`-points on `W` with naïve height bounded by `B` is finite. This is the
Northcott ingredient of the Mordell–Weil theorem. -/
lemma finite_naiveHeight_le (B : ℝ) : {P : W.Point | P.naiveHeight ≤ B}.Finite :=
  Northcott.finite_le B

end Northcott

end Affine

end WeierstrassCurve

end
