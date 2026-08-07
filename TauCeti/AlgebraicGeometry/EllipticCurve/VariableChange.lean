/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Complements on admissible changes of variables

Material complementing `Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean`: decidable
equality of changes of variables, and the negation automorphism `[-1]` of a Weierstrass curve as
an admissible change of variables, with its involution API. This is the nontrivial automorphism
in the `Aut (E, O)` milestone of `TauCetiRoadmap/EllipticCurves/README.md` §Layer 1, proved in
`TauCeti/AlgebraicGeometry/EllipticCurve/Aut.lean` to exhaust `Aut(E)` with the identity when
`j(E) ∉ {0, 1728}`.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean` at `d18b563029f3`, Apache 2.0,
by Kevin Buzzard and Claude).
-/

@[expose] public section

namespace WeierstrassCurve

/-- Two admissible changes of variables agree iff their four coefficients do; this makes equality
of changes of variables decidable over a commutative ring with decidable equality. -/
instance {R : Type*} [CommRing R] [DecidableEq R] : DecidableEq (VariableChange R) :=
  fun _ _ ↦ decidable_of_iff _ VariableChange.ext_iff.symm

variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- The automorphism `[-1] : (x, y) ↦ (x, -y - a₁x - a₃)` of a Weierstrass curve, as an admissible
change of variables `⟨-1, 0, -a₁, -a₃⟩`. It fixes `E` (`negVariableChange_smul_self`) and is an
involution (`negVariableChange_mul_self`). -/
def negVariableChange : VariableChange K :=
  ⟨-1, 0, -E.a₁, -E.a₃⟩

@[simp] lemma negVariableChange_u : E.negVariableChange.u = -1 := rfl

/-- The negation automorphism fixes the curve. -/
lemma negVariableChange_smul_self : E.negVariableChange • E = E := by
  simp only [negVariableChange, variableChange_def, inv_neg, inv_one, Units.val_neg,
    Units.val_one, mul_neg, neg_mul, one_mul, neg_add_rev, neg_neg, even_two, Even.neg_pow,
    one_pow, sub_neg_eq_add, mul_zero, add_zero, zero_mul, neg_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sub_zero]
  ring_nf

/-- The negation automorphism is an involution. -/
lemma negVariableChange_mul_self : E.negVariableChange * E.negVariableChange = 1 := by
  simp [VariableChange.mul_def, VariableChange.one_def, negVariableChange,
    Odd.neg_one_pow (by decide : Odd 3)]

/-- The negation automorphism is nontrivial for an elliptic curve: in characteristic `≠ 2` it
has `u = -1 ≠ 1`, and in characteristic `2` it has `(s, t) = (-a₁, -a₃) ≠ (0, 0)`, since an
elliptic curve in characteristic `2` cannot have `a₁ = a₃ = 0`. -/
lemma negVariableChange_ne_one [E.IsElliptic] : E.negVariableChange ≠ 1 := by
  intro h
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · have hs := congrArg VariableChange.s h
    have ht := congrArg VariableChange.t h
    simp only [negVariableChange, VariableChange.one_def, neg_eq_zero] at hs ht
    grind [a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero]
  · contrapose h2
    have hv : (-1 : K) = 1 := by
      simpa [VariableChange.one_def] using congrArg (fun C : VariableChange K ↦ (C.u : K)) h
    linear_combination -hv

end WeierstrassCurve

end
