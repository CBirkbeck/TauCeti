/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Complements on admissible changes of variables

Material complementing `Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean`.

The negation automorphism `[-1]` of a Weierstrass curve as an admissible change of variables,
with its involution API. This is the nontrivial automorphism in the `Aut (E, O)` milestone of
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 1, proved in
`TauCeti/AlgebraicGeometry/EllipticCurve/Aut.lean` to exhaust `Aut(E)` with the identity when
`j(E) ∉ {0, 1728}`.

Then the behaviour of the coordinate map `(x, y) ↦ (u²x + r, u³y + u²sx + t)` itself: the cocycle
laws `variableChange_X_mul`/`variableChange_Y_mul` for a composite change of variables, the
naturality `variableChange_X_map`/`variableChange_Y_map` along a ring homomorphism, and
`baseChange_variableChange`, the `baseChange` spelling of `map_variableChange`. None of these
mentions a curve or an affine formula, so they sit here rather than with the transformation laws
in `TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean` that consume them downstream.

Everything here is stated over a commutative ring: `⟨-1, 0, -a₁, -a₃⟩` is an admissible change
of variables for a Weierstrass curve over any commutative ring, and the two identities it
satisfies are polynomial. Only the nontriviality `negVariableChange_ne_one` needs the curve to
be elliptic over a nontrivial ring.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean` at the roadmap's pin
`bc2fe8ff7396` (FLT PR #1088), Apache 2.0, by Kevin Buzzard and Claude), generalised here from
FLT's field-level statements to a commutative ring.

The four coordinate-map laws follow
`ModularCurves/ForMathlib/AffinePointVariableChange.lean` (`vcX_comp`, `vcY_comp`, `vcX_map`,
`vcY_map`) in `CBirkbeck/AINTLIB` (Apache 2.0, by Chris Birkbeck), restated for the
`(x, y) ↦ (u²x + r, u³y + u²sx + t)` direction its consumers use.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (E : WeierstrassCurve R)

/-- The automorphism `[-1] : (x, y) ↦ (x, -y - a₁x - a₃)` of a Weierstrass curve, as an admissible
change of variables `⟨-1, 0, -a₁, -a₃⟩`. It fixes `E` (`negVariableChange_smul_self`) and is an
involution (`negVariableChange_mul_self`). -/
def negVariableChange : VariableChange R :=
  ⟨-1, 0, -E.a₁, -E.a₃⟩

@[simp] lemma negVariableChange_u : E.negVariableChange.u = -1 := by
  simp only [negVariableChange]

@[simp] lemma negVariableChange_r : E.negVariableChange.r = 0 := by
  simp only [negVariableChange]

@[simp] lemma negVariableChange_s : E.negVariableChange.s = -E.a₁ := by
  simp only [negVariableChange]

@[simp] lemma negVariableChange_t : E.negVariableChange.t = -E.a₃ := by
  simp only [negVariableChange]

/-- The negation automorphism fixes the curve. -/
@[simp] lemma negVariableChange_smul_self : E.negVariableChange • E = E := by
  ext <;>
    simp only [negVariableChange, variableChange_def, inv_neg, inv_one, Units.val_neg,
      Units.val_one] <;>
    ring

/-- The negation automorphism is an involution. -/
@[simp] lemma negVariableChange_mul_self : E.negVariableChange * E.negVariableChange = 1 := by
  simp [VariableChange.mul_def, VariableChange.one_def, negVariableChange,
    Odd.neg_one_pow (by decide : Odd 3)]

/-- The negation automorphism commutes with base change along a ring homomorphism. -/
@[simp] lemma negVariableChange_map {A : Type*} [CommRing A] (φ : R →+* A) :
    (E.map φ).negVariableChange = E.negVariableChange.map φ := by
  ext <;> simp [negVariableChange, VariableChange.map, map_a₁, map_a₃]

/-- The negation automorphism is its own inverse, being an involution. -/
@[simp] lemma negVariableChange_inv : E.negVariableChange⁻¹ = E.negVariableChange :=
  inv_eq_of_mul_eq_one_left E.negVariableChange_mul_self

/-- The negation automorphism is nontrivial for an elliptic curve: where `2 ≠ 0` it has
`u = -1 ≠ 1`, and where `2 = 0` it has `(s, t) = (-a₁, -a₃) ≠ (0, 0)`, since an elliptic curve
over a ring in which `2 = 0` cannot have `a₁ = a₃ = 0`. -/
lemma negVariableChange_ne_one [Nontrivial R] [E.IsElliptic] : E.negVariableChange ≠ 1 := by
  intro h
  rcases eq_or_ne (2 : R) 0 with h2 | h2
  · have hs := congrArg VariableChange.s h
    have ht := congrArg VariableChange.t h
    simp only [negVariableChange, VariableChange.one_def, neg_eq_zero] at hs ht
    grind [a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero]
  · contrapose h2
    have hv : (-1 : R) = 1 := by
      simpa [VariableChange.one_def] using congrArg (fun C : VariableChange R ↦ (C.u : R)) h
    linear_combination -hv

section CoordinateMaps

/-! ### The coordinate map of a change of variables

None of these is a `simp` lemma. `variableChange_X_inj` has a left-hand side that `simp` rewrites
first, by `add_left_inj`, so it is never in simp-normal form and the `simpNF` linter rejects the
attribute; `variableChange_Y_inj` is conditional rather than an unconditional normalisation law;
and the cocycle and naturality laws are equalities between two spellings of a coordinate, with no
preferred direction. -/

variable (C : VariableChange R)

/-- **Cocycle law for the `x`-coordinate.** Composing changes of variables composes their
coordinate maps: `Φ_{C * C'} = Φ_{C'} ∘ Φ_C`. -/
lemma variableChange_X_mul (C' : VariableChange R) (x : R) :
    ((C * C').u : R) ^ 2 * x + (C * C').r
      = (C'.u : R) ^ 2 * ((C.u : R) ^ 2 * x + C.r) + C'.r := by
  simp only [VariableChange.mul_def, Units.val_mul]
  ring

/-- **Cocycle law for the `y`-coordinate.** -/
lemma variableChange_Y_mul (C' : VariableChange R) (x y : R) :
    ((C * C').u : R) ^ 3 * y + ((C * C').u : R) ^ 2 * (C * C').s * x + (C * C').t
      = (C'.u : R) ^ 3 * ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
        + (C'.u : R) ^ 2 * C'.s * ((C.u : R) ^ 2 * x + C.r) + C'.t := by
  simp only [VariableChange.mul_def, Units.val_mul]
  ring

/-- **Naturality in the base ring** for the `x`-coordinate: the coordinate map commutes with a
ring homomorphism, so it is compatible with base change. -/
lemma variableChange_X_map {A : Type*} [CommRing A] (φ : R →+* A) (x : R) :
    ((C.map φ).u : A) ^ 2 * φ x + (C.map φ).r = φ ((C.u : R) ^ 2 * x + C.r) := by
  simp [VariableChange.map_u, VariableChange.map_r]

/-- **Naturality in the base ring** for the `y`-coordinate. -/
lemma variableChange_Y_map {A : Type*} [CommRing A] (φ : R →+* A) (x y : R) :
    ((C.map φ).u : A) ^ 3 * φ y + ((C.map φ).u : A) ^ 2 * (C.map φ).s * φ x + (C.map φ).t
      = φ ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t) := by
  simp [VariableChange.map_u, VariableChange.map_s, VariableChange.map_t]

/-- The change of variables is injective on `x`-coordinates: `u²x + r` determines `x`. -/
lemma variableChange_X_inj {x₁ x₂ : R} :
    (C.u : R) ^ 2 * x₁ + C.r = (C.u : R) ^ 2 * x₂ + C.r ↔ x₁ = x₂ :=
  ⟨fun h ↦ (C.u.isUnit.pow 2).mul_right_inj.mp (add_right_cancel h), fun h ↦ by rw [h]⟩

/-- The change of variables is injective on `y`-coordinates once the `x`-coordinates agree. -/
lemma variableChange_Y_inj {x₁ x₂ y₁ y₂ : R} (hx : x₁ = x₂) :
    (C.u : R) ^ 3 * y₁ + (C.u : R) ^ 2 * C.s * x₁ + C.t
      = (C.u : R) ^ 3 * y₂ + (C.u : R) ^ 2 * C.s * x₂ + C.t ↔ y₁ = y₂ := by
  subst hx
  exact ⟨fun h ↦ (C.u.isUnit.pow 3).mul_right_inj.mp (add_right_cancel (add_right_cancel h)),
    fun h ↦ by rw [h]⟩

/-- **Base change commutes with change of variables.** Base changing `D • W` to `A` is changing
the base-changed curve `W⁄A` by the base-changed variable change `D⁄A`.

This is `map_variableChange` at `algebraMap`, restated in the `baseChange` spelling. The
restatement is load-bearing rather than cosmetic: `WeierstrassCurve.baseChange` is a plain `def`,
not `abbrev` or `@[reducible]`, so `W⁄A` and `W.map (algebraMap R A)` are definitionally equal but
**not** interchangeable for `rw` and `simp only`, which match up to reducible transparency. Its
consumers — and `Point.map`, whose type is already phrased with `⁄` — are in the `baseChange`
vocabulary, so substituting `map_variableChange` at the call sites does not elaborate. -/
lemma baseChange_variableChange (W : WeierstrassCurve R) (D : VariableChange R) (A : Type*)
    [CommRing A] [Algebra R A] :
    (D.baseChange A) • (W.baseChange A) = (D • W).baseChange A :=
  map_variableChange (W := W) (C := D) (φ := algebraMap R A)

end CoordinateMaps

end WeierstrassCurve

end
