/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionFieldFinrank
public import TauCeti.FieldTheory.RatFunc.Frobenius

/-!
# The function field of a curve over the `q`-th powers of the rational function field

Let `K` be a finite field with `q` elements and `W` a Weierstrass curve over `K`. Inside the
function field `K(W)` sit the image of the rational function field `K(x)` and, inside that, the
image of its subfield of `q`-th powers `K(x^q)`. This file computes the degree of `K(W)` over the
smaller one: it is `2q`.

## Main results

* `TauCeti.WeierstrassCurve.Affine.finrank_ratFuncRange`: `[K(W) : K(x)] = 2`, the image of the
  rational function field inside `K(W)`.
* `TauCeti.WeierstrassCurve.Affine.finrank_frobeniusRatFuncRange`: `[K(W) : K(x^q)] = 2 * q`.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, the Frobenius isogeny — "the key input to
Layer 3", seeded as `frobeniusIsogeny` with `degree_frobeniusIsogeny : … = Nat.card F`, where
`Isogeny.degree φ := Module.finrank φ.fieldPullback.fieldRange W₁.FunctionField`. This is the outer
half of the tower that computes that degree: `K(x^q)` sits below both `K(x)` and `K(W)^q` inside
`K(W)`, so the tower law along the two routes reads `[K(W) : K(W)^q] · 2 = 2q`.

Nothing here defines an isogeny or competes with the seeded `frobeniusIsogeny`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/FrobeniusIsogeny.lean`, declaration
`finrank_frobFracRange_functionField`.

Changes from the source. It is `private` there, inside the file that builds the Frobenius isogeny,
and works over `FractionRing K[X]`; about half its length is then spent transporting the degree of
the rational function field over its `q`-th powers across `FractionRing K[X] ≃+* RatFunc K`. That
passage is not needed here: `TauCeti.FiniteField.finrank_fieldRange_frobeniusAlgHom_ratFunc` is
stated for `RatFunc K`, and `_root_.WeierstrassCurve.Affine.finrank_functionField` for an
arbitrary fraction field of `K[X]`, so both factors are already available over `RatFunc K`. The
source also builds its tower by hand and needs
`set_option backward.isDefEq.respectTransparency false` for the resulting `rfl`; here the tower is
Mathlib's `IntermediateField.extendScalars`, which needs no such option.
-/

public section

open Polynomial WeierstrassCurve

open scoped RatFunc

namespace TauCeti

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : _root_.WeierstrassCurve.Affine K)

/-- The image of the rational function field `K(x)` inside the function field `K(W)`. -/
noncomputable def ratFuncRange : IntermediateField K W.FunctionField :=
  (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField).fieldRange

@[simp]
theorem mem_ratFuncRange {z : W.FunctionField} :
    z ∈ ratFuncRange W ↔
      ∃ r : RatFunc K, IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField r = z :=
  AlgHom.mem_fieldRange

/-- **`[K(W) : K(x)] = 2`**, for the copy of the rational function field inside `K(W)`. -/
@[simp]
theorem finrank_ratFuncRange : Module.finrank (ratFuncRange W) W.FunctionField = 2 := by
  have h := Algebra.finrank_eq_of_equiv_equiv
    (AlgEquiv.ofInjective (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField)
      (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField).toRingHom.injective).toRingEquiv
    (RingEquiv.refl W.FunctionField) (by ext x; rfl)
  rw [_root_.WeierstrassCurve.Affine.finrank_functionField W (RatFunc K)] at h
  exact h.symm

variable [Fintype K]

/-- The image of `K(x^q)`, the `q`-th powers of the rational function field, inside `K(W)`. -/
noncomputable def frobeniusRatFuncRange : IntermediateField K W.FunctionField :=
  (_root_.FiniteField.frobeniusAlgHom K (RatFunc K)).fieldRange.map
    (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField)

@[simp]
theorem mem_frobeniusRatFuncRange {z : W.FunctionField} :
    z ∈ frobeniusRatFuncRange W ↔ ∃ r : RatFunc K,
      IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField
        (_root_.FiniteField.frobeniusAlgHom K (RatFunc K) r) = z := by
  simp only [frobeniusRatFuncRange, IntermediateField.mem_map, AlgHom.mem_fieldRange]
  constructor
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩; exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩; exact ⟨_, ⟨r, rfl⟩, rfl⟩

/-- `K(x^q)` sits inside `K(x)`, both read inside `K(W)`. -/
theorem frobeniusRatFuncRange_le_ratFuncRange :
    frobeniusRatFuncRange W ≤ ratFuncRange W := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨_root_.FiniteField.frobeniusAlgHom K (RatFunc K)
    ((AlgHom.mem_fieldRange.mp hz).choose), by
      simpa using congrArg (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField)
        (AlgHom.mem_fieldRange.mp hz).choose_spec⟩

/-- **`[K(x) : K(x^q)] = q`**, transported into `K(W)`: the copy of the rational function field is
of degree `q` over the copy of its subfield of `q`-th powers. -/
@[simp]
theorem finrank_extendScalars_ratFuncRange :
    Module.finrank (frobeniusRatFuncRange W)
      (IntermediateField.extendScalars (frobeniusRatFuncRange_le_ratFuncRange W)) =
      Fintype.card K := by
  let i : (_root_.FiniteField.frobeniusAlgHom K (RatFunc K)).fieldRange ≃+*
      frobeniusRatFuncRange W :=
    (IntermediateField.equivMap (_root_.FiniteField.frobeniusAlgHom K (RatFunc K)).fieldRange
      (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField)).toRingEquiv
  let j : RatFunc K ≃+*
      IntermediateField.extendScalars (frobeniusRatFuncRange_le_ratFuncRange W) :=
    (AlgEquiv.ofInjective (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField)
      (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField).toRingHom.injective).toRingEquiv
  have h := Algebra.finrank_eq_of_equiv_equiv i j (by ext x; rfl)
  rw [TauCeti.FiniteField.finrank_fieldRange_frobeniusAlgHom_ratFunc] at h
  exact h.symm

/-- **`[K(W) : K(x^q)] = 2q`.** The tower `K(x^q) ⊆ K(x) ⊆ K(W)` has degrees `q` and `2`. -/
@[simp]
theorem finrank_frobeniusRatFuncRange :
    Module.finrank (frobeniusRatFuncRange W) W.FunctionField = 2 * Fintype.card K := by
  have htower := Module.finrank_mul_finrank (frobeniusRatFuncRange W)
    (IntermediateField.extendScalars (frobeniusRatFuncRange_le_ratFuncRange W)) W.FunctionField
  -- `extendScalars` only changes the base ring of the intermediate field, not its carrier, so the
  -- outer degree is `finrank_ratFuncRange` unchanged
  have houter : Module.finrank
      (IntermediateField.extendScalars (frobeniusRatFuncRange_le_ratFuncRange W))
      W.FunctionField = 2 := finrank_ratFuncRange W
  rw [finrank_extendScalars_ratFuncRange W, houter] at htower
  rw [← htower, Nat.mul_comm]

end WeierstrassCurve.Affine

end TauCeti

end
