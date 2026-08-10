/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FrobeniusTower

/-!
# The function field of a curve over its subfield of `q`-th powers

Let `K` be a finite field with `q` elements and `W` a Weierstrass curve over `K`. The `q`-th powers
of the function field `K(W)` form a subfield `K(W)^q`, and this file computes the degree of `K(W)`
over it: it is `q`.

The argument is a tower with two routes. Inside `K(W)` the subfield `K(x^q)` of `q`-th powers of the
rational function field lies below both `K(x)` and `K(W)^q`, and `[K(W) : K(x^q)] = 2q` is
`finrank_frobeniusRatFuncRange`. Raising `K(x) ⊆ K(W)` to the `q`-th power gives
`K(x^q) ⊆ K(W)^q` with the same relative degree `2`, because the `q`-power map is an embedding, so
the second route reads `2 · [K(W) : K(W)^q] = 2q`.

## Main results

* `TauCeti.WeierstrassCurve.Affine.relfinrank_frobeniusFieldRange`: `[K(W)^q : K(x^q)] = 2`.
* `TauCeti.WeierstrassCurve.Affine.finrank_frobeniusFieldRange`: `[K(W) : K(W)^q] = q`.

As in `FrobeniusTower`, `W` need not be elliptic.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, the Frobenius isogeny — "the key input to
Layer 3", seeded as `frobeniusIsogeny` with `degree_frobeniusIsogeny : … = Nat.card F`, where
`Isogeny.degree φ := Module.finrank φ.fieldPullback.fieldRange W₁.FunctionField`. The subfield
`K(W)^q` here is the field range that seeded degree is taken over, so
`finrank_frobeniusFieldRange` is that degree's field-theoretic content, available before any
isogeny exists. Nothing here defines an isogeny or competes with the seeded `frobeniusIsogeny`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/FrobeniusIsogeny.lean`, the `private`
declarations `frobFracRange_le_frobRange` and `finrank_over_frobenius_image`.

Changes from the source. The source builds the intermediate tower by hand out of
`(IntermediateField.inclusion h).toRingHom.toAlgebra` and an `IsScalarTower.of_algebraMap_eq`, and
needs `set_option backward.isDefEq.respectTransparency false` for the `rfl` that results; and it
transports `[K(W)^q : K(x^q)] = 2` across an explicitly constructed isomorphism of the two towers.
Both steps are Mathlib's relative degree here: `relfinrank_map_map` says a degree is unchanged when
both fields are carried along the `q`-power embedding, and `relfinrank_mul_finrank_top` is the
tower law. No `set_option` is required.
-/

public section

open Polynomial WeierstrassCurve IntermediateField

open scoped RatFunc

namespace TauCeti

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : _root_.WeierstrassCurve.Affine K)

variable [Finite K]

/-- The subfield `K(W)^q` of `q`-th powers of the function field. -/
noncomputable def frobeniusFieldRange : IntermediateField K W.FunctionField :=
  letI := Fintype.ofFinite K
  (_root_.FiniteField.frobeniusAlgHom K W.FunctionField).fieldRange

/-- An element of `K(W)` is a `q`-th power exactly when it lies in `K(W)^q`. -/
@[simp]
theorem mem_frobeniusFieldRange {z : W.FunctionField} :
    z ∈ frobeniusFieldRange W ↔ ∃ w : W.FunctionField, w ^ Nat.card K = z := by
  let _ := Fintype.ofFinite K
  rw [frobeniusFieldRange]
  simp [AlgHom.mem_fieldRange, _root_.FiniteField.frobeniusAlgHom_apply,
    Nat.card_eq_fintype_card]

/-- `K(x^q)` sits inside `K(W)^q`: a `q`-th power of a rational function is a `q`-th power. -/
theorem frobeniusRatFuncRange_le_frobeniusFieldRange :
    frobeniusRatFuncRange W ≤ frobeniusFieldRange W := by
  intro z hz
  rw [mem_frobeniusRatFuncRange] at hz
  obtain ⟨r, rfl⟩ := hz
  exact (mem_frobeniusFieldRange W).2
    ⟨IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField r, by rw [← map_pow]⟩

/-- **`[K(W)^q : K(x^q)] = 2`.** Raising `K(x) ⊆ K(W)` to the `q`-th power is an embedding of the
pair, so the relative degree `2` of `finrank_ratFuncRange` is unchanged. -/
@[simp]
theorem relfinrank_frobeniusFieldRange :
    relfinrank (frobeniusRatFuncRange W) (frobeniusFieldRange W) = 2 := by
  let _ := Fintype.ofFinite K
  -- the two `q`-th power subfields are the images of `K(x)` and of `K(W)` itself
  have hlow : (_root_.WeierstrassCurve.Affine.ratFuncRange W).map
      (_root_.FiniteField.frobeniusAlgHom K W.FunctionField) = frobeniusRatFuncRange W := by
    ext z
    simp only [IntermediateField.mem_map, _root_.WeierstrassCurve.Affine.mem_ratFuncRange,
      mem_frobeniusRatFuncRange, _root_.FiniteField.frobeniusAlgHom_apply]
    constructor
    · rintro ⟨w, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, by rw [map_pow, Nat.card_eq_fintype_card]⟩
    · rintro ⟨r, rfl⟩
      exact ⟨_, ⟨r, rfl⟩, by rw [map_pow, Nat.card_eq_fintype_card]⟩
  have htop : (⊤ : IntermediateField K W.FunctionField).map
      (_root_.FiniteField.frobeniusAlgHom K W.FunctionField) = frobeniusFieldRange W := by
    ext z
    simp [IntermediateField.mem_map, frobeniusFieldRange]
  rw [← hlow, ← htop, relfinrank_map_map, relfinrank_top_right,
    _root_.WeierstrassCurve.Affine.finrank_ratFuncRange]

/-- **`[K(W) : K(W)^q] = q`.** The tower `K(x^q) ⊆ K(W)^q ⊆ K(W)` has degrees `2` and `[K(W) :
K(W)^q]`, with product `2q`. -/
@[simp]
theorem finrank_frobeniusFieldRange :
    Module.finrank (frobeniusFieldRange W) W.FunctionField = Nat.card K := by
  have htower := relfinrank_mul_finrank_top (frobeniusRatFuncRange_le_frobeniusFieldRange W)
  rw [relfinrank_frobeniusFieldRange W, finrank_frobeniusRatFuncRange W] at htower
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) htower

end WeierstrassCurve.Affine

end TauCeti

end
