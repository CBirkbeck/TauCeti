/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionFieldFinrank
public import TauCeti.FieldTheory.RatFunc.Frobenius
public import Mathlib.FieldTheory.Relrank

/-!
# The function field of a curve over the `q`-th powers of the rational function field

Let `K` be a finite field with `q` elements and `W` a Weierstrass curve over `K`. Inside the
function field `K(W)` sit the image of the rational function field `K(x)` and, inside that, the
image of its subfield of `q`-th powers `K(x^q)`. This file computes the degree of `K(W)` over the
smaller one: it is `2q`.

## Main results

* `TauCeti.WeierstrassCurve.Affine.relfinrank_frobeniusRatFuncRange`: `[K(x) : K(x^q)] = q`, read
  inside `K(W)`.
* `TauCeti.WeierstrassCurve.Affine.finrank_frobeniusRatFuncRange`: `[K(W) : K(x^q)] = 2 * q`.

Neither degree needs `W` to be elliptic: they are the degree of `K(W)` over embedded subfields of
the rational function field, and the Weierstrass equation alone gives the power basis.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, the Frobenius isogeny — "the key input to
Layer 3", seeded as `frobeniusIsogeny` with `degree_frobeniusIsogeny : … = Nat.card F`, where
`Isogeny.degree φ := Module.finrank φ.fieldPullback.fieldRange W₁.FunctionField`. This is the outer
half of the tower that computes that degree: `K(x^q)` sits below both `K(x)` and `K(W)^q` inside
`K(W)`, so the tower law along the two routes reads `[K(W) : K(W)^q] · 2 = 2q`.

Nothing here defines an isogeny or competes with the seeded `frobeniusIsogeny`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/FrobeniusIsogeny.lean`, declarations
`frobFracRange` — the model for `frobeniusRatFuncRange` — and `finrank_frobFracRange_functionField`,
the degree above it.

Changes from the source. It is `private` there, inside the file that builds the Frobenius isogeny,
and works over `FractionRing K[X]`; about half its length is then spent transporting the degree of
the rational function field over its `q`-th powers across `FractionRing K[X] ≃+* RatFunc K`. That
passage is not needed here: `TauCeti.FiniteField.finrank_fieldRange_frobeniusAlgHom_ratFunc` is
stated for `RatFunc K`, and `_root_.WeierstrassCurve.Affine.finrank_functionField` for an
arbitrary fraction field of `K[X]`, so both factors are already available over `RatFunc K`. The
source also builds the tower by hand, out of `(IntermediateField.inclusion h).toRingHom.toAlgebra`
and an `IsScalarTower.of_algebraMap_eq`, and needs `backward.isDefEq.respectTransparency false` for
the resulting `rfl`. Here both steps are Mathlib's relative degree `IntermediateField.relfinrank`:
`relfinrank_map_map` carries the inner degree along the embedding of `K(x)` into `K(W)`, and
`relfinrank_mul_finrank_top` is the tower law. Neither needs a hand-built scalar tower, so no
`set_option` is required.
-/

public section

open Polynomial WeierstrassCurve IntermediateField

open scoped RatFunc

namespace TauCeti

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : _root_.WeierstrassCurve.Affine K)

variable [Finite K]

/-- The image of `K(x^q)`, the `q`-th powers of the rational function field, inside `K(W)`. -/
noncomputable def frobeniusRatFuncRange : IntermediateField K W.FunctionField :=
  letI := Fintype.ofFinite K
  (_root_.FiniteField.frobeniusAlgHom K (RatFunc K)).fieldRange.map
    (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField)

/-- An element of `K(W)` lies in the copy of `K(x^q)` exactly when it is the image there of a
`q`-th power from the rational function field. -/
@[simp]
theorem mem_frobeniusRatFuncRange {z : W.FunctionField} :
    z ∈ frobeniusRatFuncRange W ↔ ∃ r : RatFunc K,
      IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField (r ^ Nat.card K) = z := by
  let _ := Fintype.ofFinite K
  rw [frobeniusRatFuncRange, AlgHom.map_fieldRange]
  simp [AlgHom.mem_fieldRange, Nat.card_eq_fintype_card]

/-- `K(x^q)` sits inside `K(x)`, both read inside `K(W)`. -/
theorem frobeniusRatFuncRange_le_ratFuncRange :
    frobeniusRatFuncRange W ≤ _root_.WeierstrassCurve.Affine.ratFuncRange W := by
  intro z hz
  rw [mem_frobeniusRatFuncRange] at hz
  obtain ⟨r, rfl⟩ := hz
  rw [_root_.WeierstrassCurve.Affine.mem_ratFuncRange]
  exact ⟨r ^ Nat.card K, rfl⟩

/-- **`[K(x) : K(x^q)] = q`**, read inside `K(W)`: the copy of the rational function field is of
degree `q` over the copy of its subfield of `q`-th powers. Embedding `K(x)` into `K(W)` does not
change this relative degree. -/
@[simp]
theorem relfinrank_frobeniusRatFuncRange :
    relfinrank (frobeniusRatFuncRange W) (_root_.WeierstrassCurve.Affine.ratFuncRange W) =
      Nat.card K := by
  let _ := Fintype.ofFinite K
  -- the copy of `K(x)` inside `K(W)` is the image of the whole rational function field
  have htop : (⊤ : IntermediateField K (RatFunc K)).map
      (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField) =
      _root_.WeierstrassCurve.Affine.ratFuncRange W := by
    ext z
    simp [IntermediateField.mem_map]
  rw [frobeniusRatFuncRange, ← htop, relfinrank_map_map, relfinrank_top_right,
    TauCeti.FiniteField.finrank_fieldRange_frobeniusAlgHom_ratFunc, Nat.card_eq_fintype_card]

/-- **`[K(W) : K(x^q)] = 2q`.** The tower `K(x^q) ⊆ K(x) ⊆ K(W)` has degrees `q` and `2`. -/
@[simp]
theorem finrank_frobeniusRatFuncRange :
    Module.finrank (frobeniusRatFuncRange W) W.FunctionField = 2 * Nat.card K := by
  have htower := relfinrank_mul_finrank_top (frobeniusRatFuncRange_le_ratFuncRange W)
  rw [relfinrank_frobeniusRatFuncRange W,
    _root_.WeierstrassCurve.Affine.finrank_ratFuncRange W] at htower
  rw [← htower, Nat.mul_comm]

end WeierstrassCurve.Affine

end TauCeti

end
