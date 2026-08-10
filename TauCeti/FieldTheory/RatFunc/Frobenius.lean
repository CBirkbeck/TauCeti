/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# The `q`-th powers in a rational function field

For a finite field `K` with `q` elements, the `q`-power map is a `K`-algebra endomorphism of the
rational function field `K(X)` (Mathlib's `FiniteField.frobeniusAlgHom`). Its image is the
subfield `K(X^q)`, and `K(X)` has degree exactly `q` over it.

## Main results

* `TauCeti.FiniteField.fieldRange_frobeniusAlgHom_ratFunc`: the image of the `q`-power map on
  `K(X)` is `K⟮X ^ q⟯`.
* `TauCeti.FiniteField.finrank_fieldRange_frobeniusAlgHom_ratFunc`: `[K(X) : K(X^q)] = q`.

Both are `@[simp]`.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, the Frobenius isogeny — "the key input to
Layer 3". The layer seeds

```lean
noncomputable def Isogeny.degree (φ : Isogeny W₁ W₂) : ℕ :=
  Module.finrank φ.fieldPullback.fieldRange W₁.FunctionField
theorem degree_frobeniusIsogeny [Finite F] (W : WeierstrassCurve.Affine F) :
    (frobeniusIsogeny W).degree = Nat.card F
```

so the target is `Module.finrank` of `K(W)` over the field range of the `q`-power map. This file
proves that statement for the rational function field. It is what the seeded degree is computed
from: `K(x^q)` sits below both `K(x)` and `K(W)^q` inside `K(W)`, the two intermediate degrees
`[K(W) : K(x)]` and `[K(W)^q : K(x^q)]` are both `2`, and the tower law along the two routes reads
`[K(W) : K(W)^q] · 2 = 2 · [K(x) : K(x^q)]`. The right-hand factor is the `q` proved here.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/FrobeniusIsogeny.lean`, declarations
`frobenius_fieldRange_ratFunc` and `finrank_ratFunc_frobenius`.

Changes from the source. Both are `private` there, inside the file that builds the Frobenius
isogeny, and are stated with an elliptic curve and a `DecidableEq K` in scope; neither is used
here, and neither statement mentions a curve. The source proves `algebraMap K[X] K(X) = aeval X`
by induction on the polynomial; Mathlib has since acquired it as
`RatFunc.aeval_X_left_eq_algebraMap`, which is used instead.
-/

public section

open Polynomial

namespace TauCeti

namespace FiniteField

variable (K : Type*) [Field K] [Fintype K]

/-- A polynomial in `X ^ q`, read in `K(X)`, lies in `K⟮X ^ q⟯`. -/
private lemma algebraMap_expand_mem_adjoin (f : K[X]) :
    algebraMap K[X] (RatFunc K) (expand K (Fintype.card K) f) ∈
      IntermediateField.adjoin K {(RatFunc.X : RatFunc K) ^ Fintype.card K} := by
  rw [← RatFunc.aeval_X_left_eq_algebraMap, expand_aeval]
  exact IntermediateField.algebra_adjoin_le_adjoin K _
    (Polynomial.aeval_mem_adjoin_singleton K _)

/-- **The `q`-th powers in `K(X)` are the rational functions in `X ^ q`.** -/
@[simp]
theorem fieldRange_frobeniusAlgHom_ratFunc :
    (_root_.FiniteField.frobeniusAlgHom K (RatFunc K)).fieldRange =
      IntermediateField.adjoin K {(RatFunc.X : RatFunc K) ^ Fintype.card K} := by
  refine le_antisymm (fun x hx => ?_) (IntermediateField.adjoin_le_iff.mpr ?_)
  · obtain ⟨g, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    obtain ⟨p, r, -, rfl⟩ : ∃ p r : K[X], algebraMap K[X] (RatFunc K) r ≠ 0 ∧
        g = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) r :=
      ⟨g.num, g.denom, RatFunc.algebraMap_ne_zero g.denom_ne_zero, g.num_div_denom.symm⟩
    -- `(p/r) ^ q = p(X^q) / r(X^q)`, by `expand_card` on numerator and denominator
    simp only [_root_.FiniteField.coe_frobeniusAlgHom, div_pow, ← map_pow,
      ← _root_.FiniteField.expand_card (K := K)]
    exact div_mem (algebraMap_expand_mem_adjoin K p) (algebraMap_expand_mem_adjoin K r)
  · intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨RatFunc.X, rfl⟩

/-- **The rational function field has degree `q` over its subfield of `q`-th powers.** -/
@[simp]
theorem finrank_fieldRange_frobeniusAlgHom_ratFunc :
    Module.finrank (_root_.FiniteField.frobeniusAlgHom K (RatFunc K)).fieldRange (RatFunc K) =
      Fintype.card K := by
  -- `X ^ q` as the image of a polynomial, so that `finrank_eq_max_natDegree` reads its
  -- numerator and denominator off `X ^ q` and `1`
  rw [fieldRange_frobeniusAlgHom_ratFunc K, ← RatFunc.algebraMap_X, ← map_pow,
    RatFunc.finrank_eq_max_natDegree, RatFunc.num_algebraMap, RatFunc.denom_algebraMap,
    natDegree_X_pow, natDegree_one, Nat.max_zero]

end FiniteField

end TauCeti

end
