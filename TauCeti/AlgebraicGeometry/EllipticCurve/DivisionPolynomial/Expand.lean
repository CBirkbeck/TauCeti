/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Expand

/-!
# Division polynomials in characteristic `p` are `p`-th power substitutions

In characteristic `p` the low division polynomials of a Weierstrass curve lie in the image of
`Polynomial.expand R p`, that is, they are polynomials in `Xᵖ`. This is the base case of the
factorisation of the `p`-power isogeny through Frobenius (Silverman III.6.2): the terms that
obstruct it all carry a factor of `p`.

Concretely, in characteristic `2` the `2 * b₆ * X` term of `Φ₂` and the `4X³`, `2b₄X` terms of
`ΨSq₂` vanish; in characteristic `3` the `3X⁴`, `3b₄X²`, `3b₆X` terms of `Ψ₃` vanish. Everything
is stated over an arbitrary commutative ring carrying `CharP`, so it specialises unchanged to a
field or to a universal polynomial ring.

## Main results

* `TauCeti.WeierstrassCurve.Φ_two_mem_range_expand`, `ΨSq_two_mem_range_expand`: characteristic
  two.
* `TauCeti.WeierstrassCurve.b₈_eq_of_charP_three`: `b₈ = b₂b₆ − b₄²` in characteristic three,
  the `4 = 1` specialisation of Mathlib's `b_relation`.
* `TauCeti.WeierstrassCurve.Ψ₃_mem_range_expand`, `ΨSq_three_mem_range_expand`: characteristic
  three.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Verschiebung/DivPolyExpand.lean`, declarations `Φ_two_mem_expand_two_charP`,
`ΨSq_two_mem_expand_two_charP`, `b_relation_of_charP_three`, `Ψ₃_mem_expand_three_charP` and
`ΨSq_three_mem_expand_three_charP`.

That file's sixth declaration, `Φ_three_mem_expand_three_charP`, is **not** ported: it carries
`set_option maxHeartbeats 1000000`, which this repository forbids, and making it elaborate within
budget is a separate piece of work rather than a transcription.
-/

public section

open Polynomial

namespace TauCeti

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve R)

/-- In characteristic two, `Φ₂` is a polynomial in `X²`.

`Φ₂ = X⁴ − b₄X² − 2b₆X − b₈`, and the `2b₆X` term vanishes. -/
theorem Φ_two_mem_range_expand [CharP R 2] : W.Φ 2 ∈ Set.range (⇑(expand R 2)) := by
  refine ⟨X ^ 2 - C W.b₄ * X - C W.b₈, ?_⟩
  rw [W.Φ_two, map_sub, map_sub, map_mul, expand_C, expand_X, map_pow, expand_X, expand_C]
  have h2 : (2 : R) * W.b₆ = 0 := by rw [show (2 : R) = 0 from CharP.cast_eq_zero R 2, zero_mul]
  rw [h2, map_zero, zero_mul, sub_zero]
  ring

/-- In characteristic two, `ΨSq₂` is a polynomial in `X²`.

`ΨSq₂ = Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`, and the `4X³` and `2b₄X` terms vanish. -/
theorem ΨSq_two_mem_range_expand [CharP R 2] : W.ΨSq 2 ∈ Set.range (⇑(expand R 2)) := by
  refine ⟨C W.b₂ * X + C W.b₆, ?_⟩
  rw [W.ΨSq_two, _root_.WeierstrassCurve.Ψ₂Sq, map_add, map_mul, expand_C, expand_X, expand_C]
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h4 : (4 : R) = 0 := by rw [show (4 : R) = 2 * 2 from by ring, h2, mul_zero]
  rw [h4, show (2 : R) * W.b₄ = 0 by rw [h2, zero_mul], map_zero, zero_mul, zero_mul]
  ring

/-- In characteristic three, `b₈ = b₂b₆ − b₄²`.

Mathlib's `b_relation` reads `4b₈ = b₂b₆ − b₄²`, and `4 = 1` here. -/
theorem b₈_eq_of_charP_three [CharP R 3] : W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  have h4 : (4 : R) = 1 := by
    rw [show (4 : R) = 3 + 1 from by ring, show (3 : R) = 0 from CharP.cast_eq_zero R 3, zero_add]
  simpa [h4] using W.b_relation

/-- In characteristic three, `Ψ₃` is a polynomial in `X³`.

`Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`, and every term with a factor of `3` vanishes. -/
theorem Ψ₃_mem_range_expand [CharP R 3] : W.Ψ₃ ∈ Set.range (⇑(expand R 3)) := by
  refine ⟨C W.b₂ * X + C W.b₈, ?_⟩
  rw [_root_.WeierstrassCurve.Ψ₃, map_add, map_mul, expand_C, expand_X, expand_C]
  have h3 : (3 : R[X]) = 0 := by exact_mod_cast CharP.cast_eq_zero R[X] 3
  linear_combination -(X ^ 4 + C W.b₄ * X ^ 2 + C W.b₆ * X) * h3

/-- In characteristic three, `ΨSq₃` is a polynomial in `X³`, since it is `Ψ₃²` and `expand` is
multiplicative. -/
theorem ΨSq_three_mem_range_expand [CharP R 3] : W.ΨSq 3 ∈ Set.range (⇑(expand R 3)) := by
  obtain ⟨g, hg⟩ := Ψ₃_mem_range_expand W
  exact ⟨g ^ 2, by rw [W.ΨSq_three, ← hg, map_pow]⟩

end WeierstrassCurve

end TauCeti
