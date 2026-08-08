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
* `TauCeti.WeierstrassCurve.Ψ₃_mem_range_expand`, `ΨSq_three_mem_range_expand`: characteristic
  three.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Verschiebung/DivPolyExpand.lean`, declarations `Φ_two_mem_expand_two_charP`,
`ΨSq_two_mem_expand_two_charP`, `Ψ₃_mem_expand_three_charP` and
`ΨSq_three_mem_expand_three_charP`.

The source's `b_relation_of_charP_three` is not ported: Mathlib already has it verbatim as
`WeierstrassCurve.b_relation_of_char_three` (`Weierstrass.lean:213`).

That file's sixth declaration, `Φ_three_mem_expand_three_charP`, is **not** ported: it carries
`set_option maxHeartbeats 1000000`, which this repository forbids, and making it elaborate within
budget is a separate piece of work rather than a transcription.
-/

public section

open Polynomial

namespace TauCeti

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve R)

/-- The characteristic relation, read in the polynomial ring: `(p : R[X]) = 0` whenever
`CharP R p`. Every proof below is the division-polynomial formula modulo this one fact, so it is
stated once rather than reshaped inline at each use. -/
private theorem natCast_eq_zero_poly (p : ℕ) [CharP R p] : (p : R[X]) = 0 := by
  exact_mod_cast CharP.cast_eq_zero R[X] p

/-- In characteristic two, `Φ₂` is a polynomial in `X²`.

`Φ₂ = X⁴ − b₄X² − 2b₆X − b₈`, and the `2b₆X` term vanishes. -/
theorem Φ_two_mem_range_expand [CharP R 2] : W.Φ 2 ∈ Set.range (⇑(expand R 2)) := by
  refine ⟨X ^ 2 - C W.b₄ * X - C W.b₈, ?_⟩
  simp only [W.Φ_two, map_sub, map_mul, map_pow, expand_C, expand_X, C_ofNat]
  linear_combination (X * C W.b₆) * natCast_eq_zero_poly (R := R) 2

/-- In characteristic two, `ΨSq₂` is a polynomial in `X²`.

`ΨSq₂ = Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`, and the `4X³` and `2b₄X` terms vanish. -/
theorem ΨSq_two_mem_range_expand [CharP R 2] : W.ΨSq 2 ∈ Set.range (⇑(expand R 2)) := by
  refine ⟨C W.b₂ * X + C W.b₆, ?_⟩
  simp only [W.ΨSq_two, _root_.WeierstrassCurve.Ψ₂Sq, map_add, map_mul, expand_C, expand_X,
    C_ofNat]
  linear_combination (-2 * X ^ 3 - X * C W.b₄) * natCast_eq_zero_poly (R := R) 2

/-- In characteristic three, `Ψ₃` is a polynomial in `X³`.

`Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`, and every term with a factor of `3` vanishes. -/
theorem Ψ₃_mem_range_expand [CharP R 3] : W.Ψ₃ ∈ Set.range (⇑(expand R 3)) := by
  refine ⟨C W.b₂ * X + C W.b₈, ?_⟩
  simp only [_root_.WeierstrassCurve.Ψ₃, map_add, map_mul, expand_C, expand_X]
  linear_combination -(X ^ 4 + C W.b₄ * X ^ 2 + C W.b₆ * X) * natCast_eq_zero_poly (R := R) 3

/-- In characteristic three, `ΨSq₃` is a polynomial in `X³`, since it is `Ψ₃²` and `expand` is
multiplicative. -/
theorem ΨSq_three_mem_range_expand [CharP R 3] : W.ΨSq 3 ∈ Set.range (⇑(expand R 3)) := by
  obtain ⟨g, hg⟩ := Ψ₃_mem_range_expand W
  exact ⟨g ^ 2, by rw [W.ΨSq_three, ← hg, map_pow]⟩

end WeierstrassCurve

end TauCeti
