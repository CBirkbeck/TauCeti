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
* `TauCeti.WeierstrassCurve.Ψ₃_mem_range_expand`, `ΨSq_three_mem_range_expand`,
  `Φ_three_mem_range_expand`: characteristic three.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Verschiebung/DivPolyExpand.lean`, declarations `Φ_two_mem_expand_two_charP`,
`ΨSq_two_mem_expand_two_charP`, `Ψ₃_mem_expand_three_charP`,
`ΨSq_three_mem_expand_three_charP` and `Φ_three_mem_expand_three_charP`.

The source's `b_relation_of_charP_three` is not ported: Mathlib already has it verbatim as
`WeierstrassCurve.b_relation_of_char_three` (`Weierstrass.lean:213`).

The source proves `Φ_three_mem_expand_three_charP` by exhibiting an explicit cubic witness,
which needs `set_option maxHeartbeats 1000000`; this repository forbids raising the limit, so
`Φ_three_mem_range_expand` is instead proved through `Polynomial.expand_contract` (whence its
extra `NoZeroDivisors` hypothesis) and elaborates within the default budget.
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
  simp only [W.Φ_two, map_sub, map_mul, map_pow, expand_C, expand_X, C_ofNat]
  linear_combination (X * C W.b₆) * CharP.cast_eq_zero R[X] 2

/-- In characteristic two, `ΨSq₂` is a polynomial in `X²`.

`ΨSq₂ = Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`, and the `4X³` and `2b₄X` terms vanish. -/
theorem ΨSq_two_mem_range_expand [CharP R 2] : W.ΨSq 2 ∈ Set.range (⇑(expand R 2)) := by
  refine ⟨C W.b₂ * X + C W.b₆, ?_⟩
  simp only [W.ΨSq_two, _root_.WeierstrassCurve.Ψ₂Sq, map_add, map_mul, expand_C, expand_X,
    C_ofNat]
  linear_combination (-2 * X ^ 3 - X * C W.b₄) * CharP.cast_eq_zero R[X] 2

/-- In characteristic three, `Ψ₃` is a polynomial in `X³`.

`Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`, and every term with a factor of `3` vanishes. -/
theorem Ψ₃_mem_range_expand [CharP R 3] : W.Ψ₃ ∈ Set.range (⇑(expand R 3)) := by
  refine ⟨C W.b₂ * X + C W.b₈, ?_⟩
  simp only [_root_.WeierstrassCurve.Ψ₃, map_add, map_mul, expand_C, expand_X]
  linear_combination -(X ^ 4 + C W.b₄ * X ^ 2 + C W.b₆ * X) * CharP.cast_eq_zero R[X] 3

/-- In characteristic three, `ΨSq₃` is a polynomial in `X³`, since it is `Ψ₃²` and `expand` is
multiplicative. -/
theorem ΨSq_three_mem_range_expand [CharP R 3] : W.ΨSq 3 ∈ Set.range (⇑(expand R 3)) := by
  obtain ⟨g, hg⟩ := Ψ₃_mem_range_expand W
  exact ⟨g ^ 2, by rw [W.ΨSq_three, ← hg, map_pow]⟩

/-- In characteristic three, `Φ₃` is a polynomial in `X³`.

Unlike the cases above, this is proved through the derivative criterion: in characteristic `p` a
polynomial with vanishing derivative lies in the image of `expand R p`
(`Polynomial.expand_contract`, whence the `NoZeroDivisors` hypothesis), and
`derivative (Φ 3) = 0` is a `linear_combination` over `3 = 0` and the characteristic-three
`b`-relation `b₈ = b₂b₆ − b₄²`. The explicit-witness route this replaces does not elaborate
within the repository heartbeat budget. -/
theorem Φ_three_mem_range_expand [CharP R 3] [NoZeroDivisors R] :
    W.Φ 3 ∈ Set.range (⇑(expand R 3)) := by
  have hderiv : Polynomial.derivative (W.Φ 3) = 0 := by
    have h3 : (3 : R[X]) = 0 := by exact_mod_cast CharP.cast_eq_zero R[X] 3
    have hbC : C W.b₈ = C W.b₂ * C W.b₆ - C W.b₄ ^ 2 := by
      rw [W.b_relation_of_char_three, map_sub, map_mul, map_pow]
    rw [_root_.WeierstrassCurve.Φ_three]
    simp only [_root_.WeierstrassCurve.Ψ₃, _root_.WeierstrassCurve.preΨ₄,
      _root_.WeierstrassCurve.Ψ₂Sq, derivative_mul, derivative_X, derivative_pow, derivative_add,
      derivative_C, derivative_ofNat, map_ofNat, map_sub, map_mul, map_pow, Nat.cast_ofNat]
    rw [hbC]
    -- The remaining identity is `3 * M = 0` for the explicit polynomial `M` below.
    linear_combination (3 * X ^ 8 - 14 * C W.b₄ * X ^ 6 -
      (2 * C W.b₂ * C W.b₄ + 48 * C W.b₆) * X ^ 5 -
      (65 * C W.b₂ * C W.b₆ - 55 * C W.b₄ ^ 2) * X ^ 4 -
      (16 * C W.b₂ ^ 2 * C W.b₆ - 16 * C W.b₂ * C W.b₄ ^ 2 + 4 * C W.b₄ * C W.b₆) * X ^ 3 -
      (C W.b₂ ^ 3 * C W.b₆ - C W.b₂ ^ 2 * C W.b₄ ^ 2 + 17 * C W.b₂ * C W.b₄ * C W.b₆ -
        18 * C W.b₄ ^ 3 - 3 * C W.b₆ ^ 2) * X ^ 2 -
      (2 * C W.b₂ ^ 2 * C W.b₄ * C W.b₆ - 2 * C W.b₂ * C W.b₄ ^ 3 + 2 * C W.b₂ * C W.b₆ ^ 2 -
        4 * C W.b₄ ^ 2 * C W.b₆) * X -
      (C W.b₂ * C W.b₄ ^ 2 * C W.b₆ - C W.b₄ ^ 4 - C W.b₄ * C W.b₆ ^ 2)) * h3
  exact ⟨contract 3 (W.Φ 3), expand_contract (p := 3) hderiv (by norm_num)⟩

end WeierstrassCurve

end TauCeti
