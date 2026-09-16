/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard

/-!
# How many points `[n]` sends to a given one

The points that `[n]` carries to a fixed `T` form a coset of `ker [n]` as soon as there is one of
them, so there are exactly `#ker [n]` of them — and over an algebraically closed field with `n`
invertible that is `n ²`.

The count is what turns a sum over the places above a point into a sum of `n ²` terms, which is how
the pullback of a divisor along `[n]` is read.

## Main results

* `TauCeti.Isogeny.card_zsmul_preimage_eq_card_ker`: a nonempty `[n]`-fibre has as many points as
  the kernel.
* `TauCeti.Isogeny.card_zsmul_preimage`: over an algebraically closed field, for `n` invertible
  there, that count is `n ²`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)
  [W.IsElliptic]

/-- **A nonempty `[n]`-fibre is a coset of `ker [n]`**: subtracting one preimage from another
lands in the kernel, and adding it back returns to the fibre. -/
theorem card_zsmul_preimage_eq_card_ker {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    {T P₀ : (W⁄F).toAffine.Point} (hP₀ : n • P₀ = T) :
    Nat.card {P : (W⁄F).toAffine.Point // n • P = T} =
      Nat.card (mulByIntIsogeny W hn).ker :=
  Nat.card_congr
    { toFun := fun P ↦ ⟨P.1 - P₀, (mem_ker_mulByIntIsogeny_iff W hn).2 <| by
        rw [smul_sub, P.2, hP₀, sub_self]⟩
      invFun := fun Q ↦ ⟨Q.1 + P₀, by
        rw [smul_add, (mem_ker_mulByIntIsogeny_iff W hn).1 Q.2, hP₀, zero_add]⟩
      left_inv := fun P ↦ Subtype.ext (sub_add_cancel P.1 P₀)
      right_inv := fun Q ↦ Subtype.ext (add_sub_cancel_right Q.1 P₀) }

/-- **`[n]` is `n ²`-to-one where it hits at all**, over an algebraically closed field in which
`n` is invertible. -/
theorem card_zsmul_preimage [IsAlgClosed F] {n : ℤ} {hn : psiFunctionField W n ≠ 0}
    (hchar : (n : F) ≠ 0) {T P₀ : (W⁄F).toAffine.Point} (hP₀ : n • P₀ = T) :
    Nat.card {P : (W⁄F).toAffine.Point // n • P = T} = n.natAbs ^ 2 := by
  rw [card_zsmul_preimage_eq_card_ker W hn hP₀, card_ker_mulByIntIsogeny W hchar]

end TauCeti.Isogeny

end
