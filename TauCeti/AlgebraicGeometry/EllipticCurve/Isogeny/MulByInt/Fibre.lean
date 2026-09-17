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
invertible that is `n ²`. Nothing about curves enters the first step: it holds for `n • ·` on any
additive commutative group, and is stated that way.

The count is what turns a sum over the places above a point into a sum of `n ²` terms, which is how
the pullback of a divisor along `[n]` is read.

## Main results

* `TauCeti.Isogeny.card_zsmul_preimage_eq_card_zsmul_eq_zero`: in any additive commutative group,
  a nonempty fibre of `n • ·` has as many points as its kernel.
* `TauCeti.Isogeny.card_zsmul_preimage_eq_card_ker`: for `[n]` on a curve, that kernel is
  `ker [n]`.
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

section Group

variable {G : Type*} [AddCommGroup G]

/-- **A nonempty fibre of `n • ·` has as many points as its kernel.** -/
theorem card_zsmul_preimage_eq_card_zsmul_eq_zero {n : ℤ} {T P₀ : G} (hP₀ : n • P₀ = T) :
    Nat.card {P : G // n • P = T} = Nat.card {P : G // n • P = 0} :=
  -- `n • ·` is an `AddMonoidHom`, so this is Mathlib's fibre-kernel equivalence read through
  -- the two subtype descriptions.
  Nat.card_congr <|
    (Equiv.subtypeEquivRight fun P ↦ by simp [hP₀]).trans <|
      ((smulAddHom ℤ G n).fiberEquivKer P₀).trans <|
        Equiv.subtypeEquivRight fun P ↦ by simp

end Group

/-- **A nonempty `[n]`-fibre has as many points as `ker [n]`.** -/
theorem card_zsmul_preimage_eq_card_ker {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    {T P₀ : (W⁄F).toAffine.Point} (hP₀ : n • P₀ = T) :
    Nat.card {P : (W⁄F).toAffine.Point // n • P = T} =
      Nat.card (mulByIntIsogeny W hn).ker := by
  rw [card_zsmul_preimage_eq_card_zsmul_eq_zero hP₀]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight fun _ ↦ (mem_ker_mulByIntIsogeny_iff W hn).symm)

/-- **`[n]` is `n ²`-to-one where it hits at all**, over an algebraically closed field in which
`n` is invertible. -/
theorem card_zsmul_preimage [IsAlgClosed F] {n : ℤ} {hn : psiFunctionField W n ≠ 0}
    (hchar : (n : F) ≠ 0) {T P₀ : (W⁄F).toAffine.Point} (hP₀ : n • P₀ = T) :
    Nat.card {P : (W⁄F).toAffine.Point // n • P = T} = n.natAbs ^ 2 := by
  rw [card_zsmul_preimage_eq_card_ker W hn hP₀, card_ker_mulByIntIsogeny W hchar]

end TauCeti.Isogeny

end
