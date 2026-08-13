/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Index bookkeeping for the descent on the elliptic relator

Mathlib's `IsEllipticNet.atomRel_avg_sub` transfers the four-index relator from a quadruple
`a, b, c, d` to the quadruple obtained by subtracting each index from the average
`m = (a + b + c + d) / 2`, in reverse order:

`atomRel W (m - d) (m - c) (m - b) (m - a) = atomRel W a b c d`.

The descent that identifies elliptic sequences runs on that transfer, and needs to know that its
two side conditions survive it: the four indices stay of one parity, and — after taking the
absolute value of the last, which `IsEllipticNet.atomRel_abs₄` absorbs — they stay nonnegative and
strictly decreasing. This file proves both, together with the bound `6 ≤ a` that makes the descent
terminate.

## Main definitions

* `IsEllipticNet.StrictAnti₄`: the four indices are nonnegative and strictly decreasing. The
  nonnegativity is bundled in because every use needs it alongside the ordering.

## Main results

* `IsEllipticNet.parity_avg_sub`: same parity survives the transfer.
* `IsEllipticNet.strictAnti₄_avg_sub`: nonnegativity and strict decrease survive it.
* `IsEllipticNet.six_le_of_strictAnti₄`: a strictly decreasing quadruple of one parity with
  `0 ≤ d` has `6 ≤ a` — consecutive indices differ by at least two, three times over.

## Implementation notes

Parity is spelled as Mathlib spells it for this API — the unbundled conjunction
`d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2`, relative to the last index, as
`IsEllipticNet.atomRel_eq` and `atomRel_avg_sub` take it — rather than as the source's bundled
predicate over `Int.negOnePow`. Matching the upstream shape means those two lemmas apply with no
conversion at the use sites, and avoids standing a second parity predicate next to Mathlib's.

That choice also shortens the proofs: `omega` reasons about `%` and `/` by the literal `2`
natively, so the parity bookkeeping the source carries out through `negOnePow_sub`,
`negOnePow_abs` and `add_two_le_iff_lt_of_even_sub` is discharged directly here.

## Provenance

Ported from J. Xu's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declarations `StrictAnti₄`, `HaveSameParity₄.transf`,
`HaveSameParity₄.strictAnti₄_transf` and `HaveSameParity₄.six_le_of_strictAnti₄`. That file's
header reads `Authors: Junyan Xu`; following this repository's convention for adapted material the
upstream authorship is credited here rather than in the copyright header.

The source's surrounding transfer machinery is **not** ported, being already upstream: its
`rel₄_transf` is Mathlib's `atomRel_avg_sub`, its `rel₄_eq_net` is Mathlib's `atomRel_eq`, and its
`avg₄` is inlined there as `(a + b + c + d) / 2`. With `rel₄_transf` unneeded, so are the four
declarations existing only to prove it — `addMulSub₄`, `addMulSub₄_mul_addMulSub₄`,
`addMulSub_transf` and `avg₄_add_avg₄`. That is also why no `set_option allowUnsafeReducibility`
appears here: the one source lemma carrying it is among those not needed.
-/

public section

namespace IsEllipticNet

/-- The four indices are nonnegative and strictly decreasing. Nonnegativity is bundled in because
the descent needs it wherever it needs the ordering. -/
def StrictAnti₄ (a b c d : ℤ) : Prop := 0 ≤ d ∧ d < c ∧ c < b ∧ b < a

/-- The defining formula for `StrictAnti₄`. The definition body is not exposed, so this equation
lemma is how a consumer computes with it. -/
theorem strictAnti₄_def (a b c d : ℤ) :
    StrictAnti₄ a b c d ↔ 0 ≤ d ∧ d < c ∧ c < b ∧ b < a := Iff.rfl

/-- **Same parity survives the transfer.** Stated for the transferred quadruple in the order
`atomRel_avg_sub` produces it, and with the absolute value on the last index that
`atomRel_abs₄` absorbs. -/
theorem parity_avg_sub {a b c d : ℤ}
    (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2) :
    |(a + b + c + d) / 2 - a| % 2 = ((a + b + c + d) / 2 - d) % 2 ∧
      |(a + b + c + d) / 2 - a| % 2 = ((a + b + c + d) / 2 - c) % 2 ∧
        |(a + b + c + d) / 2 - a| % 2 = ((a + b + c + d) / 2 - b) % 2 := by
  obtain ⟨h₁, h₂, h₃⟩ := parity
  rcases abs_cases ((a + b + c + d) / 2 - a) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

/-- **Nonnegativity and strict decrease survive the transfer.** The last index needs its absolute
value: `m - a` is the one difference that can be negative, `a` being the largest index. -/
theorem strictAnti₄_avg_sub {a b c d : ℤ}
    (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2) (anti : StrictAnti₄ a b c d) :
    StrictAnti₄ ((a + b + c + d) / 2 - d) ((a + b + c + d) / 2 - c) ((a + b + c + d) / 2 - b)
      |(a + b + c + d) / 2 - a| := by
  obtain ⟨h₁, h₂, h₃⟩ := parity
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  refine ⟨abs_nonneg _, ?_, by omega, by omega⟩
  rcases abs_cases ((a + b + c + d) / 2 - a) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

/-- A strictly decreasing quadruple of one parity, bounded below by zero, has `6 ≤ a`: each of the
three consecutive gaps is at least two. This is what makes the descent terminate. -/
theorem six_le_of_strictAnti₄ {a b c d : ℤ}
    (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2) (anti : StrictAnti₄ a b c d) :
    6 ≤ a := by
  obtain ⟨h₁, h₂, h₃⟩ := parity
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  omega

end IsEllipticNet
