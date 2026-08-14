/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# The doubling relations of an elliptic sequence, solved for the doubled term

`IsEllipticSequence W` says that `IsEllipticNet.rel W p q r 0` vanishes for all `p, q, r`.
Mathlib's `IsEllipticNet.rel_odd` and `rel_even` evaluate that relator at the two instances
relating a doubled index to its neighbours, but they give the relator's *value* rather than what
its vanishing says.

This file supplies that second step: at each of those instances, the relator vanishes exactly when
the doubled-index term stands in a named relation to the neighbouring terms. That is the form the
division-polynomial development consumes, since the hypothesis in hand there is
`IsEllipticSequence`, which supplies vanishing rather than a value.

## Main results

* `IsEllipticNet.rel_odd_eq_zero_iff`: `rel W (m + 1) m 1 0 = 0` iff
  `W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3`.
* `IsEllipticNet.rel_even_eq_zero_iff`: `rel W (m + 1) (m - 1) 1 0 = 0` iff
  `W (2 * m) * W 2 * W 1 ^ 2 = W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2)`.

## Implementation notes

These are equations about the doubled-index term, not new predicates. An earlier draft followed
the source in introducing `OddRec` and `EvenRec` as `Prop` definitions; that stood a second
recurrence interface beside Mathlib's `rel_odd` / `rel_even`, which already name these two
instances. Deriving the vanishing form from those lemmas leaves one API rather than two, and makes
each proof a rewrite followed by a rearrangement.

The equations **relate** the doubled-index term to its neighbours; they do not on their own
determine it. Nothing here inverts `W 1` or `W 2 * W 1 ^ 2`, and over an arbitrary `CommRing`
neither need be a unit, so solving for `W (2 * m + 1)` or `W (2 * m)` requires a hypothesis this
file does not carry.

## Provenance

Adapted from J. Xu's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declarations `OddRec`, `EvenRec`, `rel₃_iff_oddRec`
and `rel₃_iff_evenRec`. That file's header reads `Authors: Junyan Xu`; following this repository's
convention for adapted material the upstream authorship is credited here rather than in the
copyright header.

The adaptation is substantial, because Mathlib has since absorbed most of what the source had to
build for itself. The source states its equivalences against `Rel₃`, a three-index relation of its
own, and carries `OddRec` / `EvenRec` as `Prop` definitions naming the right-hand sides. Mathlib
supplies `Rel₃` as `rel W p q r 0` — the shape `IsEllipticSequence` quantifies over — and supplies
`rel_odd` / `rel_even` as the evaluations at these two instances. What remains to port is the
passage from value to vanishing, which is what the two lemmas here do.

The source's `rel₄_iff_evenRec`, a third equivalence against the four-index relator at
`(2 * m + 1, 2 * m - 1, 3, 1)`, is not ported. It is the one declaration in this group carrying
`set_option allowUnsafeReducibility true` together with an `attribute [local reducible]
Nat.rawCast`, which this repository has previously declined to take on, and it belongs with the
descent layer that consumes it.
-/

public section

namespace IsEllipticNet

variable {R : Type*} [CommRing R] (W : ℤ → R) (m : ℤ)

/-- **The odd doubling relation, in vanishing form.** The relator at `(m + 1, m, 1, 0)` vanishes
exactly when `W (2 * m + 1)` stands in this relation to its neighbours. -/
theorem rel_odd_eq_zero_iff : rel W (m + 1) m 1 0 = 0 ↔
    W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3 := by
  rw [rel_odd]
  constructor <;> intro h <;> linear_combination h

/-- **The even doubling relation, in vanishing form.** The relator at `(m + 1, m - 1, 1, 0)`
vanishes exactly when `W (2 * m)` stands in this relation to its neighbours. -/
theorem rel_even_eq_zero_iff : rel W (m + 1) (m - 1) 1 0 = 0 ↔
    W (2 * m) * W 2 * W 1 ^ 2 =
      W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2) := by
  rw [rel_even]
  constructor <;> intro h <;> linear_combination h

end IsEllipticNet
