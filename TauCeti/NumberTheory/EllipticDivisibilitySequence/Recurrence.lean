/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# The odd and even recurrences of an elliptic sequence

An elliptic sequence satisfies `IsEllipticNet.rel W p q r 0 = 0` for all `p, q, r` — that is
Mathlib's `IsEllipticSequence`. Two particular cases of that relation are the recurrences that
compute the sequence term by term, doubling the index:

* at `(m + 1, m, 1)` the relation says how `W (2 * m + 1)` is determined by lower terms;
* at `(m + 1, m - 1, 1)` it says the same for `W (2 * m)`.

This file names those two right-hand sides, `OddRec` and `EvenRec`, and proves that each is
equivalent to the corresponding instance of Mathlib's relator. Naming them is what lets the
division-polynomial development state the doubling step without carrying the four-index relator
through every use site.

## Main definitions

* `IsEllipticNet.OddRec`: the recurrence for `W (2 * m + 1)`.
* `IsEllipticNet.EvenRec`: the recurrence for `W (2 * m)`.

## Main results

* `IsEllipticNet.rel_iff_oddRec`: the relator at `(m + 1, m, 1, 0)` vanishes iff `OddRec` holds.
* `IsEllipticNet.rel_iff_evenRec`: the relator at `(m + 1, m - 1, 1, 0)` vanishes iff `EvenRec`
  holds.

## Implementation notes

The recurrences are stated over Mathlib's `IsEllipticNet.rel` at `s = 0`, which is exactly the
shape `IsEllipticSequence` quantifies over — `IsEllipticSequence W ↔ ∀ p q r, rel W p q r 0 = 0`
holds by definition. The source states them over a three-index predicate of its own; taking
Mathlib's four-index relator with `s = 0` instead means a consumer that has `IsEllipticSequence`
can apply these directly, and no second relation stands beside Mathlib's.

## Provenance

Ported from J. Xu's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declarations `OddRec`, `EvenRec`,
`rel₃_iff_oddRec` and `rel₃_iff_evenRec`. That file's header reads `Authors: Junyan Xu`; following
this repository's convention for adapted material the upstream authorship is credited here rather
than in the copyright header.

The source states both equivalences against its own `Rel₃`, a three-index predicate defined as the
`d = 0` case of its four-index relation. Mathlib supplies that case as `rel W p q r 0`, so `Rel₃`
is not ported: the equivalences are stated against Mathlib's relator directly.

The source's `rel₄_iff_evenRec`, a third equivalence against the four-index relator at
`(2 * m + 1, 2 * m - 1, 3, 1)`, is **not** ported here. It is the one declaration in this group
carrying `set_option allowUnsafeReducibility true` together with a `Nat.rawCast` reducibility
attribute, which this repository does not take on unexamined; it belongs with the descent layer
that consumes it rather than with the definitions.
-/

public section

namespace IsEllipticNet

variable {R : Type*} [CommRing R] (W : ℤ → R) (m : ℤ)

/-- The recurrence determining the odd-index term `W (2 * m + 1)` of an elliptic sequence. -/
def OddRec : Prop :=
  W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3

/-- The recurrence determining the even-index term `W (2 * m)` of an elliptic sequence. -/
def EvenRec : Prop :=
  W (2 * m) * W 2 * W 1 ^ 2 = W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2)

/-- **The odd recurrence is the relator at `(m + 1, m, 1, 0)`.** -/
theorem rel_iff_oddRec : rel W (m + 1) m 1 0 = 0 ↔ OddRec W m := by
  rw [rel, OddRec]
  ring_nf
  constructor <;> intro h <;> linear_combination h

/-- **The even recurrence is the relator at `(m + 1, m - 1, 1, 0)`.** -/
theorem rel_iff_evenRec : rel W (m + 1) (m - 1) 1 0 = 0 ↔ EvenRec W m := by
  rw [rel, EvenRec]
  ring_nf
  constructor <;> intro h <;> linear_combination h

end IsEllipticNet
