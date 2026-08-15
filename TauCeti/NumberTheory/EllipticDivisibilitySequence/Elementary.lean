/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Vanishing at zero and oddness of an elliptic sequence

`IsEllipticSequence W` constrains `W` on every triple of integers. Two facts about `W` alone
follow, given that suitable terms are nonzerodivisors: `W` vanishes at `0`, and `W` is an odd
function.

Both are used elsewhere as *hypotheses*. `Descent.lean` carries `zero : W 0 = 0` and
`odd : W.Odd` on `IsEllipticNet.of_rel` and on the two equivalences, and it must: those results
reconstruct the relation from the two doubling recurrences, so they cannot assume the relation
they are proving. The lemmas here go the other way — the relation is the hypothesis — so they
apply exactly where a caller already has `IsEllipticSequence W` in hand.

## Main results

* `IsEllipticSequence.zero`: `W 0 = 0`, given that some even term is a nonzerodivisor.
* `IsEllipticSequence.neg`: `W (-m) = -W m`, given that `W 1` and `W 2` are nonzerodivisors.
* `IsEllipticSequence.odd`: the same, packaged as Mathlib's `Function.Odd`.

## Implementation notes

Each proof specialises the relator at indices chosen to make all but one term cancel, then
divides by the surviving nonzerodivisor.

For `zero` the choice is `(m, m, 2 * m)`: the two outer terms of `rel` coincide and cancel, and
the first collapses to `W 0 * W (2 * m) ^ 3`.

For `neg` the relator is symmetrised first. Adding `rel W m n r 0` to `rel W n m r 0` cancels the
two outer terms against each other and leaves `(W (m - n) + W (n - m)) * W (m + n) * W r ^ 2`,
which is `sub_add_neg_sub_mul_eq_zero`. Choosing `(1 - k, k + 1, 1)` puts `2` in the middle slot
and `-(2 * k)` in the first, and `(-k, k + 1, 1)` puts `1` and `-(2 * k + 1)` there; those are the
even and odd cases, and they are why both `W 1` and `W 2` are needed.

## Provenance

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declarations `IsEllSequence.zero`, `IsEllSequence.sub_add_neg_sub_mul_eq_zero` and
`IsEllSequence.neg`. That file's header reads `Authors: David Kurniadi Angdinata`; following this
repository's convention for adapted material the upstream authorship is credited here rather than
in the copyright header. J. Xu is acknowledged for the surrounding LutzNagell development — he
authors `Universal.lean` and co-authors `DivisionPolynomialOmega.lean` at the same revision — as
context for this port, not as an author of the declarations above.

The source also carries a `zero'` proved from `IsReduced R` rather than from a nonzerodivisor.
It is not ported: `zero` below is what the development uses, and `IsReduced` is a hypothesis no
consumer in this repository has.
-/

public section

open scoped nonZeroDivisors

namespace IsEllipticSequence

variable {R : Type*} [CommRing R] {W : ℤ → R}

/-- **An elliptic sequence vanishes at `0`**, given that some even term is a nonzerodivisor.

At `(m, m, 2 * m)` the relator's two outer terms are equal and cancel, leaving
`W 0 * W (2 * m) ^ 3`. -/
protected theorem zero (h : IsEllipticSequence W) (m : ℤ) (mem : W (2 * m) ∈ R⁰) : W 0 = 0 := by
  have key : W 0 * W (2 * m) ^ 3 = 0 := by
    have := h m m (2 * m)
    rw [IsEllipticNet.rel] at this
    simp only [add_zero] at this
    rw [show m + m = 2 * m by ring, show m - m = (0 : ℤ) by ring] at this
    linear_combination this
  exact (pow_mem mem 3).2 _ key

/-- **The symmetrised relator vanishes.** Adding `rel W m n r 0` to `rel W n m r 0` cancels the
two outer terms against each other, leaving the first slot's contribution from each. -/
theorem sub_add_neg_sub_mul_eq_zero (h : IsEllipticSequence W) (m n r : ℤ) :
    (W (m - n) + W (n - m)) * W (m + n) * W r ^ 2 = 0 := by
  have hmn := h m n r
  have hnm := h n m r
  rw [IsEllipticNet.rel] at hmn hnm
  simp only [add_zero] at hmn hnm
  rw [show n + m = m + n by ring] at hnm
  linear_combination hmn + hnm

/-- **An elliptic sequence is an odd function**, given that `W 1` and `W 2` are nonzerodivisors.

The two parities use different slots of `sub_add_neg_sub_mul_eq_zero`, which is why both terms
are needed: the even case divides by `W 2 * W 1 ^ 2`, the odd case by `W 1 ^ 3`. -/
protected theorem neg (h : IsEllipticSequence W) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (m : ℤ) :
    W (-m) = -W m := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨k, rfl | rfl⟩ := m.even_or_odd'
  · have := h.sub_add_neg_sub_mul_eq_zero (1 - k) (k + 1) 1
    rw [show (1 : ℤ) - k - (k + 1) = -(2 * k) by ring,
      show (k + 1) - (1 - k) = 2 * k by ring, show (1 : ℤ) - k + (k + 1) = 2 by ring] at this
    exact (mul_mem two (pow_mem one 2)).2 _ (by linear_combination this)
  · have := h.sub_add_neg_sub_mul_eq_zero (-k) (k + 1) 1
    rw [show (-k : ℤ) - (k + 1) = -(2 * k + 1) by ring,
      show (k + 1) - -k = 2 * k + 1 by ring, show (-k : ℤ) + (k + 1) = 1 by ring] at this
    exact (mul_mem one (pow_mem one 2)).2 _ (by linear_combination this)

/-- **An elliptic sequence is odd**, in Mathlib's `Function.Odd` spelling — the form
`SignEquivariance.lean` and `Descent.lean` take as a hypothesis. -/
protected theorem odd (h : IsEllipticSequence W) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) : W.Odd :=
  fun m ↦ h.neg one two m

end IsEllipticSequence
