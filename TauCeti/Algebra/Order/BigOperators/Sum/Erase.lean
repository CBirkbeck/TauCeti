/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# What a term-by-term lower bound leaves for the erased index

If a finite family `d` has a known total and every other term of a family `a` is within `η'` below
its counterpart in `d`, then the sum of `a` over the erased index set cannot fall much short of
what `d` leaves there.  This is the arithmetic behind a squeeze: knowing every member of a finite
family from below, together with the total, bounds the remaining member from above.

## Main results

* `Finset.sub_sub_le_sum_erase_of_forall_sub_le`: the erased sum of `a` is at least the total of
  `d` minus the erased term minus the accumulated slack.
-/

public section

namespace Finset

/-- **What a term-by-term lower bound leaves.** If `d` sums to `t` over `s` and every `a i` away
from `i₀` is within `η'` below `d i`, the erased sum falls short of `t - d i₀` by at most
`#s * η'`.

Pure arithmetic on a finite index set in an ordered ring: the slack is charged once per index, so
the whole error is `#s * η'`, and any `η` dominating that will do. Stating it with `η` rather than
`#s * η'` lets a caller fix an error budget first and choose `η'` afterwards. -/
theorem sub_sub_le_sum_erase_of_forall_sub_le {ι R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] [DecidableEq ι] {s : Finset ι} {d a : ι → R} {t η η' : R} {i₀ : ι}
    (hi₀ : i₀ ∈ s) (hd : ∑ i ∈ s, d i = t) (ha : ∀ i ∈ s.erase i₀, d i - η' ≤ a i) (hη' : 0 ≤ η')
    (hη : (s.card : R) * η' ≤ η) :
    t - d i₀ - η ≤ ∑ i ∈ s.erase i₀, a i := by
  have hlb := Finset.sum_le_sum ha
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_erase_eq_sub hi₀,
    hd] at hlb
  have hcard : ((s.erase i₀).card : R) ≤ (s.card : R) := by exact_mod_cast Finset.card_erase_le
  have hbound : ((s.erase i₀).card : R) * η' ≤ η :=
    (mul_le_mul_of_nonneg_right hcard hη').trans hη
  exact (sub_le_sub_left hbound _).trans hlb

end Finset
