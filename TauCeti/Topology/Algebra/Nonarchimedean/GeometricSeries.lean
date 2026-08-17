/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# The geometric series in a complete nonarchimedean ring

**Wedhorn, *Adic Spaces*, Proposition 5.38.** In a complete nonarchimedean topological ring,
`1 - a` is a unit for every topologically nilpotent `a`, with `∑ aⁿ` as its inverse.

Nonarchimedean is what makes this cheap. In a general topological ring the geometric series need
not converge just because its terms tend to `0`, but in a nonarchimedean additive group summability
is *equivalent* to the terms tending to zero along the cofinite filter
(`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`) — and for the powers of `a` that is
precisely topological nilpotence. Completeness then makes the sum exist, and Mathlib's
`Summable.one_sub_mul_tsum_pow` identifies it as the inverse.

Mathlib has the analytic counterpart, `isUnit_one_sub_of_norm_lt_one`, which needs a norm; the
nonarchimedean-topological statement is what the Huber theory uses, since a Huber ring carries no
canonical norm.

## Main results

* `IsTopologicallyNilpotent.summable_pow` : the geometric series `∑ aⁿ` is summable.
* `IsTopologicallyNilpotent.neg` : the negation of a topologically nilpotent element is
  topologically nilpotent.
* `IsTopologicallyNilpotent.isUnit_one_sub` : Proposition 5.38 itself.
* `IsTopologicallyNilpotent.isUnit_one_add` : the `1 + a` form, which is the one consumers want.

## Provenance

Ported from AINTLIB's `projects/AdicSpaces/Adic spaces/GeometricSeries.lean`, branch
`dev/adic-spaces`, commit `37bbdaeb`, which states the same four results over the same hypotheses.
The proofs are AINTLIB's and rest entirely on Mathlib primitives; the statements are unchanged, and
the `omit` annotations record which hypotheses each result genuinely needs.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.38.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/GeometricSeries.lean`.
-/

open Filter Topology

public section

variable {A : Type*} [CommRing A] [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]

omit [T2Space A] [IsTopologicalRing A] in
/-- **The geometric series of a topologically nilpotent element is summable.** In a nonarchimedean
additive group summability is equivalent to the terms tending to zero cofinitely, which for powers
is topological nilpotence. -/
theorem IsTopologicallyNilpotent.summable_pow {a : A} (ha : IsTopologicallyNilpotent a) :
    Summable (a ^ · : ℕ → A) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
  exact ha

omit [T2Space A] [CompleteSpace A] [IsTopologicalRing A] [IsUniformAddGroup A] in
/-- **The negation of a topologically nilpotent element is topologically nilpotent.** The odd
powers pick up a sign, which an open subgroup absorbs. -/
theorem IsTopologicallyNilpotent.neg {a : A} (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (-a) := by
  intro U hU
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  refine (ha.eventually (V.isOpen.mem_nhds V.zero_mem')).mono fun n hn ↦ hVU ?_
  change (-a) ^ n ∈ (V : Set A)
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_pow]; exact hn
  · rw [ho.neg_pow]; exact V.neg_mem' hn

/-- **Wedhorn Proposition 5.38**: in a complete nonarchimedean ring, `1 - a` is a unit for every
topologically nilpotent `a`, the inverse being `∑ aⁿ`. -/
theorem IsTopologicallyNilpotent.isUnit_one_sub {a : A} (ha : IsTopologicallyNilpotent a) :
    IsUnit (1 - a) :=
  .of_mul_eq_one _ ha.summable_pow.one_sub_mul_tsum_pow

/-- **`1 + a` is a unit for topologically nilpotent `a`**, by Proposition 5.38 applied to `-a`.
This is the form consumers use: the units of a complete nonarchimedean ring contain the coset
`1 + A°°`, which is what makes the unit group open. -/
theorem IsTopologicallyNilpotent.isUnit_one_add {a : A} (ha : IsTopologicallyNilpotent a) :
    IsUnit (1 + a) := by
  rw [← sub_neg_eq_add]
  exact ha.neg.isUnit_one_sub

end
