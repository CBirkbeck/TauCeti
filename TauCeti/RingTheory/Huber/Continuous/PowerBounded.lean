/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.PowerBounded
public import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# A continuous archimedean valuation is bounded by one on the power-bounded elements

**Wedhorn Proposition 7.41.** If `v` is a continuous valuation whose value monoid is
archimedean, and some topologically nilpotent `b` has `v b ≠ 0`, then `v a ≤ 1` for every
power-bounded `a`.

The two hypotheses on `v` are what Wedhorn's `x ∈ Cont(A)ᵃ of height 1` supplies. Height one
gives archimedean value group — Mathlib's `Valuation.nonempty_rankOne_iff_mulArchimedean` is that
equivalence — and analyticity gives the topologically nilpotent `b` with `v b ≠ 0`, which is
Wedhorn's Remark 7.40(1). Stating the archimedean property and the witness directly rather than
through `Valuation.RankOne` and `IsAnalyticPoint` keeps the statement at the level its proof uses.

The argument is Wedhorn's. Suppose `1 < v a`. Archimedeanness gives `n` with
`(v b)⁻¹ ≤ v a ^ n`, hence `1 ≤ v (a ^ n * b)`. But `a ^ n` is power-bounded and `b` is
topologically nilpotent, so `a ^ n * b` is topologically nilpotent, and continuity forces
`v (a ^ n * b) < 1`. The two bounds are incompatible, so no such `a` exists.

## Main results

* `TauCeti.Huber.le_one_of_isPowerBounded`: Proposition 7.41.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.41, whose proof
  this follows step by step, together with Remark 7.40(1) for the witness `b` and Proposition
  1.14 for height one implying archimedean.
-/

public section

namespace TauCeti.Huber

open TauCeti Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [MulArchimedean Γ₀]

/-- **Wedhorn Proposition 7.41.** A continuous valuation with archimedean value monoid, which is
nonzero on some topologically nilpotent element, is bounded by `1` on the power-bounded elements.

The witness `b` is what analyticity supplies (Wedhorn Remark 7.40(1)); without it the statement
fails, since the trivial valuation is continuous and unbounded on `A°`. -/
theorem le_one_of_isPowerBounded {v : Valuation A Γ₀} (hv : v.IsContinuous) {b : A}
    (hb : IsTopologicallyNilpotent b) (hb0 : v b ≠ 0) {a : A} (ha : IsPowerBounded a) :
    v a ≤ 1 := by
  by_contra! hgt
  -- archimedeanness of the value monoid: some power of `v a` overtakes `(v b)⁻¹`
  obtain ⟨n, hn⟩ := MulArchimedean.arch (v b)⁻¹ hgt
  -- so `a ^ n * b` has value at least `1`
  have hab : (1 : Γ₀) ≤ v (a ^ n * b) := by
    rw [map_mul, map_pow, ← inv_mul_cancel₀ hb0]
    exact mul_le_mul' hn le_rfl
  -- but it is topologically nilpotent, and a continuous valuation is `< 1` there
  exact absurd hab (not_le.mpr (hv.lt_one_of_isTopologicallyNilpotent
    ((ha.pow n).isTopologicallyNilpotent_mul hb)))

end Huber

end TauCeti
