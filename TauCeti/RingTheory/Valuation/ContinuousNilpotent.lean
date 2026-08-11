/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import TauCeti.RingTheory.Valuation.CofinalIdeal.Basic
public import TauCeti.RingTheory.Valuation.Continuous

/-!
# A continuous valuation at a topologically nilpotent element

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Theorem 7.10 and Remark 7.11(1), in the
directions that need no Huber-ring hypothesis.**

Continuity says every `{x ; v x < v b}` is open, and topological nilpotence says the powers of
`a` eventually enter every neighbourhood of `0`. Putting the two together bounds `v a`, and this
file records the two bounds Theorem 7.10 asks for — which are *not* the same statement and do not
need the same hypotheses.

* `v a < 1`, at `b = 1`. The threshold `1 = v 1` is a value `v` attains, so the ball is open by
  the definition of continuity alone: no compatibility between the topology and the ring
  operations is used, and the codomain need only be a `LinearOrderedCommMonoidWithZero`.
* `v a` is **cofinal** in the value group `Γ_v`: for every `γ ∈ Γ_v` some power `v a ^ n` falls
  below `γ`. This is strictly stronger and costs strictly more, for the reason below.

## The value group, not the codomain

Cofinality quantifies over `Γ_v`, the subgroup of the codomain *generated* by the attained
values, so a general `γ` is a **ratio** `v t / v r` and not itself attained. That is exactly what
`Valuation.IsContinuous.isOpen_lt_div` supplies, and it is why this proof reaches for the ratio
form of continuity rather than the attained-value one: `{x ; v x < γ}` has to be open for the
ratios too before topological nilpotence can be applied to it. Mathlib's
`MonoidWithZeroHom.ValueGroup₀.zero_or_exists_mk` is what puts a general element of `Γ_v` in
that form.

## Why `lt_one` is not just the case `γ = 1`

Cofinality does imply `v a < 1`, through `CofinalValueFor.lt_one`. But that route pays for the
general `γ`: a group codomain, and `[SeparatelyContinuousMul A]` for the ratios. Since
`Spv (A, I·A)` membership is a condition on all of `Γ_v` while the second conjunct of Theorem
7.10 is a condition on `1` alone, the two really are separate obligations, and the second is
recorded at its own — much weaker — hypotheses rather than as a corollary of the first.

## Main results

* `TauCeti.Valuation.lt_one_of_isContinuous_of_isTopologicallyNilpotent`
* `TauCeti.Valuation.CofinalValueFor.of_isContinuous_of_isTopologicallyNilpotent`

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark 7.11 and Theorem 7.10.
-/

public section

namespace TauCeti.Valuation

open MonoidWithZeroHom TauCeti

variable {A : Type*} [Ring A] [TopologicalSpace A]

section Monoid

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀]

/-- **The second conjunct of Wedhorn Theorem 7.10.** A continuous valuation is `< 1` at every
topologically nilpotent element.

The threshold `1` is the attained value `v 1`, so the ball `{x ; v x < 1}` is open straight from
the definition of continuity: nothing relates the topology to the ring operations, and the
codomain is only a monoid — contrast
`CofinalValueFor.of_isContinuous_of_isTopologicallyNilpotent`, which needs both.

`Nontrivial Γ₀` is not decoration. If `0 = 1` in `Γ₀` then `Γ₀` is trivial, every `{x ; v x < v b}`
is empty and so open, and the conclusion `v a < 1` reads `0 < 0`; a group codomain rules this out
by fiat, a monoid one does not. -/
theorem lt_one_of_isContinuous_of_isTopologicallyNilpotent {v : Valuation A Γ₀}
    (hv : v.IsContinuous) {a : A} (ha : IsTopologicallyNilpotent a) : v a < 1 := by
  obtain ⟨n, hn⟩ := ha.exists_pow_mem_of_mem_nhds
    ((isContinuous_def.mp hv 1).mem_nhds (by simp [zero_le_one.lt_of_ne zero_ne_one]))
  rw [Set.mem_ofPred_eq, map_pow, map_one] at hn
  exact not_le.mp fun h ↦ absurd hn (not_lt.mpr (one_le_pow₀ h))

end Monoid

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Wedhorn Remark 7.11(1), the direction that holds for any topological ring.** A continuous
valuation has cofinal values at every topologically nilpotent element: the powers of `a` are
eventually inside each ball `{x ; v x < γ}`, and continuity is what makes that ball open.

A general `γ ∈ Γ_v` is a ratio `v t / v r` of attained values rather than an attained value, so
the ball is opened by `IsContinuous.isOpen_lt_div` — whence `[SeparatelyContinuousMul A]`. -/
theorem CofinalValueFor.of_isContinuous_of_isTopologicallyNilpotent [SeparatelyContinuousMul A]
    {v : Valuation A Γ₀} (hv : v.IsContinuous) {a : A} (ha : IsTopologicallyNilpotent a) :
    CofinalValueFor v ⊤ a := by
  rw [cofinalValueFor_def]
  intro γ _
  obtain hz | ⟨r, t, hr, ht, hmk⟩ :=
    ValueGroup₀.zero_or_exists_mk (f := .ofClass v) (γ : ValueGroup₀ (.ofClass v))
  · exact absurd hz (by simp)
  · -- the ball of radius `v t / v r` is open and contains `0`, so a power of `a` lands in it
    obtain ⟨n, hn⟩ := ha.exists_pow_mem_of_mem_nhds
      ((hv.isOpen_lt_div t hr).mem_nhds (by simpa using zero_lt_iff.mpr (div_ne_zero ht hr)))
    refine ⟨n, ?_⟩
    have hemb : ValueGroup₀.embedding
        ((valueGroup.mk (ofClass v) r t hr ht : ValueGroup₀ (.ofClass v))) = v t / v r := by
      simp [valueGroup.mk, ValueGroup₀.embedding, div_eq_mul_inv, mul_comm]
    rw [← map_pow, Valuation.restrict_lt_iff_lt_embedding, hmk, hemb]
    exact hn

end TauCeti.Valuation
