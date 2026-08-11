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
# Continuity makes the values of a topologically nilpotent element cofinal

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Remark 7.11(1), the direction that needs no
Huber-ring hypothesis.**

If `v` is continuous and `a` is topologically nilpotent, then `v a` is cofinal in the value
group `Γ_v`: for every `γ ∈ Γ_v` some power `v a ^ n` falls below `γ`.

## The value group, not the codomain

Cofinality quantifies over `Γ_v`, the subgroup of the codomain *generated* by the attained
values, so a general `γ` is a **ratio** `v t / v r` and not itself attained. That is exactly what
`Valuation.IsContinuous.isOpen_lt_div` supplies, and it is why this proof reaches for the ratio
form of continuity rather than the attained-value one: `{x ; v x < γ}` has to be open for the
ratios too before topological nilpotence can be applied to it. Mathlib's
`MonoidWithZeroHom.ValueGroup₀.zero_or_exists_mk` is what puts a general element of `Γ_v` in
that form.

## Relation to the `v a < 1` statement

Taking `γ = 1` recovers "a continuous valuation is `< 1` on topologically nilpotent elements",
the shape in which the forward half of Wedhorn Theorem 7.10 is usually quoted. Cofinality is
strictly stronger, and it is the form Theorem 7.10 actually needs, since membership of
`Spv (A, I·A)` is a statement about all of `Γ_v` rather than about `1` alone.

## Main results

* `TauCeti.Valuation.CofinalValueFor.of_isContinuous_of_isTopologicallyNilpotent`

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark 7.11 and Theorem 7.10.
-/

public section

namespace TauCeti.Valuation

open MonoidWithZeroHom TauCeti

variable {A : Type*} [Ring A] [TopologicalSpace A]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

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
