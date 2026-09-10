/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution

/-!
# Integer discrete convolution as a sum over one index

Mathlib's `DiscreteConvolution.addConvolution` sums over the fibre `addFiber n`, the
antidiagonal `{(i, j) | i + j = n}`. Over `ℤ` that fibre is parametrised by its first
coordinate, which turns the convolution into a single sum:

* `DiscreteConvolution.addFiberEquivInt`: the parametrisation `k ↦ (k, n - k)`;
* `DiscreteConvolution.addConvolution_mul_apply`: `(f ⋆ g) n = ∑' k, f k * g (n - k)`, the
  familiar Laurent convolution.

The equivalence is an `Equiv` rather than a `Finset` because the antidiagonal in `ℤ × ℤ` is
infinite. Nothing here is specific to any ring of interest; it is the bridge between Mathlib's
fibre picture and the `ℤ`-indexed one.
-/

@[expose] public section

namespace DiscreteConvolution

/-- **The antidiagonal `{(i, j) | i + j = n}` in `ℤ × ℤ`, parametrised by its first
coordinate.** This is where the `ℤ`-indexed picture and Mathlib's fibre picture meet, and it is
an `Equiv` rather than a `Finset` precisely because the antidiagonal is infinite. -/
def addFiberEquivInt (n : ℤ) : ℤ ≃ (addFiber n : Set (ℤ × ℤ)) where
  toFun k := ⟨(k, n - k), by grind⟩
  invFun ab := ab.1.1
  left_inv _ := rfl
  right_inv ab := by grind

/-- **The integer convolution is a single sum**: `(f ⋆ g) n = ∑' k, f k * g (n - k)`, the
familiar Laurent convolution. Reindexing Mathlib's sum over `addFiber n` by the first coordinate
is exactly `DiscreteConvolution.addFiberEquivInt`. -/
theorem addConvolution_mul_apply {A : Type*} [Ring A] [TopologicalSpace A] (f g : ℤ → A)
    (n : ℤ) : addConvolution (LinearMap.mul ℤ A) f g n = ∑' k : ℤ, f k * g (n - k) :=
  ((addFiberEquivInt n).tsum_eq fun ab ↦ f ab.1.1 * g ab.1.2).symm

end DiscreteConvolution

end
