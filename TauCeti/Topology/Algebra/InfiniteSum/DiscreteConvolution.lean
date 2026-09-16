/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution

/-!
# Convolution of single-point families

Mathlib's `DiscreteConvolution.single_ringConvolution` says that `Pi.single 1 1` is a unit for
multiplication convolution. More generally, the convolution of two families supported at one point
each is supported at the product of the points, with the product of the values.

## Main results

* `DiscreteConvolution.single_ringConvolution_single` and its additive version
  `DiscreteConvolution.single_addRingConvolution_single`:
  `Pi.single m a ⋆ᵣ Pi.single n b = Pi.single (m * n) (a * b)`.
-/

public section

open scoped DiscreteConvolution

namespace DiscreteConvolution

variable {M R : Type*} [Monoid M] [DecidableEq M] [NonUnitalNonAssocSemiring R]
  [TopologicalSpace R]

/-- **The convolution of two single-point families is a single-point family**, at the product of
the points and with the product of the values. -/
@[to_additive (dont_translate := R) single_addRingConvolution_single]
theorem single_ringConvolution_single (m n : M) (a b : R) :
    Pi.single m a ⋆ᵣ Pi.single n b = Pi.single (m * n) (a * b) := by
  ext p
  simp only [ringConvolution_apply, Pi.single_apply, ite_zero_mul_ite_zero]
  split_ifs with hp
  · rw [tsum_eq_single ⟨(m, n), mem_mulFiber.mpr hp.symm⟩ fun _ _ ↦ by grind]
    simp
  · exact (tsum_congr fun _ ↦ by grind).trans tsum_zero

end DiscreteConvolution
