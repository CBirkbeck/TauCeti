/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Finite sums of functions vanishing or bounded along a filter

Mathlib's `Filter.ZeroAtFilter` and `Filter.BoundedAtFilter` are closed under binary sums
(`Filter.ZeroAtFilter.add`, `Filter.BoundedAtFilter.add`), and the bounded functions are closed
under a `Finset.prod` (`Filter.BoundedAtFilter.prod`, via `boundedFilterSubalgebra`). The additive
counterpart of that product lemma is not recorded upstream; this file adds it for both predicates.

The gap shows up wherever an operator is a finite sum of slashes: proving that such an operator
stays bounded, or stays vanishing, along `atImInfty` is an induction over the summands, and
without these each call site reruns it.

## Main results

* `Filter.ZeroAtFilter.sum`: a finite sum of functions vanishing along `l` vanishes along `l`.
* `Filter.BoundedAtFilter.sum`: a finite sum of functions bounded along `l` is bounded along `l`.
-/

public section

open Finset

namespace Filter

variable {α β ι : Type*} {l : Filter α} {s : Finset ι} {f : ι → α → β}

/-- **A finite sum of functions vanishing along `l` vanishes along `l`.** This is the additive
companion of `Filter.BoundedAtFilter.prod`, and it is `zeroAtFilterAddSubmonoid`'s closure under
`Finset.sum`. It needs `AddCommMonoid` rather than the submonoid's `AddZeroClass`, since that is
what `Finset.sum` itself requires. -/
theorem ZeroAtFilter.sum [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
    (h : ∀ i ∈ s, ZeroAtFilter l (f i)) : ZeroAtFilter l (∑ i ∈ s, f i) :=
  sum_mem (S := zeroAtFilterAddSubmonoid l) h

/-- **A finite sum of functions bounded along `l` is bounded along `l`** — the additive companion
of `Filter.BoundedAtFilter.prod`. -/
theorem BoundedAtFilter.sum [SeminormedAddCommGroup β]
    (h : ∀ i ∈ s, BoundedAtFilter l (f i)) : BoundedAtFilter l (∑ i ∈ s, f i) :=
  Finset.sum_induction f (BoundedAtFilter l) (fun _ _ ↦ BoundedAtFilter.add)
    (const_boundedAtFilter l 0) h

end Filter

end
