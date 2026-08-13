/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Cont.Basic

/-!
# The adic spectrum `Spa (A, A⁺)`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.23.**

For a subring `A⁺` of a topological ring `A`, the adic spectrum is the set of continuous points
of `Spv A` that are sub-unit on `A⁺`:

```text
Spa (A, A⁺) = {v ∈ Cont A ; v(a) ≤ 1 for every a ∈ A⁺}.
```

Following the roadmap's conventions, the plus ring is an explicit `Subring A` argument and the
spectrum is a `Set (Spv A)`, so a point is a valuation up to equivalence with no chosen value
group, and the subspace topology is the one the coercion `↥(spa Aplus)` carries. (Mathlib's
in-flight `SpaPoint` of mathlib4#42315 instead bundles a representative valuation with a chosen
value group — the representation the roadmap warns must be compared before later layers may use
it; the subspace form here needs no such comparison.)

Nothing here asks `A⁺` to be a ring of integral elements or `A` to be a Huber ring. The
definition makes sense for any subring, and those hypotheses enter only where theorems need
them: spectrality (Wedhorn Theorem 7.35) is the first such theorem, and it lives with the
`Spv (A, I)` machinery it consumes, not in this file.

## Main definitions

* `TauCeti.ValuationSpectrum.spa` : the adic spectrum of `(A, A⁺)`, as a `Set (Spv A)`.

## Main results

* `TauCeti.ValuationSpectrum.mem_spa_iff` : membership is continuity plus the sub-unit
  condition on the plus ring.
* `TauCeti.ValuationSpectrum.spa_subset_cont` and `TauCeti.ValuationSpectrum.spa_antitone` :
  the spectrum sits inside `Cont A` and shrinks as the plus ring grows.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.23.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Wedhorn's `Spa (A, A⁺)`** (Definition 7.23): the continuous points of `Spv A` that are
sub-unit on the subring `A⁺`, as a `Set (Spv A)` — the subspace topology is the one the
coercion `↥(spa Aplus)` carries. The plus ring is an arbitrary subring: that it is a ring of
integral elements is a hypothesis of later theorems, not of the definition. -/
def spa (Aplus : Subring A) : Set (Spv A) :=
  cont A ∩ {v : Spv A | ∀ a ∈ Aplus, v.toValuativeRel.vle a 1}

@[simp]
theorem mem_spa_iff (Aplus : Subring A) (v : Spv A) :
    v ∈ spa Aplus ↔ v.IsContinuous ∧ ∀ a ∈ Aplus, v.toValuativeRel.vle a 1 := by
  rw [spa, Set.mem_inter_iff, mem_cont_iff, Set.mem_ofPred_eq]

/-- The adic spectrum sits inside the continuous locus. -/
theorem spa_subset_cont (Aplus : Subring A) : spa Aplus ⊆ cont A :=
  Set.inter_subset_left

/-- Enlarging the plus ring shrinks the adic spectrum. -/
theorem spa_antitone : Antitone (spa (A := A)) := fun _ _ hle ↦
  Set.inter_subset_inter_right _ fun _ hv a ha ↦ hv a (hle ha)

end TauCeti.ValuationSpectrum

end
