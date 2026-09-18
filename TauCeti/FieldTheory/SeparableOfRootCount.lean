/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
-- The closure hypothesis is in the statement: an algebraically closed field splits every
-- polynomial, which is what makes the number of roots with multiplicity the degree.
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# A polynomial that attains its degree in distinct roots is separable

Over a field where `p` splits it has exactly `natDegree p` roots counted with multiplicity, so it
can have that many *distinct* roots only if none of them repeats — which is separability.

Mathlib has the equivalence as `Polynomial.card_rootSet_eq_natDegree_iff_of_splits`, phrased with
`rootSet` and an equality. A counting argument produces neither of those: it produces a lower bound
on the number of roots in the field itself, the matching upper bound being automatic from
`card_roots'`. This is that form, and it is the shape every root-counting proof of separability
ends in.

## Main results

* `Polynomial.separable_of_natDegree_le_card_roots`: a polynomial with at least as many distinct
  roots as its degree is separable.
-/

public section

namespace Polynomial

open Finset

/-- **A polynomial with at least as many distinct roots as its degree is separable**, over an
algebraically closed field. The hypothesis is a lower bound because that is what a counting
argument gives; the reverse inequality always holds, so the two together are the equality
`card_rootSet_eq_natDegree_iff_of_splits` characterises separability by. -/
theorem separable_of_natDegree_le_card_roots {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    {p : F[X]} (hp : p ≠ 0) (h : p.natDegree ≤ #p.roots.toFinset) : p.Separable := by
  rw [← card_rootSet_eq_natDegree_iff_of_splits (K := F) hp (by simpa using IsAlgClosed.splits p)]
  have hrs : Fintype.card (p.rootSet F) = #p.roots.toFinset := by
    simp [rootSet_def, aroots_def, Algebra.algebraMap_self]
  rw [hrs]
  refine le_antisymm ?_ h
  have hmul := p.card_roots'
  have hdistinct := Multiset.toFinset_card_le p.roots
  omega

end Polynomial

end
