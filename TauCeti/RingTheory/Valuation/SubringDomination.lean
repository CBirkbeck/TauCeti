/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Domination between valuation subrings forces equivalence

A valuation of a field is determined by its valuation subring, so `v.IsEquiv w` is the same as
`𝒪_v = 𝒪_w` (`Valuation.isEquiv_iff_valuationSubring`). This file records that for the
*domination* order only **one** inclusion has to be checked: `𝒪_v ≤ 𝒪_w` already forces
`𝒪_v = 𝒪_w`, because valuation subrings are maximal for domination
(`ValuationSubring.isMax_toLocalSubring`, Stacks 052K).

The order in play is the one on `LocalSubring`, which is domination rather than mere inclusion:
`A ≤ B` there means `A ≤ B` as subrings *and* that `Subring.inclusion` is a local homomorphism.
Plain inclusion is not enough — a valuation subring has many larger valuation subrings, obtained
by coarsening, and those are not equivalent to it. What rules them out is exactly the local-hom
half of domination, which is why the hypothesis is stated on `toLocalSubring`.

## Main results

* `Valuation.isEquiv_of_toLocalSubring_le` : if `𝒪_v` dominates downward into `𝒪_w`, then
  `v.IsEquiv w`.

## References

* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/hasse-weil`, commit
  `513e83879e2f8cbc626eb9e04d660e92be16ccba`,
  `projects/HasseWeil/HasseWeil/Curves/RankOneDomination.lean`. The proof is that file's.
-/

public section

/-- **A one-sided domination between valuation subrings already gives equivalence.** If
`𝒪_v ≤ 𝒪_w` in the domination order on local subrings then `v.IsEquiv w`; the reverse inclusion,
which one might expect to have to prove, is free, because valuation subrings are maximal for
domination (`ValuationSubring.isMax_toLocalSubring`).

The two valuations may take values in different groups: equivalence of valuations is a relation
between valuations with unrelated value groups, and so is the conclusion here. -/
theorem Valuation.isEquiv_of_toLocalSubring_le {F : Type*} [Field F] {Γ₁ Γ₂ : Type*}
    [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂]
    (v : Valuation F Γ₁) (w : Valuation F Γ₂)
    (hle : v.valuationSubring.toLocalSubring ≤ w.valuationSubring.toLocalSubring) :
    v.IsEquiv w := by
  have heq : v.valuationSubring.toLocalSubring = w.valuationSubring.toLocalSubring :=
    (v.valuationSubring.isMax_toLocalSubring).eq_of_le hle
  rw [Valuation.isEquiv_iff_valuationSubring]
  exact ValuationSubring.toLocalSubring_injective heq

end
