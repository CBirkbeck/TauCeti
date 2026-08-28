/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Valuation subrings under domination and inclusion

Two facts about how a valuation of a field is pinned down by its valuation subring.

The first is that a *one-sided* domination already forces equivalence: valuation subrings are
maximal for the domination order on local subrings, so `𝒪_v ≤ 𝒪_w` collapses to `𝒪_v = 𝒪_w`, and
equivalence follows. The reverse inclusion, which one might expect to have to prove, is free.

The second is the rank-one rigidity behind that: a valuation subring which is a discrete valuation
ring has no proper overrings other than the whole field, because its overrings correspond to its
primes and a DVR has only `⊥` and its maximal ideal.

## Main results

* `Valuation.isEquiv_of_valuationSubring_le` : `𝒪_v ≤ 𝒪_w` in the domination order implies
  `v.IsEquiv w`.
* `rankOne_valuationSubring_le_eq_of_ne_top` : a valuation subring that is a DVR is equal to any
  larger valuation subring other than `⊤`.

## References

* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/hasse-weil`, commit
  `513e83879e2f8cbc626eb9e04d660e92be16ccba`,
  `projects/HasseWeil/HasseWeil/Curves/RankOneDomination.lean`. The proofs are that file's.
-/

public section

open ValuationSubring

/-- If the valuation subring of `v` dominates downward into that of `w`, then `v` and `w` are
equivalent. Only one inclusion is needed: valuation subrings are maximal for the domination order
(`ValuationSubring.isMax_toLocalSubring`), so `𝒪_v ≤ 𝒪_w` already forces equality. -/
theorem Valuation.isEquiv_of_valuationSubring_le {F : Type*} [Field F] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v w : Valuation F Γ₀)
    (hle : v.valuationSubring.toLocalSubring ≤ w.valuationSubring.toLocalSubring) :
    v.IsEquiv w := by
  have heq : v.valuationSubring.toLocalSubring = w.valuationSubring.toLocalSubring :=
    (v.valuationSubring.isMax_toLocalSubring).eq_of_le hle
  rw [Valuation.isEquiv_iff_valuationSubring]
  exact ValuationSubring.toLocalSubring_injective heq

/-- A valuation subring `A` of a field which is a discrete valuation ring is equal to every larger
valuation subring `B` except `⊤`.

Overrings of `A` correspond to its primes, by `B ↦ A.idealOfLE B`, with
`ValuationSubring.ofPrime_idealOfLE` reconstructing `B`. A DVR has exactly two primes, so
`A.idealOfLE B` is `⊥` — giving `B = ⊤`, excluded — or the maximal ideal, giving `B = A`.

The transport of `ofPrime` along an equality of primes is routed through
`ValuationSubring.primeSpectrumEquiv` rather than `rw`, because `ofPrime` takes an `IsPrime`
instance argument and rewriting under it is not type correct; `PrimeSpectrum` bundles the
instance and so avoids the issue. -/
theorem rankOne_valuationSubring_le_eq_of_ne_top {L : Type*} [Field L] (A B : ValuationSubring L)
    [IsDiscreteValuationRing A] (hAB : A ≤ B) (hB : B ≠ ⊤) : A = B := by
  classical
  have hPprime : (A.idealOfLE B hAB).IsPrime := ValuationSubring.prime_idealOfLE A B hAB
  have transport : ∀ (C : ValuationSubring L) (hC : A ≤ C),
      A.idealOfLE B hAB = A.idealOfLE C hC → B = C := by
    intro C hC hEq
    have hPS : (⟨A.idealOfLE B hAB, hPprime⟩ : PrimeSpectrum A)
        = ⟨A.idealOfLE C hC, ValuationSubring.prime_idealOfLE A C hC⟩ :=
      PrimeSpectrum.ext hEq
    have hval := congrArg (fun P ↦ ((ValuationSubring.primeSpectrumEquiv A) P).1) hPS
    simpa only [ValuationSubring.primeSpectrumEquiv_apply, ValuationSubring.ofPrime_idealOfLE]
      using hval
  rcases eq_or_ne (A.idealOfLE B hAB) ⊥ with hbot | hne
  · exfalso
    apply hB
    refine transport ⊤ le_top ?_
    rw [hbot, ValuationSubring.idealOfLE, IsLocalRing.maximalIdeal_eq_bot]
    refine (Ideal.comap_bot_of_injective (ValuationSubring.inclusion A ⊤ le_top) ?_).symm
    intro a b hab
    have hab' := congrArg (Subtype.val (p := fun y ↦ y ∈ (⊤ : ValuationSubring L))) hab
    rw [ValuationSubring.inclusion, Subring.coe_inclusion, Subring.coe_inclusion] at hab'
    exact Subtype.ext hab'
  · have hmax : (A.idealOfLE B hAB).IsMaximal := hPprime.isMaximal hne
    refine (transport A le_rfl ?_).symm
    rw [IsLocalRing.eq_maximalIdeal hmax, ValuationSubring.idealOfLE]
    ext x
    have hx : (ValuationSubring.inclusion A A le_rfl) x = x :=
      Subtype.ext (by rw [ValuationSubring.inclusion, Subring.coe_inclusion])
    rw [Ideal.mem_comap, hx]

end
