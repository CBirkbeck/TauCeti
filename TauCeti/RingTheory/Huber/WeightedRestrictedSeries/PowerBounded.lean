/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.PowerBounded
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic

/-!
# Power-bounded elements of `A⟨X₁, …, Xₖ⟩`

The variables `Xᵢ` and the power-bounded constants are power-bounded in the restricted
power-series ring. Together they say that `A°[X₁, …, Xₖ]` lands in `A⟨X₁, …, Xₖ⟩°`, which is what
makes `A°` the plus ring of the closed polydisc.

The two differ in how much of the weighted setting they need, and the difference is exactly
whether the coefficient moves.

Multiplying by a *constant* leaves every coefficient where it is, so the weight at `ν` is still
`Tν`; a neighbourhood of `A` absorbing the powers of `a` therefore absorbs them coefficientwise,
and `TauCeti.Huber.isPowerBounded_weightedC` holds for **every** weight family.

Multiplying by `Xᵢⁿ` moves the coefficient at `ν` to `ν + n · eᵢ`, where the weight is `Tν · Tᵢⁿ`
rather than `Tν`, and nothing in `TauCeti.Huber.IsWeightFamily` makes those comparable. So
`TauCeti.Huber.isPowerBounded_weightedX` is stated at the trivial family `Tᵢ = {1}` — the one at
which `TauCeti.Huber.weightedRestrictedSubring` is the ordinary ring of restricted power series —
where `TauCeti.Huber.weightMul_one_weight` says every weight is the ambient subgroup and the basic
neighbourhoods are shift-invariant.

## Main results

* `TauCeti.Huber.isPowerBounded_weightedX`: the variable `Xᵢ` is power-bounded.
* `TauCeti.Huber.isPowerBounded_weightedC`: the constant `a` is power-bounded in `A⟨X⟩_T`, for any
  weight family, as soon as it is power-bounded in `A`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.56 and
  Example 7.57.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08` records the power-boundedness of `Xᵢ` in
`projects/AdicSpaces/Adic spaces/Wedhorn828.lean`, but reaches it another way: there `Xᵢ` is
power-bounded because it lies in a *ring of definition* of the series ring, whose elements are
power-bounded because it is bounded. That route needs `A` to be Huber — a general nonarchimedean
ring has no ring of definition to appeal to — so it does not prove the statement in the generality
used here, and nothing was ported. The absorption argument below is direct and assumes only the
nonarchimedean topology. Were the Huber case all that were wanted,
`TauCeti.Huber.IsBounded.isPowerBounded_of_mem` is the TauCeti lemma that route would use.
-/

public section

namespace TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **The variable `Xᵢ` is power-bounded.** Multiplying by `Xᵢⁿ` only shifts coefficients, and at
the trivial weight family every basic neighbourhood asks the same of each coefficient, so one
neighbourhood absorbs every power at once.

This is what puts the coordinates of the closed polydisc in its plus ring `A⟨T⟩°`. -/
theorem isPowerBounded_weightedX (i : Fin k) :
    IsPowerBounded (weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i) := by
  refine isPowerBounded_iff.mpr <| isBounded_iff.mpr fun U hU ↦ ?_
  have hbasis := hasBasis_nhds_zero_weightedTopology (isWeightFamily_one_weight (k := k) (A := A))
  obtain ⟨W, -, hWU⟩ := hbasis.mem_iff.mp hU
  refine ⟨_, hbasis.mem_of_mem (i := W) trivial, ?_⟩
  rintro _ ⟨g, hg, _, ⟨n, rfl⟩, rfl⟩
  refine hWU ?_
  simp only [SetLike.mem_coe, mem_weightedNhd, weightMul_one_weight] at hg ⊢
  intro ν
  push_cast [coe_weightedX, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_mul_monomial]
  split <;> simp [hg]

/-- **A power-bounded constant stays power-bounded**, at any weight family. The `n`-th power of
the constant series `a` multiplies every coefficient by `aⁿ` and moves none of them, so the weight
at each `ν` is unchanged and a neighbourhood of `A` absorbing all the `aⁿ` absorbs the whole
family at once.

Continuity of `TauCeti.Huber.weightedC` would not give this: continuous ring homomorphisms do not
preserve power-boundedness in general. Contrast `TauCeti.Huber.isPowerBounded_weightedX`, which
does need the trivial weight family. -/
theorem isPowerBounded_weightedC {T : Fin k → Set A} (hT : IsWeightFamily T) {a : A}
    (ha : IsPowerBounded a) : IsPowerBounded (weightedC T hT a) := by
  refine isPowerBounded_iff.mpr <| isBounded_iff.mpr fun U hU ↦ ?_
  have hbasis := hasBasis_nhds_zero_weightedTopology hT
  obtain ⟨W, -, hWU⟩ := hbasis.mem_iff.mp hU
  obtain ⟨V, hV, hVW⟩ :=
    isBounded_iff.mp (isPowerBounded_iff.mp ha) (W : Set A) (W.isOpen.mem_nhds W.zero_mem)
  obtain ⟨V', hV'⟩ := NonarchimedeanRing.is_nonarchimedean V hV
  refine ⟨_, hbasis.mem_of_mem (i := V') trivial, ?_⟩
  rintro _ ⟨g, hg, _, ⟨n, rfl⟩, rfl⟩
  refine hWU ?_
  simp only [SetLike.mem_coe, mem_weightedNhd] at hg ⊢
  intro ν
  have hcoe : MvPowerSeries.coeff ν
      ((g * weightedC T hT a ^ n : weightedRestrictedSubring T hT) : MvPowerSeries (Fin k) A)
      = MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) A) * a ^ n := by
    push_cast [coe_weightedC, ← map_pow, MvPowerSeries.coeff_mul_C]
    rfl
  rw [hcoe, mul_comm]
  refine mul_mem_of_forall_mul_mul_mem (fun t ht u hu ↦ ?_) (hg ν)
  have huW : u * a ^ n ∈ W.toAddSubgroup := hVW ⟨u, hV' hu, _, ⟨n, rfl⟩, rfl⟩
  have hassoc : a ^ n * (t * u) = t * (u * a ^ n) := by ring
  rw [hassoc]
  exact mul_mem_weightMul T ν _ ht huW

end TauCeti.Huber

end
