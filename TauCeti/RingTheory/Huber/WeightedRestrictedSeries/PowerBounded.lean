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

Both statements are about the *trivial* weight family `Tᵢ = {1}`, the one at which
`TauCeti.Huber.weightedRestrictedSubring` is the ordinary ring of restricted power series. At a
general weight family neither holds: the topology is then cut out by
`TauCeti.Huber.weightMul`, and multiplying a coefficient at `ν` by `Xᵢⁿ` moves it to `ν + n · eᵢ`,
where the weight is `Tν · Tᵢⁿ` rather than `Tν`. It is exactly
`TauCeti.Huber.weightMul_one_weight` — the trivial family's weights are all the ambient subgroup —
that makes the basic neighbourhoods shift-invariant, and both proofs below turn on it.

## Main results

* `TauCeti.Huber.isPowerBounded_weightedX`: the variable `Xᵢ` is power-bounded.
* `TauCeti.Huber.isPowerBounded_weightedC`: the constant `a` is power-bounded in `A⟨X⟩` as soon as
  it is power-bounded in `A`.

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

/-- **A power-bounded constant stays power-bounded.** The `n`-th power of the constant series `a`
multiplies every coefficient by `aⁿ`, so a neighbourhood absorbing all the `aⁿ` in `A` absorbs
all the powers of the constant series at once.

Continuity of `TauCeti.Huber.weightedC` would not give this: continuous ring homomorphisms do not
preserve power-boundedness in general. -/
theorem isPowerBounded_weightedC {a : A} (ha : IsPowerBounded a) :
    IsPowerBounded (weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight a) := by
  refine isPowerBounded_iff.mpr <| isBounded_iff.mpr fun U hU ↦ ?_
  have hbasis := hasBasis_nhds_zero_weightedTopology (isWeightFamily_one_weight (k := k) (A := A))
  obtain ⟨W, -, hWU⟩ := hbasis.mem_iff.mp hU
  obtain ⟨V, hV, hVW⟩ :=
    isBounded_iff.mp (isPowerBounded_iff.mp ha) (W : Set A) (W.isOpen.mem_nhds W.zero_mem)
  obtain ⟨V', hV'⟩ := NonarchimedeanRing.is_nonarchimedean V hV
  refine ⟨_, hbasis.mem_of_mem (i := V') trivial, ?_⟩
  rintro _ ⟨g, hg, _, ⟨n, rfl⟩, rfl⟩
  refine hWU ?_
  simp only [SetLike.mem_coe, mem_weightedNhd, weightMul_one_weight] at hg ⊢
  intro ν
  push_cast [coe_weightedC, ← map_pow, MvPowerSeries.coeff_mul_C]
  exact hVW ⟨_, hV' (hg ν), _, ⟨n, rfl⟩, rfl⟩

end TauCeti.Huber

end
