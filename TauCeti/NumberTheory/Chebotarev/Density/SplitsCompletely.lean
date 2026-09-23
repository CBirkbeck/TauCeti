/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Contraction
public import TauCeti.NumberTheory.Chebotarev.SplitsCompletely

/-!
# The completely split primes have density `1 / [L : K]`

Let `L / K` be a finite Galois extension of number fields. The primes of `𝓞 K` that split
completely in `L` — the identity fibre `frobeniusPrimeSet K L 1` of the Artin class — have
Dirichlet density `1 / [L : K]`.

## Main results

* `NumberField.Chebotarev.hasDirichletDensity_frobeniusPrimeSet_one`: the completely split primes
  have Dirichlet density `1 / [L : K]`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.
-/

public section

open IsDedekindDomain (HeightOneSpectrum)

open NumberField

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

variable (K L) in
/-- **The completely split primes have density `1 / [L : K]`.** The primes of `𝓞 K` that split
completely in the finite Galois extension `L` have Dirichlet density `1 / [L : K]`. -/
theorem hasDirichletDensity_frobeniusPrimeSet_one :
    (frobeniusPrimeSet K L 1).HasDirichletDensity (1 / Module.finrank K L) := by
  have hunder (𝔓 : HeightOneSpectrum (𝓞 L)) :
      𝔓.asIdeal.LiesOver (𝔓.under (𝓞 K)).asIdeal :=
    ⟨HeightOneSpectrum.under_asIdeal _ 𝔓⟩
  -- Contract all the primes of `𝓞 L`, which have density one: away from the ramified primes, a
  -- prime of residue degree one over `K` lies over a completely split prime, and each completely
  -- split prime has `[L : K]` primes above it.
  refine (Set.hasDirichletDensity_contraction (T := (Set.univ : Set (HeightOneSpectrum (𝓞 L))))
    (Set.hasDirichletDensity_of_finite (K := K) (ramifiedPrimes K L).finite_toSet)
    (fun 𝔓 _ hdeg hram ↦ ?_) Module.finrank_pos.ne' fun 𝔭 h𝔭 ↦ ?_).mp
      Set.hasDirichletDensity_univ
  · rw [Finset.mem_coe, mem_ramifiedPrimes_iff, not_not] at hram
    exact (mem_frobeniusPrimeSet_one_iff_inertiaDeg_eq_one hram 𝔓.asIdeal).mpr hdeg
  · -- Over a completely split prime every prime above has residue degree one, and there are
    -- `[L : K]` of them.
    have hdiv (𝔓 : HeightOneSpectrum (𝓞 L)) :
        (𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓 ∈ Set.univ ∧ 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1) ↔
          𝔓.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔭.asIdeal := by
      rw [← Ideal.liesOver_iff_dvd_map 𝔓.isPrime.ne_top]
      refine ⟨fun h ↦ ⟨(congrArg HeightOneSpectrum.asIdeal h.1).symm⟩, fun h ↦ ?_⟩
      have h𝔓 : 𝔓.under (𝓞 K) = 𝔭 := HeightOneSpectrum.ext h.over.symm
      subst h𝔓
      exact ⟨rfl, trivial, inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one h𝔭.1 𝔓.asIdeal⟩
    rw [Nat.card_congr ((Equiv.subtypeEquivRight hdiv).trans
      (HeightOneSpectrum.equivPrimesOver (𝓞 L) 𝔭.ne_bot)), Nat.card_coe_set_eq]
    exact mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank.mp h𝔭.1

end NumberField.Chebotarev
