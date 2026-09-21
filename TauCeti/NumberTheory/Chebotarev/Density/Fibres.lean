/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible
public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet

/-!
# The Frobenius fibres carry all of the density

Let `L / K` be a finite Galois extension of number fields. The Artin class partitions the primes
of `𝓞 K` outside the finite set `ramifiedPrimes K L` into the fibres `frobeniusPrimeSet K L C`,
one for each conjugacy class `C` of `Gal(L/K)`. This file records the consequence for Dirichlet
density: if every fibre has a density, those densities sum to `1`.

Nothing here is an analytic argument. The partition is finite and pairwise disjoint, so density is
additive along it by `NumberField.Set.hasDirichletDensity_biUnion_finset`; the primes it omits are
the ramified ones, of which there are finitely many, so they carry density `0` and their
complement carries density `1`. Uniqueness of density then equates the two descriptions of the
same set.

This is the statement a Chebotarev density theorem has to refine. It says the fibres exhaust the
primes, so no density leaks away; it says nothing about how the total is distributed between the
classes, which is exactly the content of Chebotarev and is not proved here.

## Main results

* `NumberField.Chebotarev.hasDirichletDensity_compl_ramifiedPrimes`: the primes unramified in `L`
  have Dirichlet density `1`.
* `NumberField.Chebotarev.sum_eq_one_of_hasDirichletDensity_frobeniusPrimeSet`: if every Artin
  fibre has a Dirichlet density, the densities sum to `1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

public section

open IsDedekindDomain (HeightOneSpectrum)

-- `primeIdealZetaSum` and `HasDirichletDensity` live in `NumberField.Set`, so dot notation on a
-- set of primes finds them only while `NumberField` is open.
open NumberField

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

omit [IsGalois K L] in
variable (K L) in
/-- **The unramified primes have density one.** Only finitely many primes of `𝓞 K` ramify in
`L`, so they carry density `0` and their complement carries all of it. -/
theorem hasDirichletDensity_compl_ramifiedPrimes :
    ((↑(ramifiedPrimes K L) : Set (HeightOneSpectrum (𝓞 K)))ᶜ).HasDirichletDensity 1 := by
  simpa using (Set.hasDirichletDensity_of_finite
    (ramifiedPrimes K L).finite_toSet).compl

open scoped Classical in
variable (K L) in
/-- **The Artin fibres carry all of the density.** If every `frobeniusPrimeSet K L C` has a
Dirichlet density, those densities sum to `1`: the fibres partition the unramified primes, and
the ramified ones are finite, hence negligible.

The hypothesis is that each density *exists*; that is genuinely an assumption here, and supplying
it for every class is the work of a Chebotarev density theorem. What this rules out is density
leaking away from the partition. -/
theorem sum_eq_one_of_hasDirichletDensity_frobeniusPrimeSet
    {d : ConjClasses (L ≃ₐ[K] L) → ℝ}
    (hd : ∀ C, (frobeniusPrimeSet K L C).HasDirichletDensity (d C)) :
    ∑ C : ConjClasses (L ≃ₐ[K] L), d C = 1 := by
  have hcov : (↑(ramifiedPrimes K L) : Set (HeightOneSpectrum (𝓞 K)))ᶜ =
      ⋃ C ∈ (Finset.univ : Finset (ConjClasses (L ≃ₐ[K] L))), frobeniusPrimeSet K L C := by simp
  have hbi := Set.hasDirichletDensity_biUnion_finset (s := Finset.univ)
    (f := fun C ↦ frobeniusPrimeSet K L C) (d := d) (fun C _ ↦ hd C)
    ((pairwise_disjoint_frobeniusPrimeSet K L).set_pairwise _)
  exact (hcov ▸ hasDirichletDensity_compl_ramifiedPrimes K L).unique hbi |>.symm

end NumberField.Chebotarev
