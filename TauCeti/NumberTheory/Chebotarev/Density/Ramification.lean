/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible
public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet

/-!
# The unramified primes carry all of the density

Let `L / K` be an extension of number fields. The primes of `𝓞 K` ramified in `L` form the finite
set `ramifiedPrimes K L`, so their complement has Dirichlet density `1`.

For a Galois extension the Frobenius fibres partition that complement, so once every fibre is
known to have a density, those densities sum to `1`. That total is what pins the individual
values down: a lower bound of `1 / #G` on each of the `#G` fibres of an abelian extension can only
be an equality, which is how the density of a single fibre is finally extracted.

## Main results

* `NumberField.Chebotarev.hasDirichletDensity_compl_ramifiedPrimes`: the primes outside the finite
  ramified set have Dirichlet density `1`.
* `NumberField.Chebotarev.sum_dirichletDensity_frobeniusPrimeSet`: densities assigned to the
  Frobenius fibres sum to `1`.

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
/-- **The Frobenius fibres carry all of the density.** If every Artin fibre
`frobeniusPrimeSet K L C` has a Dirichlet density `d C`, then those densities sum to `1`.

That each fibre *has* a density is not automatic; supplying it is the analytic content of a
Chebotarev theorem, and what this records is the constraint linking the fibres to each other. -/
theorem sum_dirichletDensity_frobeniusPrimeSet {d : ConjClasses (L ≃ₐ[K] L) → ℝ}
    (hd : ∀ C, (frobeniusPrimeSet K L C).HasDirichletDensity (d C)) :
    ∑ C : ConjClasses (L ≃ₐ[K] L), d C = 1 :=
  -- the fibres are pairwise disjoint, and they cover exactly the complement of the finite set
  -- `ramifiedPrimes K L`, which carries all of the density
  (Set.hasDirichletDensity_biUnion_finset (fun C _ ↦ hd C)
    ((pairwise_disjoint_frobeniusPrimeSet K L).set_pairwise _)).unique <| by
    simpa using hasDirichletDensity_compl_ramifiedPrimes K L

end NumberField.Chebotarev
