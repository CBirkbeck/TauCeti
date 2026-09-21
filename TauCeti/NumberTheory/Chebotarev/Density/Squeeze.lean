/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Basic
public import TauCeti.NumberTheory.Chebotarev.Density.Ramification

/-!
# Lower bounds on every Frobenius fibre are exact

Let `L / K` be a finite Galois extension of number fields. The Artin fibres partition the primes
outside the finite set `ramifiedPrimes K L`, whose density is `1`. If each fibre is known only
from *below*, by `d C`, and those lower bounds already sum to `1`, then none of them has any room
left: each fibre has Dirichlet density exactly `d C`.

This is the step that converts the one-sided estimates a crossing argument produces into density
statements. A crossing argument bounds a fibre below — it exhibits enough primes — and says
nothing from above; the upper bound comes for free from the *other* fibres' lower bounds, because
the total is pinned.

Both results here are specialisations of the generic finite-partition squeeze
`NumberField.Set.hasDirichletDensity_of_forall_isLowerDirichletDensityBound`, which holds for any
finite pairwise disjoint family of prime sets whose union has a known density. The only inputs
particular to this setting are the partition facts `pairwise_disjoint_frobeniusPrimeSet` and
`hasDirichletDensity_compl_ramifiedPrimes`.

## Main results

* `isUpperDirichletDensityBound_frobeniusPrimeSet_of_forall_isLowerDirichletDensityBound`:
  the complementary upper bound.
* `hasDirichletDensity_frobeniusPrimeSet_of_forall_isLowerDirichletDensityBound`: matching
  bounds, hence the density.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
* C. Birkbeck and R. Brasca, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/Abelian.lean`, whose
  `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` and `ratioSum_frobeniusFibres_tendsto_one`
  are the corresponding steps: the fibre-sum identity divided by the all-prime sum, and the
  `card ι * ε` budget that turns the other fibres' lower bounds into this one's upper bound.
-/

public section

open IsDedekindDomain (HeightOneSpectrum)
open NumberField

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

open scoped Classical in
variable (K L) in
/-- **The Artin fibres are a partition of density one.** They are pairwise disjoint and their
union is the complement of the ramified primes, which is cofinite and so has density `1`. This is
the sole Chebotarev-specific input to the squeeze below. -/
private theorem hasDirichletDensity_iUnion_frobeniusPrimeSet :
    Set.HasDirichletDensity
      (⋃ C ∈ (Finset.univ : Finset (ConjClasses (L ≃ₐ[K] L))), frobeniusPrimeSet K L C) 1 := by
  simpa using hasDirichletDensity_compl_ramifiedPrimes K L

open scoped Classical in
variable (K L) in
/-- **Lower bounds on the other fibres bound this one from above.** The Artin fibres exhaust the
unramified primes, whose density is `1`, so a fibre's ratio is what the others leave behind. If
the lower bounds `d` sum to `1`, what they leave behind is `d C₀`. -/
theorem isUpperDirichletDensityBound_frobeniusPrimeSet_of_forall_isLowerDirichletDensityBound
    {d : ConjClasses (L ≃ₐ[K] L) → ℝ}
    (hlow : ∀ C, (frobeniusPrimeSet K L C).IsLowerDirichletDensityBound (d C))
    (hsum : ∑ C : ConjClasses (L ≃ₐ[K] L), d C = 1) (C₀ : ConjClasses (L ≃ₐ[K] L)) :
    (frobeniusPrimeSet K L C₀).IsUpperDirichletDensityBound (d C₀) :=
  Set.isUpperDirichletDensityBound_of_forall_isLowerDirichletDensityBound (Finset.mem_univ C₀)
    ((pairwise_disjoint_frobeniusPrimeSet K L).set_pairwise _)
    (hasDirichletDensity_iUnion_frobeniusPrimeSet K L) (fun C _ ↦ hlow C) hsum

open scoped Classical in
variable (K L) in
/-- **A lower bound on every Frobenius fibre is exact once the bounds sum to one.** Each Artin
fibre then has Dirichlet density equal to its lower bound.

This is how a density is finally extracted. A crossing argument produces only lower bounds — it
exhibits primes in a fibre and cannot see that there are no more — and the missing upper bound is
supplied by the other fibres, since together they leave exactly `d C₀` behind. -/
theorem hasDirichletDensity_frobeniusPrimeSet_of_forall_isLowerDirichletDensityBound
    {d : ConjClasses (L ≃ₐ[K] L) → ℝ}
    (hlow : ∀ C, (frobeniusPrimeSet K L C).IsLowerDirichletDensityBound (d C))
    (hsum : ∑ C : ConjClasses (L ≃ₐ[K] L), d C = 1) (C₀ : ConjClasses (L ≃ₐ[K] L)) :
    (frobeniusPrimeSet K L C₀).HasDirichletDensity (d C₀) :=
  Set.hasDirichletDensity_of_forall_isLowerDirichletDensityBound (Finset.mem_univ C₀)
    ((pairwise_disjoint_frobeniusPrimeSet K L).set_pairwise _)
    (hasDirichletDensity_iUnion_frobeniusPrimeSet K L) (fun C _ ↦ hlow C) hsum

end NumberField.Chebotarev
