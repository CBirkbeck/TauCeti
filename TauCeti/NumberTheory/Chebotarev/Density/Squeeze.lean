/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Density.Ramification
public import TauCeti.NumberTheory.NumberField.DirichletDensityBounds
public import TauCeti.NumberTheory.Chebotarev.Density.ZetaSum

/-!
# Lower bounds on every Frobenius fibre are exact

Let `L / K` be a finite Galois extension of number fields. The Artin fibres partition the primes
outside the finite set `ramifiedPrimes K L`, so their density ratios add up to a quantity tending
to `1`. If each fibre is known only from *below*, by `d C`, and those lower bounds already sum to
`1`, then none of them has any room left: each fibre has Dirichlet density exactly `d C`.

This is the step that converts the one-sided estimates a crossing argument produces into density
statements. A crossing argument bounds a fibre below — it exhibits enough primes — and says
nothing from above; the upper bound comes for free from the *other* fibres' lower bounds, because
the total is pinned.

## Main results

* `NumberField.Chebotarev.isUpperDirichletDensityBound_frobeniusPrimeSet_of_forall_isLowerBound`:
  the complementary upper bound.
* `NumberField.Chebotarev.hasDirichletDensity_frobeniusPrimeSet_of_forall_isLowerBound`: matching
  bounds, hence the density.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
-/

public section

open Filter
open IsDedekindDomain (HeightOneSpectrum)
open scoped Topology
open NumberField

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

open scoped Classical in
variable (K L) in
/-- **The fibre ratio, read off from the others.** For `s > 1` every fibre series converges, so
the Artin fibres split the unramified sum exactly; dividing by the all-prime sum expresses one
fibre's density ratio as the unramified ratio minus the ratios of the remaining fibres. -/
private theorem primeIdealZetaSum_div_eq_sub_sum_erase {s : ℝ} (hs : 1 < s)
    (C₀ : ConjClasses (L ≃ₐ[K] L)) :
    (frobeniusPrimeSet K L C₀).primeIdealZetaSum s /
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s =
      ((↑(ramifiedPrimes K L) : Set (HeightOneSpectrum (𝓞 K)))ᶜ).primeIdealZetaSum s /
          (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s -
        ∑ C ∈ Finset.univ.erase C₀, (frobeniusPrimeSet K L C).primeIdealZetaSum s /
          (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s := by
  rw [← Finset.sum_div, ← sub_div, ← sum_primeIdealZetaSum_frobeniusPrimeSet K L
    fun C ↦ TauCeti.summable_absNorm_rpow_subtype_of_one_lt _ hs]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ C₀)]
  ring_nf

open scoped Classical in
variable (K L) in
/-- **Lower bounds on the other fibres bound this one from above.** The Artin fibres exhaust the
unramified primes, whose density is `1`, so a fibre's ratio is what the others leave behind. If
the lower bounds `d` sum to `1`, what they leave behind is `d C₀`. -/
theorem isUpperDirichletDensityBound_frobeniusPrimeSet_of_forall_isLowerBound
    {d : ConjClasses (L ≃ₐ[K] L) → ℝ}
    (hlow : ∀ C, (frobeniusPrimeSet K L C).IsLowerDirichletDensityBound (d C))
    (hsum : ∑ C : ConjClasses (L ≃ₐ[K] L), d C = 1) (C₀ : ConjClasses (L ≃ₐ[K] L)) :
    (frobeniusPrimeSet K L C₀).IsUpperDirichletDensityBound (d C₀) := by
  -- `IsUpperDirichletDensityBound` is a non-exposed `def`, so unfold it through its `Iff.rfl`
  -- restatement rather than by `intro`.
  refine Set.isUpperDirichletDensityBound_iff.mpr fun ε hε ↦ ?_
  have hcard : (0 : ℝ) < Fintype.card (ConjClasses (L ≃ₐ[K] L)) := by
    exact_mod_cast Fintype.card_pos
  set ε' : ℝ := ε / (2 * Fintype.card (ConjClasses (L ≃ₐ[K] L))) with hε'def
  have hε' : 0 < ε' := by positivity
  have hothers : ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ C ∈ Finset.univ.erase C₀,
      d C - ε' < (frobeniusPrimeSet K L C).primeIdealZetaSum s /
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s :=
    eventually_all_finset _ |>.2 fun C _ ↦
      Set.isLowerDirichletDensityBound_iff.mp (hlow C) ε' hε'
  have hcompl := Set.isUpperDirichletDensityBound_iff.mp
    (hasDirichletDensity_compl_ramifiedPrimes K L).isUpperDirichletDensityBound
    (ε / 2) (by positivity)
  filter_upwards [hothers, hcompl, self_mem_nhdsWithin] with s hs_oth hs_cpl (hs1 : 1 < s)
  rw [primeIdealZetaSum_div_eq_sub_sum_erase K L hs1 C₀]
  -- The erased sum is bounded below term by term, and `hsum` turns what is left into `d C₀`.
  have hlb : ∑ C ∈ Finset.univ.erase C₀, (d C - ε') ≤
      ∑ C ∈ Finset.univ.erase C₀, (frobeniusPrimeSet K L C).primeIdealZetaSum s /
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s :=
    Finset.sum_le_sum fun C hC ↦ (hs_oth C hC).le
  have herase : ∑ C ∈ Finset.univ.erase C₀, d C = 1 - d C₀ := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ C₀), hsum]
  have hhalf : (Fintype.card (ConjClasses (L ≃ₐ[K] L)) : ℝ) * ε' = ε / 2 := by
    rw [hε'def]; field_simp
  -- The erased sum loses at most `card * ε' = ε / 2` against `1 - d C₀`.
  have hsum_lb : 1 - d C₀ - ε / 2 ≤ ∑ C ∈ Finset.univ.erase C₀, (d C - ε') := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, herase]
    have hcard_le : ((Finset.univ.erase C₀).card : ℝ) * ε' ≤ ε / 2 := by
      rw [← hhalf]
      gcongr
      exact_mod_cast (Finset.card_erase_le).trans Finset.card_univ.le
    linarith
  linarith

open scoped Classical in
variable (K L) in
/-- **A lower bound on every Frobenius fibre is exact once the bounds sum to one.** Each Artin
fibre then has Dirichlet density equal to its lower bound.

This is how a density is finally extracted. A crossing argument produces only lower bounds — it
exhibits primes in a fibre and cannot see that there are no more — and the missing upper bound is
supplied by the other fibres, since together they leave exactly `d C₀` behind. -/
theorem hasDirichletDensity_frobeniusPrimeSet_of_forall_isLowerBound
    {d : ConjClasses (L ≃ₐ[K] L) → ℝ}
    (hlow : ∀ C, (frobeniusPrimeSet K L C).IsLowerDirichletDensityBound (d C))
    (hsum : ∑ C : ConjClasses (L ≃ₐ[K] L), d C = 1) (C₀ : ConjClasses (L ≃ₐ[K] L)) :
    (frobeniusPrimeSet K L C₀).HasDirichletDensity (d C₀) :=
  Set.hasDirichletDensity_of_upperBound_of_lowerBound
    (isUpperDirichletDensityBound_frobeniusPrimeSet_of_forall_isLowerBound K L hlow hsum C₀)
    (hlow C₀)

end NumberField.Chebotarev
