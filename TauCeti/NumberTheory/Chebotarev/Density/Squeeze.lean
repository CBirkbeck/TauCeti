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

* `isUpperDirichletDensityBound_frobeniusPrimeSet_of_forall_isLowerDirichletDensityBound`:
  the complementary upper bound.
* `hasDirichletDensity_frobeniusPrimeSet_of_forall_isLowerDirichletDensityBound`: matching
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
private theorem primeIdealZetaSum_frobeniusPrimeSet_div_univ_eq_sub_sum_erase {s : ℝ} (hs : 1 < s)
    (C₀ : ConjClasses (L ≃ₐ[K] L)) :
    (frobeniusPrimeSet K L C₀).primeIdealZetaSum s /
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s =
      ((↑(ramifiedPrimes K L) : Set (HeightOneSpectrum (𝓞 K)))ᶜ).primeIdealZetaSum s /
          (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s -
        ∑ C ∈ Finset.univ.erase C₀, (frobeniusPrimeSet K L C).primeIdealZetaSum s /
          (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s := by
  rw [← Finset.sum_div, ← sub_div, ← sum_primeIdealZetaSum_frobeniusPrimeSet K L
    fun C ↦ TauCeti.summable_absNorm_rpow_subtype_of_one_lt _ hs,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ C₀), add_sub_cancel_right]

omit [NumberField K] [NumberField L] [IsGalois K L] [Algebra K L] [Field L] [Field K] in
/-- **What a term-by-term lower bound leaves.** If `d` sums to `1` and every `a i` off `i₀` is
within `δ` below `d i`, the erased sum falls short of `1 - d i₀` by at most `card ι * δ`.

Pure arithmetic on a finite index type: no primes, no densities. It is what turns the other
fibres' lower bounds into an upper bound on the remaining one. -/
private theorem one_sub_sub_le_sum_erase_of_forall_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d a : ι → ℝ} {δ η : ℝ} (i₀ : ι) (hd : ∑ i, d i = 1)
    (ha : ∀ i ∈ Finset.univ.erase i₀, d i - δ ≤ a i) (hδ : 0 ≤ δ)
    (hη : (Fintype.card ι : ℝ) * δ ≤ η) :
    1 - d i₀ - η ≤ ∑ i ∈ Finset.univ.erase i₀, a i := by
  have hlb := Finset.sum_le_sum ha
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_erase_eq_sub (Finset.mem_univ i₀), hd] at hlb
  have hcard : ((Finset.univ.erase i₀).card : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Finset.card_univ (α := ι) ▸ Finset.card_erase_le
  linarith [(mul_le_mul_of_nonneg_right hcard hδ).trans hη]

open scoped Classical in
variable (K L) in
/-- **Every other fibre is eventually above its bound.** A finite conjunction of eventual
statements is eventually true, so all fibres but `C₀` clear `d C - ε'` simultaneously. -/
private theorem eventually_forall_mem_erase_sub_lt {d : ConjClasses (L ≃ₐ[K] L) → ℝ}
    (hlow : ∀ C, (frobeniusPrimeSet K L C).IsLowerDirichletDensityBound (d C))
    (C₀ : ConjClasses (L ≃ₐ[K] L)) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ C ∈ Finset.univ.erase C₀,
      d C - ε' < (frobeniusPrimeSet K L C).primeIdealZetaSum s /
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s :=
  eventually_all_finset _ |>.2 fun C _ ↦
    Set.isLowerDirichletDensityBound_iff.mp (hlow C) ε' hε'

open scoped Classical in
variable (K L) in
/-- **Lower bounds on the other fibres bound this one from above.** The Artin fibres exhaust the
unramified primes, whose density is `1`, so a fibre's ratio is what the others leave behind. If
the lower bounds `d` sum to `1`, what they leave behind is `d C₀`. -/
theorem isUpperDirichletDensityBound_frobeniusPrimeSet_of_forall_isLowerDirichletDensityBound
    {d : ConjClasses (L ≃ₐ[K] L) → ℝ}
    (hlow : ∀ C, (frobeniusPrimeSet K L C).IsLowerDirichletDensityBound (d C))
    (hsum : ∑ C : ConjClasses (L ≃ₐ[K] L), d C = 1) (C₀ : ConjClasses (L ≃ₐ[K] L)) :
    (frobeniusPrimeSet K L C₀).IsUpperDirichletDensityBound (d C₀) := by
  -- `IsUpperDirichletDensityBound` is a non-exposed `def`, so unfold it through its `Iff.rfl`
  -- restatement rather than by `intro`.
  refine Set.isUpperDirichletDensityBound_iff.mpr fun ε hε ↦ ?_
  obtain ⟨ε', hε', hhalf⟩ : ∃ ε' : ℝ, 0 < ε' ∧
      (Fintype.card (ConjClasses (L ≃ₐ[K] L)) : ℝ) * ε' = ε / 2 := by
    have hcard : (0 : ℝ) < Fintype.card (ConjClasses (L ≃ₐ[K] L)) := by
      exact_mod_cast Fintype.card_pos
    exact ⟨ε / (2 * Fintype.card (ConjClasses (L ≃ₐ[K] L))), by positivity, by field_simp⟩
  have hcompl := Set.isUpperDirichletDensityBound_iff.mp
    (hasDirichletDensity_compl_ramifiedPrimes K L).isUpperDirichletDensityBound
    (ε / 2) (by positivity)
  filter_upwards [eventually_forall_mem_erase_sub_lt K L hlow C₀ hε', hcompl,
    self_mem_nhdsWithin] with s hs_oth hs_cpl (hs1 : 1 < s)
  rw [primeIdealZetaSum_frobeniusPrimeSet_div_univ_eq_sub_sum_erase K L hs1 C₀]
  -- The unramified ratio costs `ε / 2`; the other fibres' lower bounds cost the other half.
  linarith [one_sub_sub_le_sum_erase_of_forall_sub_le C₀ hsum
    (fun C hC ↦ (hs_oth C hC).le) hε'.le hhalf.le]

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
  Set.hasDirichletDensity_of_upperBound_of_lowerBound
    (isUpperDirichletDensityBound_frobeniusPrimeSet_of_forall_isLowerDirichletDensityBound
      K L hlow hsum C₀)
    (hlow C₀)

end NumberField.Chebotarev
