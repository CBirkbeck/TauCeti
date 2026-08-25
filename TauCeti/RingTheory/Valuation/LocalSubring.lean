/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# A valuation subring that separates a point and is small on a prescribed ideal

Stacks 090P, in Mathlib as `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`,
separates a point from a subring integrally closed in a field: for `R ≤ K` with `K` a field and
`z ∉ R`, some valuation subring `V ⊇ R` still misses `z`. Independently,
`Ideal.image_subset_nonunits_valuationSubring` puts a prescribed proper ideal `J` of `R` inside
the non-units of some valuation subring containing `R`. **Neither gives both at once**, and the
valuative criterion for integrality by *continuous* valuations needs both of a single `V`:
missing `z` is what refutes integrality, while `J` landing strictly below `1` is what makes the
induced valuation continuous when `J` is an ideal of definition.

## The hypothesis that combines them

Both conclusions can be read off one maximal ideal `𝔪` of `R`: the point is separated when `𝔪`
contains every denominator of `z` — the `s ∈ R` with `s • z ∈ R`, which are Mathlib's colon
ideal `(1 : Submodule R K).colon {z}` — and `J` lands below `1` when `𝔪` contains `J`. So it is
enough that the denominators and `J` sit inside a common proper ideal, and the form this takes
in practice is that a *power* of `J` consists of denominators: `𝔪` is chosen over the
denominators, and primality pulls `J` itself into it.

An ideal of definition supplies exactly that. Multiplication by `z` is continuous and the powers
of an ideal of definition are a neighbourhood basis of `0`, so some power of it multiplies `z`
back into any given open subring. That step is topological and is left to the caller, which is
why this file states an algebraic hypothesis and sits beside the Mathlib lemma it refines.

## Main results

* `Subring.exists_le_valuationSubring_notMem_valuation_lt_one` : the combined statement.
* `LocalSubring.isIntegrallyClosedIn_ofPrime` : localising at a prime preserves integral
  closedness in `K`, which is what lets Stacks 090P part (2) apply to the local subring built
  in that proof.
* `LocalSubring.notMem_ofPrime_of_colon_le` : a point whose denominators all lie in `𝔪` is
  still missing from the localisation at `𝔪`.

## References

* [The Stacks Project](https://stacks.math.columbia.edu/tag/090P), Tag 090P.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.18, whose proof
  is given there as the citation [Hu2, Lemma 3.3].

## Provenance

Adapted from [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch
`dev/adic-spaces`, commit `37bbdaeb9`, `projects/AdicSpaces/Adic spaces/Presheaf.lean`,
declarations `conductorIdeal`, `conductorIdeal_ne_top`, `notMem_ofPrime_of_conductor_le`,
`isIntegrallyClosedIn_ofPrime` and `exists_valuationSubring_of_notMem_integralClosure`, where
this argument is carried out. **Adapted, not copied.** That development states the result for a
topological ring with a pair of definition, with `R` the integral closure of an open subring in
a fraction field, and defines its own `conductorIdeal`; here the statement is purely algebraic —
an arbitrary subring integrally closed in `K`, an arbitrary ideal, and the explicit hypothesis
that a power of it multiplies `z` back in — and the denominators are Mathlib's `Submodule.colon`
rather than a new definition.
-/

public section

variable {K : Type*} [Field K]

namespace LocalSubring

/-- **Localising at a prime preserves integral closedness in `K`.** If `x : K` is integral over
`R` localised at `𝔪`, clearing denominators makes `m • x` integral over `R` itself for some
`m ∉ 𝔪`; closedness of `R` puts `m • x` in `R`, and `m` is a unit downstairs. -/
theorem isIntegrallyClosedIn_ofPrime (R : Subring K) [IsIntegrallyClosedIn R K]
    (𝔪 : Ideal R) [𝔪.IsPrime] :
    IsIntegrallyClosedIn (LocalSubring.ofPrime R 𝔪).toSubring K := by
  set L := (LocalSubring.ofPrime R 𝔪).toSubring
  rw [Subring.isIntegrallyClosedIn_iff]
  intro x hx
  obtain ⟨⟨m, hm⟩, hmx⟩ := hx.exists_multiple_integral_of_isLocalization 𝔪.primeCompl x
  have hmx_R : m • x ∈ R := Subring.isIntegrallyClosedIn_iff.mp inferInstance hmx
  have hmx_L : m • x ∈ L := LocalSubring.le_ofPrime R 𝔪 hmx_R
  -- `m` is a unit downstairs, so dividing by it stays inside `L`
  obtain ⟨u, hu⟩ := IsLocalization.map_units L (⟨m, hm⟩ : 𝔪.primeCompl)
  have hval : ((u : L) : K) = algebraMap R K m := by rw [hu]; rfl
  have hinv : ((↑u⁻¹ : L) : K) * ((u : L) : K) = 1 := by
    rw [← Subring.coe_mul, u.inv_mul, Subring.coe_one]
  have hx_eq : x = ((↑u⁻¹ : L) : K) * (m • x) := by
    rw [Algebra.smul_def, ← hval, ← mul_assoc, hinv, one_mul]
  exact hx_eq ▸ L.mul_mem (↑u⁻¹ : L).2 hmx_L

/-- **A point survives the localisation as long as all its denominators lie in `𝔪`.** Writing
`z = a / s` with `s ∉ 𝔪` exhibits `s` as a denominator of `z`, hence puts `s` in `𝔪`. -/
theorem notMem_ofPrime_of_colon_le (R : Subring K) (𝔪 : Ideal R) [𝔪.IsPrime] {z : K}
    (hcol : (1 : Submodule R K).colon {z} ≤ 𝔪) :
    z ∉ (LocalSubring.ofPrime R 𝔪).toSubring := by
  intro hmem
  obtain ⟨⟨a, ⟨s, hs⟩⟩, heq⟩ :=
    IsLocalization.surj 𝔪.primeCompl (⟨z, hmem⟩ : (LocalSubring.ofPrime R 𝔪).toSubring)
  have h1 : z * (s : K) = (a : K) := congrArg (Subring.subtype _) heq
  have hs_col : s ∈ (1 : Submodule R K).colon {z} := by
    rw [Submodule.mem_colon_singleton, Algebra.smul_def, Submodule.mem_one]
    exact ⟨a, by rw [mul_comm]; exact h1.symm⟩
  exact hs (hcol hs_col)

end LocalSubring

namespace Subring

/-- **A valuation subring separating `z` and strictly below `1` on `J`.** Let `R` be a subring
of a field `K`, integrally closed in `K`, let `z : K` lie outside `R`, and let `J` be an ideal
of `R` some power of which multiplies `z` back into `R`. Then a single valuation subring
`V ⊇ R` both misses `z` and has valuation `< 1` at every element of `J`.

This refines Stacks 090P: the separation alone is
`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`, and the bound on `J` alone is
`Ideal.image_subset_nonunits_valuationSubring`. Taking `J = ⊥` and `n = 1` recovers the former,
so the strength here is that one `V` does both. -/
theorem exists_le_valuationSubring_notMem_valuation_lt_one (R : Subring K)
    [IsIntegrallyClosedIn R K] {z : K} (hz : z ∉ R) {J : Ideal R} {n : ℕ}
    (hJ : ∀ a ∈ J ^ n, (a : K) * z ∈ R) :
    ∃ V : ValuationSubring K, R ≤ V.toSubring ∧ z ∉ V ∧
      ∀ a ∈ J, V.valuation (a : K) < 1 := by
  -- the denominators of `z`, as an ideal of `R`
  set S : Ideal R := (1 : Submodule R K).colon {z} with hS
  have hmem_S : ∀ s : R, s ∈ S ↔ (s : K) * z ∈ R := fun s ↦ by
    rw [hS, Submodule.mem_colon_singleton, Algebra.smul_def, Submodule.mem_one]
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun h ↦ ⟨⟨_, h⟩, rfl⟩⟩
  -- it is proper: `1` is a denominator only if `z` already lies in `R`
  have hS_ne_top : S ≠ ⊤ := fun h ↦ hz (by
    simpa using (hmem_S 1).mp (h ▸ Submodule.mem_top))
  obtain ⟨𝔪, h𝔪, hS𝔪⟩ := S.exists_le_maximal hS_ne_top
  have : 𝔪.IsPrime := h𝔪.isPrime
  -- a power of `J` consists of denominators, so primality puts `J` itself inside `𝔪`
  have hJ𝔪 : J ≤ 𝔪 :=
    Ideal.IsPrime.le_of_pow_le (le_trans (fun a ha ↦ (hmem_S a).mpr (hJ a ha)) hS𝔪)
  -- localise at `𝔪`; the point survives and integral closedness is preserved
  have : IsIntegrallyClosedIn (LocalSubring.ofPrime R 𝔪).toSubring K :=
    LocalSubring.isIntegrallyClosedIn_ofPrime R 𝔪
  obtain ⟨V, hVdom, hzV⟩ := LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (LocalSubring.notMem_ofPrime_of_colon_le R 𝔪 (hS ▸ hS𝔪))
  refine ⟨V, (LocalSubring.le_ofPrime R 𝔪).trans hVdom.1, hzV, fun a ha ↦ ?_⟩
  -- domination carries the maximal ideal of the localisation into that of `V`
  have haL : (⟨(a : K), LocalSubring.le_ofPrime R 𝔪 a.2⟩ :
      (LocalSubring.ofPrime R 𝔪).toSubring) ∈
      IsLocalRing.maximalIdeal (LocalSubring.ofPrime R 𝔪).toSubring :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔪 a).mpr (hJ𝔪 ha)
  have : IsLocalHom (Subring.inclusion hVdom.1) := hVdom.2
  exact (ValuationSubring.valuation_lt_one_iff V _).mp
    (map_nonunit (Subring.inclusion hVdom.1) _ haL)

end Subring
