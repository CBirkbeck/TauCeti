/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Map

/-!
# The evaluation of a weighted restricted series is multiplicative

`TauCeti/RingTheory/Huber/WeightedEval/Map.lean` gives Wedhorn's evaluation its additive API. This
file supplies the remaining half — `weightedEval (f * g) = weightedEval f * weightedEval g` — which
together with `weightedEval_C` and `weightedEval_X` is what makes Proposition 5.50 a universal
property.

The argument is the Cauchy product. `HasSum.mul_of_nonarchimedean` sums the products of terms over
*pairs* of multi-indices; regrouping those pairs by their sum, which `HasSum.tsum_fiberwise` does,
turns that into a sum over single multi-indices whose `ν`-th entry runs over the antidiagonal of
`ν` — and that entry is exactly the `ν`-th term of `f * g`, by `MvPowerSeries.coeff_mul`.

## Main results

* `TauCeti.Huber.weightedEval_mul`: the evaluation is multiplicative on `T`-restricted series.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

section Term

variable {k : ℕ} {A B : Type*} [CommRing A] [CommRing B] {φ : A →+* B} {b : Fin k → B}

/-- The product of the `α`-th term of `f` and the `β`-th term of `g` is the term the pair
contributes to `f * g`: the monomials multiply because `bα · bβ = b(α+β)`. -/
theorem weightedEvalTerm_mul_weightedEvalTerm (f g : MvPowerSeries (Fin k) A)
    (α β : Fin k →₀ ℕ) :
    weightedEvalTerm φ b f α * weightedEvalTerm φ b g β
      = φ (MvPowerSeries.coeff α f * MvPowerSeries.coeff β g) * ∏ i, b i ^ (α + β) i := by
  simp only [weightedEvalTerm_def, map_mul, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
  ring

end Term

section Mul

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B]
  [T2Space B] {φ : A →+* B} {T : Fin k → Set A} {b : Fin k → B}

/-- The pairs of multi-indices summing to `ν` are exactly the antidiagonal of `ν`. -/
private theorem preimage_add_singleton (ν : Fin k →₀ ℕ) :
    (fun p : (Fin k →₀ ℕ) × (Fin k →₀ ℕ) ↦ p.1 + p.2) ⁻¹' {ν} = ↑(Finset.antidiagonal ν) := by
  ext p
  simp [Finset.mem_antidiagonal]

/-- **The evaluation is multiplicative**, by the Cauchy product: the products of terms summed over
pairs of multi-indices, regrouped by the sum of the pair, are the terms of `f * g`.

Only `f` and `g` need be `T`-restricted. Restrictedness of `f * g` is not a hypothesis and no
weight-family condition appears: the regrouping produces the terms of `f * g` and their sum
whether or not `f * g` is separately known to be restricted. -/
theorem weightedEval_mul (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) {f g : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) (hg : IsWeightedRestricted T g) :
    weightedEval φ b (f * g) = weightedEval φ b f * weightedEval φ b g := by
  classical
  have hpair : HasSum (fun p : (Fin k →₀ ℕ) × (Fin k →₀ ℕ) ↦
      weightedEvalTerm φ b f p.1 * weightedEvalTerm φ b g p.2)
      (weightedEval φ b f * weightedEval φ b g) :=
    (hasSum_weightedEval hφ hb hf).mul_of_nonarchimedean (hasSum_weightedEval hφ hb hg)
  have hfib := hpair.tsum_fiberwise fun p ↦ p.1 + p.2
  have key : (fun ν ↦ ∑' p : (fun q : (Fin k →₀ ℕ) × (Fin k →₀ ℕ) ↦ q.1 + q.2) ⁻¹' {ν},
      weightedEvalTerm φ b f (↑p : (Fin k →₀ ℕ) × (Fin k →₀ ℕ)).1 *
        weightedEvalTerm φ b g (↑p : (Fin k →₀ ℕ) × (Fin k →₀ ℕ)).2)
      = weightedEvalTerm φ b (f * g) := by
    funext ν
    rw [preimage_add_singleton ν, Finset.tsum_subtype' (Finset.antidiagonal ν)
      fun q : (Fin k →₀ ℕ) × (Fin k →₀ ℕ) ↦
        weightedEvalTerm φ b f q.1 * weightedEvalTerm φ b g q.2,
      weightedEvalTerm_def, MvPowerSeries.coeff_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [weightedEvalTerm_mul_weightedEvalTerm, Finset.mem_antidiagonal.mp hp]
  rw [key] at hfib
  simpa only [weightedEval_def] using hfib.tsum_eq

end Mul

end TauCeti.Huber

end
