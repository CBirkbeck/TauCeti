/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval

/-!
# The evaluation of a weighted restricted power series

`TauCeti/RingTheory/Huber/WeightedEval.lean` proves that the terms `φ(coeff ν f) · bν` of
Wedhorn's evaluation (Proposition 5.50) are summable. This file takes their sum and gives it the
API a universal property needs: the value on a constant series, the value on a variable, and
additivity in the series.

Multiplicativity is **not** proved here. `weightedEval (f * g) = weightedEval f * weightedEval g`
is a Cauchy-product argument — the coefficients of `f * g` are sums over the antidiagonal, so the
statement is a reindexing of a double sum rather than a consequence of anything below — and it is
the remaining step before 5.50 can be stated as a universal property.

## Main definitions

* `TauCeti.Huber.weightedEval`: the sum `∑' ν, φ(coeff ν f) · bν`.

## Main results

* `TauCeti.Huber.hasSum_weightedEvalTerm`: under the hypotheses of the summability theorem, the
  terms have `weightedEval` as their sum. Every result below is read off this, and a consumer
  wanting to compute a value should reach for it rather than for `tsum` lemmas.
* `TauCeti.Huber.weightedEval_zero`, `TauCeti.Huber.weightedEval_add`: the evaluation is additive
  in the series.
* `TauCeti.Huber.weightedEval_C` and `TauCeti.Huber.weightedEval_X`: it sends the constant series
  `C a` to `φ a` and the variable `X i` to `bᵢ`, which is what makes it *the* evaluation at `b`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

section Values

variable {k : ℕ} {A B : Type*} [CommRing A] [CommRing B] [UniformSpace B]

/-- **Wedhorn's evaluation** of a series at a tuple `b` along `φ`: the sum of the terms
`φ(coeff ν f) · bν`.

Unconditionally a `tsum`, so it is junk when the family is not summable; every result about it
carries the hypotheses of `TauCeti.Huber.summable_weightedEvalTerm`, and
`TauCeti.Huber.hasSum_weightedEvalTerm` is the bridge. -/
noncomputable def weightedEval (φ : A →+* B) (b : Fin k → B) (f : MvPowerSeries (Fin k) A) : B :=
  ∑' ν, weightedEvalTerm φ b f ν

/-- Unfolding lemma for `TauCeti.Huber.weightedEval`. -/
theorem weightedEval_def (φ : A →+* B) (b : Fin k → B) (f : MvPowerSeries (Fin k) A) :
    weightedEval φ b f = ∑' ν, weightedEvalTerm φ b f ν := (rfl)

/-- The evaluation of the zero series is zero. -/
@[simp]
theorem weightedEval_zero (φ : A →+* B) (b : Fin k → B) :
    weightedEval φ b (0 : MvPowerSeries (Fin k) A) = 0 := by
  simp [weightedEval_def, weightedEvalTerm_def]

/-- **The evaluation sends a constant series to its image.** Only the constant term contributes,
since every other coefficient of `C a` vanishes. -/
@[simp]
theorem weightedEval_C (φ : A →+* B) (b : Fin k → B) (a : A) :
    weightedEval φ b (MvPowerSeries.C a) = φ a := by
  classical
  rw [weightedEval_def, tsum_eq_single 0 ?_]
  · simp [weightedEvalTerm_def]
  · intro ν hν
    simp [weightedEvalTerm_def, MvPowerSeries.coeff_C, hν]

/-- **The evaluation sends a variable to its value.** Only the multi-index `single i 1`
contributes, and its monomial is `bᵢ`. -/
@[simp]
theorem weightedEval_X (φ : A →+* B) (b : Fin k → B) (i : Fin k) :
    weightedEval φ b (MvPowerSeries.X i) = b i := by
  classical
  rw [weightedEval_def, tsum_eq_single (Finsupp.single i 1) ?_]
  · simp [weightedEvalTerm_def, MvPowerSeries.coeff_X, Finsupp.single_apply,
      Finset.prod_ite_eq]
  · intro ν hν
    simp [weightedEvalTerm_def, MvPowerSeries.coeff_X, hν]

end Values

section Sums

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanAddGroup B] [CompleteSpace B]
  {φ : A →+* B} {T : Fin k → Set A} {b : Fin k → B}

/-- **The terms sum to the evaluation.** This is the form in which additivity below uses
summability, and the form a consumer should use: it names the sum rather than leaving it as a
`tsum` to be manipulated. -/
theorem hasSum_weightedEvalTerm (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ T b)
    {f : MvPowerSeries (Fin k) A} (hf : IsWeightedRestricted T f) :
    HasSum (weightedEvalTerm φ b f) (weightedEval φ b f) :=
  (summable_weightedEvalTerm hφ hb hf).hasSum

variable [T2Space B]

/-- **The evaluation is additive in the series.** Both summability hypotheses are needed: a sum of
two families is the sum of their sums only when each converges. -/
theorem weightedEval_add (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ T b)
    {f g : MvPowerSeries (Fin k) A} (hf : IsWeightedRestricted T f)
    (hg : IsWeightedRestricted T g) :
    weightedEval φ b (f + g) = weightedEval φ b f + weightedEval φ b g := by
  have hterm : weightedEvalTerm φ b (f + g)
      = fun ν ↦ weightedEvalTerm φ b f ν + weightedEvalTerm φ b g ν := by
    funext ν
    simp [weightedEvalTerm_def, add_mul]
  rw [weightedEval_def, hterm]
  exact ((hasSum_weightedEvalTerm hφ hb hf).add (hasSum_weightedEvalTerm hφ hb hg)).tsum_eq

end Sums

end TauCeti.Huber

end
