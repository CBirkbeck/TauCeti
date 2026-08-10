/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Basic

/-!
# The evaluation of a weighted restricted power series

`TauCeti/RingTheory/Huber/WeightedEval/Basic.lean` proves that the terms `φ(coeff ν f) · bν` of
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

* `TauCeti.Huber.weightedEval_C` and `TauCeti.Huber.weightedEval_X`: it sends the constant series
  `C a` to `φ a` and the variable `X i` to `bᵢ`, which is what makes it *the* evaluation at `b`.
  These, and the value on `0`, are unconditional: only one term of each family is nonzero, so no
  summability hypothesis is involved.
* `TauCeti.Huber.hasSum_weightedEvalTerm`: under the hypotheses of the summability theorem, the
  terms have `weightedEval` as their sum. This is what `TauCeti.Huber.weightedEval_add` is read
  off, and what a consumer facing a genuine infinite sum should reach for rather than `tsum`
  lemmas.
* `TauCeti.Huber.weightedEval_zero` and `TauCeti.Huber.weightedEval_add`: the evaluation is
  additive in the series.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

section Values

variable {k : ℕ} {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace B]

/-- **Wedhorn's evaluation** of a series at a tuple `b` along `φ`: the sum of the terms
`φ(coeff ν f) · bν`.

Unconditionally a `tsum`, so it is junk when the family is not summable. The results that take a
genuine infinite sum — `TauCeti.Huber.weightedEval_add` and its corollaries — therefore carry the
hypotheses of `TauCeti.Huber.summable_weightedEvalTerm`, through
`TauCeti.Huber.hasSum_weightedEvalTerm`. The values on `0`, on a constant and on a variable need
none of that: their term families are supported at a single index and are computed directly. -/
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

/-- `TauCeti.Huber.hasSum_weightedEvalTerm` under Wedhorn's coordinatewise hypothesis. -/
theorem hasSum_weightedEvalTerm_of_isWeightedVarPowerBounded (hφ : ContinuousAt φ 0)
    (hb : IsWeightedVarPowerBounded φ T b) {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) :
    HasSum (weightedEvalTerm φ b f) (weightedEval φ b f) :=
  hasSum_weightedEvalTerm hφ (isWeightBounded_of_isWeightedVarPowerBounded hb) hf

/-- `TauCeti.Huber.hasSum_weightedEvalTerm` at the one-weight family, where the hypothesis is that
each variable is power-bounded. -/
theorem hasSum_weightedEvalTerm_of_forall_isPowerBounded (hφ : ContinuousAt φ 0)
    (hb : ∀ i, IsPowerBounded (b i)) {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) f) :
    HasSum (weightedEvalTerm φ b f) (weightedEval φ b f) :=
  hasSum_weightedEvalTerm hφ ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).mpr hb) hf

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

/-- `TauCeti.Huber.weightedEval_add` under Wedhorn's coordinatewise hypothesis. -/
theorem weightedEval_add_of_isWeightedVarPowerBounded (hφ : ContinuousAt φ 0)
    (hb : IsWeightedVarPowerBounded φ T b) {f g : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) (hg : IsWeightedRestricted T g) :
    weightedEval φ b (f + g) = weightedEval φ b f + weightedEval φ b g :=
  weightedEval_add hφ (isWeightBounded_of_isWeightedVarPowerBounded hb) hf hg

/-- `TauCeti.Huber.weightedEval_add` at the one-weight family. -/
theorem weightedEval_add_of_forall_isPowerBounded (hφ : ContinuousAt φ 0)
    (hb : ∀ i, IsPowerBounded (b i)) {f g : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) f)
    (hg : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) g) :
    weightedEval φ b (f + g) = weightedEval φ b f + weightedEval φ b g :=
  weightedEval_add hφ ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).mpr hb) hf hg

end Sums

end TauCeti.Huber

end
