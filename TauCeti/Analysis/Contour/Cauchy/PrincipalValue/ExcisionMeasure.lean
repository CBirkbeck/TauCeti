/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The excised parameter set shrinks to nothing

An `ε`-excision deletes from the parameter interval every time at which the curve comes within
`ε` of one of finitely many centres. This file records that the deleted set carries no length in
the limit: the integral of the excision's indicator over `[a, b]` tends to `b - a` as `ε → 0⁺`.

The only thing needed of the curve is that it meets each centre at most once, so that the set of
parameters deleted at every `ε` is finite, hence null. Injectivity is the convenient form of that
hypothesis, and is what the fundamental-domain arc satisfies.

## Main results

* `TauCeti.Contour.tendsto_intervalIntegral_excisionIndicator`: the excision indicator's integral
  over `[a, b]` tends to `b - a` as `ε → 0⁺`.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti.Contour

/-- A point lying off a finite set stays off it by a fixed positive margin. -/
private theorem exists_pos_le_norm_sub_of_notMem {S : Finset ℂ} {z : ℂ} (hz : z ∉ S) :
    ∃ δ > 0, ∀ s ∈ S, δ ≤ ‖z - s‖ := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · exact ⟨S.inf' hne fun s => ‖z - s‖,
      (Finset.lt_inf'_iff _).2 fun s hs =>
        norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hz (h ▸ hs)),
      fun s hs => Finset.inf'_le _ hs⟩

/-- The parameters at which an injective curve meets a finite set are finite. -/
private theorem finite_preimage_of_injOn {γ : ℝ → ℂ} {a b : ℝ} (hγ : InjOn γ (Icc a b))
    (S : Finset ℂ) : {t ∈ Icc a b | γ t ∈ S}.Finite :=
  Set.Finite.of_finite_image
    (S.finite_toSet.subset (by rintro _ ⟨t, ht, rfl⟩; exact ht.2))
    (hγ.mono fun _ ht => ht.1)

/-- **The excised parameter set shrinks to nothing.** For a continuous curve meeting each of
finitely many centres at most once, the length of the parameter interval surviving the deletion
of the centres' `ε`-neighbourhoods tends to the whole length as `ε → 0⁺`.

Only the finiteness of the parameters the curve sends into `S` is used; injectivity on `[a, b]`
is the convenient hypothesis giving it. -/
theorem tendsto_intervalIntegral_excisionIndicator {γ : ℝ → ℂ} (hγc : Continuous γ) {a b : ℝ}
    (hab : a ≤ b) (hγ : InjOn γ (Icc a b)) (S : Finset ℂ) :
    Tendsto (fun ε => ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then (0 : ℝ) else 1)
      (𝓝[>] 0) (𝓝 (b - a)) := by
  -- Dominated convergence compares an integral with an integral, so the limit `b - a` is first
  -- presented as one. (Mathlib's `tendsto_measure_of_ae_tendsto_indicator` proves the companion
  -- statement about the surviving set's *measure*; the integral form is what the arc's excised
  -- integral consumes, and reaching it from the measure needs the same two facts below plus a
  -- measure-to-integral and an `ENNReal.toReal` conversion.)
  have hconst : ∫ _ in a..b, (1 : ℝ) = b - a := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  rw [← hconst]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε => ?_)
    intervalIntegrable_const ?_
  · refine (stronglyMeasurable_const.ite ?_ stronglyMeasurable_const).aestronglyMeasurable
    have h : {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} = ⋃ s ∈ S, {t | ‖γ t - s‖ ≤ ε} := by
      ext; simp
    rw [h]
    exact Finset.measurableSet_biUnion _ fun s _ =>
      (isClosed_le (by fun_prop) continuous_const).measurableSet
  · exact Eventually.of_forall fun t _ => by split_ifs <;> norm_num
  · rw [ae_iff]
    refine measure_mono_null (fun t ht => ?_)
      ((finite_preimage_of_injOn hγ S).measure_zero volume)
    push Not at ht
    obtain ⟨htmem, htne⟩ := ht
    rw [uIoc_of_le hab] at htmem
    by_contra hnot
    refine htne (tendsto_const_nhds.congr' ?_)
    obtain ⟨δ, hδ, hδle⟩ :=
      exists_pos_le_norm_sub_of_notMem (S := S) (z := γ t)
        (fun hmem => hnot ⟨⟨htmem.1.le, htmem.2⟩, hmem⟩)
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact (if_neg (by push Not; exact fun s hs => hε.2.trans_le (hδle s hs))).symm

end TauCeti.Contour
