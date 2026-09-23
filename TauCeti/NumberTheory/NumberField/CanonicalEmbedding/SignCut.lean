/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Cutting a sign-symmetric subset of the mixed space at a finset of real places

A subset `A` of the mixed space is *symmetric at the real places* when membership in it depends on
the real coordinates only through their absolute values.  Such a set is stable under reflecting
any one real coordinate, so for a finset `S` of real places the `2 ^ S.card` sign patterns along
`S` cut `A` into pieces of equal volume, exhausting `A` up to the null set where some coordinate
of `S` vanishes.

Cutting `A` down to the points that are positive at every place of `S` therefore divides its
volume by `2 ^ S.card`, the real coordinates outside `S` staying free.  For `S` all of the real
places this is Mathlib's `NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_plusPart`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.isOpen_setOfPred_forall_mem_pos`: the points positive at
  every place of a finset of real places form an open set.
* `TauCeti.NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_inter_pos`: for a set symmetric
  at the real places, the volume is `2 ^ S.card` times the volume of the part that is positive at
  every place of `S`.
-/

public section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- A set stable under reflecting the real coordinate at the place `w` has twice the volume of its
part where that coordinate is positive. -/
private theorem volume_eq_two_mul_volume_inter_pos_at {B : Set (mixedSpace K)}
    {w : {w : InfinitePlace K // w.IsReal}}
    (hB : ∀ x : mixedSpace K, negAt ({w} : Set _) x ∈ B ↔ x ∈ B) (hm : MeasurableSet B) :
    volume B = 2 * volume (B ∩ {x | 0 < x.1 w}) := by
  have hmP : MeasurableSet (B ∩ {x : mixedSpace K | 0 < x.1 w}) :=
    hm.inter (measurableSet_lt measurable_const (by fun_prop))
  have hmN : MeasurableSet (B ∩ {x : mixedSpace K | x.1 w < 0}) :=
    hm.inter (measurableSet_lt (by fun_prop) measurable_const)
  -- reflecting at `w` carries the part of `B` negative at `w` onto the part positive at `w`
  have hNP : B ∩ {x : mixedSpace K | x.1 w < 0}
      = negAt ({w} : Set _) ⁻¹' (B ∩ {x : mixedSpace K | 0 < x.1 w}) := by
    ext x
    simp [hB]
  have hcover : (B ∩ {x : mixedSpace K | 0 < x.1 w} ∪ B ∩ {x : mixedSpace K | x.1 w < 0})
      ∪ B ∩ {x : mixedSpace K | x.1 w = 0} = B := by
    ext x
    grind
  have hdisj : Disjoint (B ∩ {x : mixedSpace K | 0 < x.1 w})
      (B ∩ {x : mixedSpace K | x.1 w < 0}) := by
    grind
  -- the slice where the coordinate vanishes is null, so it does not change the volume
  have hvolB : volume B = volume (B ∩ {x : mixedSpace K | 0 < x.1 w}
      ∪ B ∩ {x : mixedSpace K | x.1 w < 0}) := by
    nth_rewrite 1 [← hcover]
    exact measure_congr <| union_ae_eq_left_of_ae_eq_empty <| ae_eq_empty.mpr <|
      measure_mono_null Set.inter_subset_right (volume_eq_zero w)
  rw [hvolB, measure_union hdisj hmN, hNP,
    volume_preserving_negAt.measure_preimage hmP.nullMeasurableSet, two_mul]

omit [NumberField K] in
/-- The points positive at every place of `S` form an open set: it is a finite intersection of
open half spaces. -/
theorem isOpen_setOfPred_forall_mem_pos (S : Finset {w : InfinitePlace K // w.IsReal}) :
    IsOpen {x : mixedSpace K | ∀ w ∈ S, 0 < x.1 w} := by
  simp only [Set.ofPred_forall]
  exact isOpen_biInter_finset fun w _ ↦ isOpen_lt continuous_const (by fun_prop)

omit [NumberField K] in
open scoped Classical in
private theorem setOfPred_forall_mem_insert_pos (w : {w : InfinitePlace K // w.IsReal})
    (S : Finset {w : InfinitePlace K // w.IsReal}) :
    {x : mixedSpace K | ∀ v ∈ insert w S, 0 < x.1 v}
      = {x | ∀ v ∈ S, 0 < x.1 v} ∩ {x | 0 < x.1 w} := by
  ext x
  grind

open scoped Classical in
/-- **The volume of a sign cut at a finset of real places.**  If membership in `A` depends on the
real coordinates only through their absolute values, then prescribing a positive sign at each
place of `S` divides the volume of `A` by `2 ^ S.card`. -/
theorem volume_eq_two_pow_mul_volume_inter_pos (S : Finset {w : InfinitePlace K // w.IsReal})
    {A : Set (mixedSpace K)} (hA : ∀ x : mixedSpace K, x ∈ A ↔ ((fun w ↦ ‖x.1 w‖), x.2) ∈ A)
    (hm : MeasurableSet A) : volume A = 2 ^ S.card * volume (A ∩ {x | ∀ w ∈ S, 0 < x.1 w}) := by
  have hAneg (s : Set {w : InfinitePlace K // w.IsReal}) (x : mixedSpace K) :
      negAt s x ∈ A ↔ x ∈ A := by
    rw [hA (negAt s x), hA x, funext (negAt_apply_norm_isReal x), negAt_apply_snd]
  induction S using Finset.induction_on with
  | empty => simp
  | @insert w S hw ih =>
    -- `A` is sign-symmetric and `w ∉ S`, so reflecting at `w` preserves the cut along `S`
    have hstable (x : mixedSpace K) : negAt ({w} : Set _) x ∈ A ∩ {x | ∀ v ∈ S, 0 < x.1 v}
        ↔ x ∈ A ∩ {x | ∀ v ∈ S, 0 < x.1 v} := by
      grind [negAt_apply_isReal_and_notMem]
    rw [Finset.card_insert_of_notMem hw, pow_succ, ih, setOfPred_forall_mem_insert_pos w S,
      ← Set.inter_assoc, volume_eq_two_mul_volume_inter_pos_at hstable
        (hm.inter (isOpen_setOfPred_forall_mem_pos S).measurableSet), mul_assoc]

end TauCeti.NumberField.mixedEmbedding
