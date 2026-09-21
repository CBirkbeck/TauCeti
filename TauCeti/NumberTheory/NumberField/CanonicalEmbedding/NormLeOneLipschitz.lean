/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
public import TauCeti.Topology.MetricSpace.LipschitzParametrizable

/-!
# A Lipschitz parametrization of the frontier of the norm-≤-one region

`TauCeti.NumberTheory.GeometryOfNumbers.LatticePointCount` counts lattice points in a dilated
region with a power-saving error, but only for regions whose frontier is Lipschitz
parametrizable: `exists_abs_ncard_smul_inter_sub_le` takes
`IsLipschitzParametrizable (finrank ℝ E - 1) (frontier D)` as a hypothesis. Mathlib proves that
`frontier (normLeOne K)` is *null* (`volume_frontier_normLeOne`), which is what a rate-free limit
needs and is strictly weaker: a null frontier gives no error term at all.

This file works towards discharging that hypothesis for `normLeOne K`. Mathlib presents the
region through `expMapBasis`, a partial homeomorphism of `realSpace K` whose image of the box
`paramSet K = univ.pi fun w ↦ if w = w₀ then Iic 0 else Ico 0 1` is the norm-≤-one region up to
`normAtAllPlaces`. The frontier of a box is the union of its faces, so a Lipschitz cover of the
image reduces to parametrizing the image of each face — which is what the maps here do.

The `w₀` face is where the unbounded `Iic 0` direction is pinned at its endpoint; the side faces
pin one of the bounded `Ico 0 1` directions, and there the substitution `t = exp (x w₀)` turns the
unbounded direction into the freed cube coordinate.

## Main definitions

* `faceMapZero`: the face where the unbounded `w₀` coordinate sits at its endpoint.
* `faceMapSide`: the face pinning one bounded coordinate at `0` or `1`.

## Main results

* `isLipschitzParametrizable_frontier_image_paramSet`: the frontier of the box image is Lipschitz
  parametrizable in dimension `rank K`, one less than that of `realSpace K`.
* `contDiff_expMapBasis`: the parametrization is smooth.
* `contDiff_faceMapZero`, `contDiff_faceMapSide`: so is each face map.
* `frontier_image_subset_of_closure_subset`: the frontier of an image sits inside the image of
  the source's boundary, for an open injective map.
* `frontier_image_paramSet_subset`: its instance for the box whose image is the norm-≤-one
  region, where the extra point is the origin.
* `image_boundary_paramSet_subset`: the image of the box boundary is covered by the faces.

## References

* C. Birkbeck and R. Brasca, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean`, from which the face
  decomposition is adapted: `faceMapZero`, `faceMapSide`, `contDiff_faceMapZero`,
  `contDiff_faceMapSide`, `frontier_image_subset_of_closure_subset` and
  `frontier_image_paramSet_subset` follow that file's declarations of the same names.
-/

public section

open Finset Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units dirichletUnitTheorem
open scoped NumberField

/-- **The frontier of an image, from the boundary of the source.** For an open injective `f`, if
the closure of `f '' s` is contained in `f '' closure s` together with one extra point `p`, then
the frontier of `f '' s` lies in the image of the boundary `closure s \ interior s`, together
with `p`.

This is general topology, stated here because the number-field instance below is its only
consumer: openness shrinks the interior side (`IsOpenMap.image_interior_subset`), the hypothesis
shrinks the closure side, and injectivity lets the difference of images become the image of the
difference. -/
theorem frontier_image_subset_of_closure_subset {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsOpenMap f) (hfi : Function.Injective f) {s : Set X}
    {p : Y} (hcl : closure (f '' s) ⊆ f '' closure s ∪ {p}) :
    frontier (f '' s) ⊆ f '' (closure s \ interior s) ∪ {p} := by
  refine (Set.sdiff_subset_sdiff hcl (hf.image_interior_subset s)).trans ?_
  rw [Set.union_sdiff_distrib, ← Set.image_sdiff hfi]
  exact Set.union_subset_union_right _ Set.sdiff_subset

namespace NumberField.mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

/-- **The box parametrization is smooth.** `expMapBasis` is an exponential in the `w₀`
coordinate times a product of real powers in the others, so it is `C^n` for every `n`. The
side condition discharged here is that each `w (fundSystem ...)` is nonzero, which holds because
an infinite place is positive on a unit. -/
theorem contDiff_expMapBasis {n : WithTop ℕ∞} : ContDiff ℝ n (⇑(expMapBasis (K := K))) := by
  classical
  rw [show ⇑(expMapBasis (K := K)) = fun x : realSpace K ↦
      Real.exp (x w₀) • fun w : InfinitePlace K ↦
        ∏ i : {w : InfinitePlace K // w ≠ w₀},
          w (fundSystem K (equivFinRank.symm i)) ^ x i from funext expMapBasis_apply']
  fun_prop (disch := exact fun x ↦ (InfinitePlace.pos_iff.mpr (by simp)).ne')

open scoped Classical in
/-- **The `w₀` face.** `paramSet K` is unbounded only in the `w₀` direction, where it is `Iic 0`;
its finite endpoint is `0`. This plugs `0` into that slot and the cube coordinates into the rest. -/
noncomputable def faceMapZero (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  expMapBasis fun w ↦ if hw : w = w₀ then 0 else c ⟨w, hw⟩

open scoped Classical in
/-- **A side face.** Pinning a bounded coordinate `i ≠ w₀` at an endpoint `a ∈ {0, 1}` frees one
cube coordinate, and `expMapBasis_apply''` lets the unbounded `w₀` direction take its place: the
substitution `t = exp (x w₀) ∈ (0, 1]` turns `Iic 0` into the freed coordinate `c i`. -/
noncomputable def faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ)
    (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  c i • expMapBasis fun w ↦ if hw : w = w₀ then 0 else
    if (⟨w, hw⟩ : {w : InfinitePlace K // w ≠ w₀}) = i then a else c ⟨w, hw⟩

open scoped Classical in
/-- The `w₀` face map is `C¹`: it is `expMapBasis` after a map that is coordinatewise either
constant or a projection. -/
theorem contDiff_faceMapZero : ContDiff ℝ 1 (faceMapZero K) := by
  refine (contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ ?_)
  by_cases hw : w = w₀
  · simpa [hw] using contDiff_const
  · simpa [hw] using contDiff_apply ℝ ℝ _

open scoped Classical in
/-- A side face map is `C¹`: the freed coordinate scales a composition of the same shape. -/
theorem contDiff_faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ) :
    ContDiff ℝ 1 (faceMapSide K i a) := by
  refine (contDiff_apply ℝ ℝ i).smul ((contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ ?_))
  by_cases hw : w = w₀
  · simpa [hw] using contDiff_const
  · simp only [hw, ↓reduceDIte]
    by_cases hi : (⟨w, hw⟩ : {w : InfinitePlace K // w ≠ w₀}) = i
    · simpa [hi] using contDiff_const
    · simpa [hi] using contDiff_apply ℝ ℝ _

/-- **The closure of the box image adds only the origin.** `compactSet K` is closed and contains
the image of the closed box, so it contains the closure of the image; Mathlib identifies it as
that image together with `0`. The origin is what the `w₀` coordinate escapes to as it runs to
`-∞`, and it is the sole reason the closure of the image is not the image of the closure. -/
theorem closure_image_paramSet_subset :
    closure (expMapBasis '' paramSet K) ⊆ expMapBasis '' closure (paramSet K) ∪ {0} := by
  rw [← compactSet_eq_union]
  exact (isCompact_compactSet K).isClosed.closure_subset_iff.mpr
    ((Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet K))

/-- **The frontier of the box image lies in the image of the box boundary, plus the origin.**
This is the reduction the Lipschitz cover runs on: the boundary of a product of intervals is a
finite union of faces, so parametrizing it reduces to parametrizing each face. -/
theorem frontier_image_paramSet_subset :
    frontier (expMapBasis '' paramSet K) ⊆
      expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ∪ {0} :=
  frontier_image_subset_of_closure_subset
    (fun _ hs ↦ expMapBasis.isOpen_image_of_subset_source hs (by simp [expMapBasis_source]))
    (injective_expMapBasis K) (closure_image_paramSet_subset K)

variable {K}

open scoped Classical in
/-- **A point of the `w₀` face is hit by `faceMapZero`.** Its cube coordinates are the point's own
coordinates away from `w₀`, which lie in `Icc 0 1` because the point is in the closed box; the
pinned coordinate agrees because the point sits at the face's endpoint `x w₀ = 0`. -/
theorem expMapBasis_mem_image_faceMapZero {x : realSpace K} (hx : x ∈ closure (paramSet K))
    (hx₀ : x w₀ = 0) :
    expMapBasis x ∈ faceMapZero K '' Set.Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 := by
  rw [closure_paramSet, Set.mem_univ_pi] at hx
  have hmem : ∀ i : {w : InfinitePlace K // w ≠ w₀}, x i ∈ Set.Icc (0 : ℝ) 1 :=
    fun i ↦ by simpa [i.2] using hx i
  refine ⟨fun i ↦ x i, ⟨fun i ↦ (hmem i).1, fun i ↦ (hmem i).2⟩, ?_⟩
  exact congrArg expMapBasis (funext fun w ↦ by by_cases hw : w = w₀ <;> simp [hw, hx₀])

open scoped Classical in
/-- **A point of the side face pinning `i` is hit by `faceMapSide`.** The substitution
`t = exp (x w₀) ∈ (0, 1]` moves the unbounded `w₀` direction into the cube coordinate freed by
pinning `i`, so the cube point is the original coordinates with `i` replaced by `t`. -/
theorem expMapBasis_mem_image_faceMapSide {x : realSpace K} (hx : x ∈ closure (paramSet K))
    (i : {w : InfinitePlace K // w ≠ w₀}) :
    expMapBasis x ∈
      faceMapSide K i (x i) '' Set.Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 := by
  rw [closure_paramSet, Set.mem_univ_pi] at hx
  have hx₀ : x w₀ ≤ 0 := by simpa using hx w₀
  have hmem : ∀ j : {w : InfinitePlace K // w ≠ w₀}, x j ∈ Set.Icc (0 : ℝ) 1 :=
    fun j ↦ by simpa [j.2] using hx j
  refine ⟨Function.update (fun j : {w : InfinitePlace K // w ≠ w₀} ↦ x j) i (Real.exp (x w₀)),
    ⟨fun j ↦ ?_, fun j ↦ ?_⟩, ?_⟩
  · rcases eq_or_ne j i with rfl | hj
    · simpa using (Real.exp_pos (x w₀)).le
    · simpa [Function.update_of_ne hj] using (hmem j).1
  · rcases eq_or_ne j i with rfl | hj
    · simpa using Real.exp_le_one_iff.2 hx₀
    · simpa [Function.update_of_ne hj] using (hmem j).2
  · rw [faceMapSide, Function.update_self, expMapBasis_apply'' x]
    refine congrArg (fun z : realSpace K ↦ Real.exp (x w₀) • expMapBasis z) (funext fun w ↦ ?_)
    by_cases hw : w = w₀
    · simp [hw]
    · by_cases hwi : (⟨w, hw⟩ : {w : InfinitePlace K // w ≠ w₀}) = i
      · simp [hw, hwi, ← Subtype.ext_iff.mp hwi]
      · simp [hw, hwi]

variable (K)

open scoped Classical in
/-- **The boundary of the box is covered by the faces.** A point of the closed box that misses the
open box has some coordinate at an endpoint: the `w₀` coordinate at `0`, or a bounded coordinate at
`0` or `1`. Those are exactly the faces parametrized by `faceMapZero` and `faceMapSide`. -/
theorem image_boundary_paramSet_subset :
    expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ⊆
      faceMapZero K '' Set.Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 ∪
        ⋃ p : {w : InfinitePlace K // w ≠ w₀} × Bool,
          faceMapSide K p.1 (if p.2 then 1 else 0) ''
            Set.Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 := by
  rintro _ ⟨x, ⟨hxc, hxi⟩, rfl⟩
  have hbox := (closure_paramSet K).subset hxc
  rw [Set.mem_univ_pi] at hbox
  rw [interior_paramSet] at hxi
  have hsome : ∃ w : InfinitePlace K,
      x w ∉ (if w = w₀ then Set.Iio (0 : ℝ) else Set.Ioo 0 1) := by
    by_contra hcon
    push Not at hcon
    exact hxi (Set.mem_univ_pi.2 hcon)
  obtain ⟨w, hw⟩ := hsome
  by_cases hw₀ : w = w₀
  · subst hw₀
    have hge : (0 : ℝ) ≤ x w₀ := by simpa using hw
    exact Or.inl (expMapBasis_mem_image_faceMapZero hxc
      (le_antisymm (by simpa using hbox w₀) hge))
  · have hnot : x w ∉ Set.Ioo (0 : ℝ) 1 := by simpa [hw₀] using hw
    have hmem : x w ∈ Set.Icc (0 : ℝ) 1 := by simpa [hw₀] using hbox w
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hnot
    refine Or.inr ?_
    rcases hnot with h | h
    · exact Set.mem_iUnion.2 ⟨(⟨w, hw₀⟩, false), by
        simpa [le_antisymm h hmem.1] using expMapBasis_mem_image_faceMapSide hxc ⟨w, hw₀⟩⟩
    · exact Set.mem_iUnion.2 ⟨(⟨w, hw₀⟩, true), by
        simpa [le_antisymm hmem.2 h] using expMapBasis_mem_image_faceMapSide hxc ⟨w, hw₀⟩⟩

private theorem isLipschitzParametrizable_image_boundary_paramSet :
    TauCeti.IsLipschitzParametrizable (rank K)
      (expMapBasis '' (closure (paramSet K) \ interior (paramSet K))) := by
  classical
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = rank K :=
    (Fintype.card_congr equivFinRank).symm.trans (Fintype.card_fin _)
  refine .mono ?_ (image_boundary_paramSet_subset K)
  refine .union (.image_unitCube_of_contDiff hcard (contDiff_faceMapZero K)) ?_
  exact .iUnion fun p ↦ .image_unitCube_of_contDiff hcard (contDiff_faceMapSide K p.1 _)

/-- **The frontier of the box image is Lipschitz parametrizable in codimension one.** This is the
hypothesis `TauCeti.IsLipschitzParametrizable.exists_ncard_smul_add_inter_le` needs to turn a
lattice-point count into a count with a power-saving error term; Mathlib's
`volume_frontier_normLeOne` gives only that the frontier is null, which carries no error term.

The dimension is `rank K = #(InfinitePlace K) - 1`, one less than that of `realSpace K`. -/
theorem isLipschitzParametrizable_frontier_image_paramSet :
    TauCeti.IsLipschitzParametrizable (rank K) (frontier (expMapBasis '' paramSet K)) :=
  .mono ((isLipschitzParametrizable_image_boundary_paramSet K).union (.singleton 0)) <|
    frontier_image_paramSet_subset K

end NumberField.mixedEmbedding.fundamentalCone
