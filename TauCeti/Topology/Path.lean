/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected

/-!
# A function continuous on a closed interval traverses its image as a path

Mathlib's `Path.segment a b` is the straight-line path traversing `[a, b] ⊆ ℝ`, and `Path.map'`
pushes a path forward along a map continuous on its range. Composing the two turns a function `F`
continuous on `Icc a b` into a `Path` from `F a` to `F b`. The lemma below records the two facts a
consumer actually needs about that composite: its range is exactly `F '' Icc a b`, and it is given
pointwise by the affine reparametrisation `AffineMap.lineMap a b`.

Packaging this as an existential statement rather than a definition is deliberate: the composite is
already built from Mathlib's two constructions, so naming it would add a definition — and the simp
lemmas and interface that come with one — for something a consumer only ever uses through the two
properties above.

Degenerate intervals are allowed: the hypothesis is `a ≤ b`, so `a = b` is permitted, and there the
traversed set `F '' Icc a a` is the single point `{F a}`.

The intended consumer is layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, Carathéodory's
boundary correspondence, through `TauCeti/Analysis/Complex/Conformal/Crosscut/Path.lean`: a closed
image crosscut is described set-theoretically as the image of a closed angular interval, and the
separation argument that consumes it needs that description upgraded to a continuous
parametrisation.
-/

public section

open Set

open scoped unitInterval

namespace Path

/-- **A continuous function on `Icc a b` traverses its image as a path.** Reparametrising `[a, b]`
affinely by the unit interval turns `F` into a path from `F a` to `F b` whose range is exactly
`F '' Icc a b`. -/
theorem exists_path_range_eq_image_Icc {Y : Type*} [TopologicalSpace Y] {a b : ℝ} (hab : a ≤ b)
    {F : ℝ → Y} (hFcIcc : ContinuousOn F (Icc a b)) :
    ∃ γ : Path (F a) (F b), range γ = F '' Icc a b ∧
      ∀ t : unitInterval, γ t = F (AffineMap.lineMap a b (t : ℝ)) := by
  have hrange : range (Path.segment a b) = Icc a b := by
    rw [Path.range_segment, segment_eq_Icc hab]
  have hcoe : ⇑((Path.segment a b).map' (hrange ▸ hFcIcc)) = F ∘ ⇑(Path.segment a b) := by
    simp only [Path.map', Path.coe_mk_mk]
  refine ⟨(Path.segment a b).map' (hrange ▸ hFcIcc), ?_, fun t => ?_⟩
  · rw [hcoe, range_comp, hrange]
  · rw [hcoe, Function.comp_apply, Path.segment_apply]

end Path
