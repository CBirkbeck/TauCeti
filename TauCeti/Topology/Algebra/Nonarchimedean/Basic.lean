/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Transporting a nonarchimedean topology along an open homomorphism

`NonarchimedeanGroup G` asks that every neighbourhood of `1` contain an *open subgroup*. That
property passes to the target of any open homomorphism that is continuous at `1`: the image of an
open subgroup inside `f ⁻¹' U` is an open subgroup inside `U`.

Mathlib has the embedding case, `NonarchimedeanGroup.nonarchimedean_of_emb`. Injectivity plays no
part in the argument, so the statement below drops it and keeps only openness; the embedding case
is recovered from it.

## Main results

* `NonarchimedeanGroup.nonarchimedean_of_isOpenMap`, and its additive form
  `NonarchimedeanAddGroup.nonarchimedean_of_isOpenMap`.
-/

public section

open Topology

namespace NonarchimedeanGroup

-- This generalization was proposed in the review of TauCetiProject/TauCeti#4930, on the
-- observation that the quotient instance proved there used nothing about quotients beyond
-- continuity and openness of the quotient map.

/-- **Transport along an open homomorphism.** If `f : G →* H` is open and continuous at `1`, and
`G` is nonarchimedean, then so is `H`. This generalizes Mathlib's `nonarchimedean_of_emb`, which
is the case of an open *embedding*; injectivity is not used. -/
@[to_additive /-- **Transport along an open homomorphism.** If `f : G →+ H` is open and continuous
at `0`, and `G` is nonarchimedean, then so is `H`. -/]
theorem nonarchimedean_of_isOpenMap {G H : Type*} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (f : G →* H)
    (hf : ContinuousAt f 1) (hopen : IsOpenMap f) : NonarchimedeanGroup H where
  is_nonarchimedean U hU := by
    obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean (G := G) _ (hf (by simpa using hU))
    -- `Subgroup.coe_map` rewrites the carrier of `V.toSubgroup.map f` to the image `f '' V`,
    -- which is the form both `hopen` and `hV` are stated in. It holds by `rfl`, but is named
    -- here rather than left to unfolding.
    refine ⟨⟨V.toSubgroup.map f, ?_⟩, ?_⟩
    · -- `OpenSubgroup`'s field is stated about `.carrier`; naming it as the subgroup's coercion
      -- is what lets `Subgroup.coe_map` rewrite it to the image `f '' V`.
      change IsOpen ((V.toSubgroup.map f : Subgroup H) : Set H)
      simpa only [Subgroup.coe_map, OpenSubgroup.coe_toSubgroup] using hopen _ V.isOpen
    · -- likewise the subset goal is stated through the `OpenSubgroup` constructor, so its
      -- carrier is named as a `Subgroup` coercion before `Subgroup.coe_map` can rewrite it.
      change ((V.toSubgroup.map f : Subgroup H) : Set H) ⊆ U
      simpa only [Subgroup.coe_map, OpenSubgroup.coe_toSubgroup] using Set.image_subset_iff.2 hV

end NonarchimedeanGroup
