/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# A quotient of a nonarchimedean ring is nonarchimedean

`NonarchimedeanRing R` asks that every neighbourhood of `0` contain an *open additive subgroup*.
That property passes to `R ⧸ I` for any ideal `I`, and the proof is the one-line reason it should:
the quotient map is open, so it carries a basis of open subgroups at `0` to one downstairs.

Mathlib gives `R ⧸ I` its quotient topology and an `IsTopologicalRing` instance
(`Mathlib/Topology/Algebra/Ring/Ideal.lean`) — indeed the latter is built from
`QuotientAddGroup.instIsTopologicalAddGroup`, so the ring-quotient and additive-quotient
topologies agree by construction — but it does not carry the nonarchimedean structure across, and
neither did this repository.

The consumer is the universal property of a rational localisation
(`TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_completion_locTopology`), which
requires `[NonarchimedeanRing B]` on its target. Wedhorn's Example 6.38 presents a rational
localisation as a quotient `C ⧸ a` of a ring of restricted power series, so applying that
universal property to `C ⧸ a` needs exactly this instance.

## Main results

* `TauCeti.instNonarchimedeanRingQuotient`: `R ⧸ I` is nonarchimedean when `R` is.
-/

public section

open Topology

namespace TauCeti

variable {R : Type*} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R] (I : Ideal R)

/-- A quotient of a nonarchimedean ring is nonarchimedean. -/
instance : NonarchimedeanRing (R ⧸ I) where
  is_nonarchimedean U hU := by
    have hpre : (Ideal.Quotient.mk I) ⁻¹' U ∈ 𝓝 (0 : R) :=
      (continuous_quot_mk.tendsto (0 : R)) hU
    obtain ⟨V, hV⟩ := NonarchimedeanRing.is_nonarchimedean _ hpre
    refine ⟨⟨V.toAddSubgroup.map (Ideal.Quotient.mk I).toAddMonoidHom, ?_⟩, ?_⟩
    · -- `OpenAddSubgroup` asks for openness of the bundled subgroup's `carrier`; naming it as
      -- the subgroup's coercion is what lets `AddSubgroup.coe_map` rewrite it to an image.
      change IsOpen ((V.toAddSubgroup.map (Ideal.Quotient.mk I).toAddMonoidHom :
        AddSubgroup (R ⧸ I)) : Set (R ⧸ I))
      rw [AddSubgroup.coe_map]
      exact QuotientRing.isOpenMap_coe I _ V.isOpen
    · rintro _ ⟨x, hx, rfl⟩
      exact hV hx

end TauCeti
