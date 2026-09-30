/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Completion.Homeomorph
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafForEveryPresentation
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SubsetLimit

/-!
# Sheafy Huber rings

Wedhorn calls a Huber ring `A` *sheafy* when, for every ring of integral elements `Â⁺` of its
completion `Â`, the structure presheaf of `Spa(Â, Â⁺)` is a sheaf of topological rings. Here the
sheaf condition on a pair is `TauCeti.Huber.IsSheafyForEveryPresentation`, which asks it of the
presentation-indexed limit presheaf for every compatible pair of definition.

That presheaf is isomorphic, as a presheaf, to Wedhorn's limit over rational subsets
`V ↦ lim_{U ⊆ V} Â⟨U⟩` (`TauCeti.ValuationSpectrum.rationalSubsetLimitPresheaf`), so sheafiness is
equivalently the sheaf condition on that presheaf, for every compatible pair of definition `P`;
the coordinate rings in both presheaves are built from `P`.

## Main definitions

* `TauCeti.Huber.IsSheafyRing`: sheafy Huber rings.

## Main results

* `TauCeti.Huber.isSheafyRing_iff_isSheaf_rationalSubsetLimitPresheaf`: `A` is sheafy exactly
  when every presheaf `V ↦ lim_{U ⊆ V} Â⟨U⟩` of limits over rational subsets, for every ring of
  integral elements of `Â` and every compatible pair of definition, is a sheaf.
* `TauCeti.Huber.IsSheafyRing.isSheafyForEveryPresentation_completionPlus`: if `A` is sheafy and
  `A⁺` is a ring of integral elements of `A`, then `Â⁺`, the closure of the image of `A⁺`,
  satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Definition 8.26.
-/

public section

open CategoryTheory UniformSpace TauCeti.ValuationSpectrum _root_.TopologicalSpace

namespace TauCeti.Huber

universe u

variable (A : Type u) [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A]

/-- **Wedhorn Definition 8.26**: a Huber ring `A` is *sheafy* when every ring of integral elements
`Â⁺` of its completion `Â` satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`, the sheaf
condition on the presentation-indexed limit presheaves of `Spa(Â, Â⁺)`. -/
def IsSheafyRing : Prop :=
  ∀ Aplus : Subring (Completion A), IsRingOfIntegralElements Aplus →
    IsSheafyForEveryPresentation Aplus

variable {A}

/-- Unfolding lemma for the sealed definition `TauCeti.Huber.IsSheafyRing`. -/
theorem isSheafyRing_iff : IsSheafyRing A ↔ ∀ Aplus : Subring (Completion A),
    IsRingOfIntegralElements Aplus → IsSheafyForEveryPresentation Aplus :=
  (Iff.rfl)

/-- **Sheafiness through Wedhorn's limit over rational subsets**: `A` is sheafy exactly when, for
every ring of integral elements `Â⁺` of `Â` and every pair of definition `P` of `Â` contained in
it, the presheaf `V ↦ lim_{U ⊆ V} Â⟨U⟩` of limits over the rational subsets of `Spa(Â, Â⁺)`, with
coordinate rings built from `P`, is a sheaf. `TauCeti.Huber.isSheafyRing_iff` states the same
condition through the presentation-indexed presheaves. -/
theorem isSheafyRing_iff_isSheaf_rationalSubsetLimitPresheaf : IsSheafyRing A ↔
    ∀ (Aplus : Subring (Completion A)) (hAplus : IsRingOfIntegralElements Aplus)
      (P : PairOfDefinition (Completion A)), P.ringOfDefinition ≤ Aplus → Presheaf.IsSheaf
        (Opens.grothendieckTopology ↥(spa Aplus)) (rationalSubsetLimitPresheaf P Aplus fun _ ha ↦
          mem_powerBoundedSubring.mp (hAplus.le_powerBoundedSubring ha)) := by
  simp only [← isSheaf_presentationLimitPresheaf_iff_isSheaf_rationalSubsetLimitPresheaf]
  exact isSheafyRing_iff.trans <| forall₂_congr fun _ hAplus ↦ ⟨(·.isSheaf), .mk hAplus⟩

/-- If `A` is sheafy and `A⁺` is a ring of integral elements of `A`, then `Â⁺`, the closure of the
image of `A⁺` in `Â`, satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`. For this `Â⁺`,
`TauCeti.ValuationSpectrum.spaCompletionHomeomorph` identifies `Spa(Â, Â⁺)` with `Spa(A, A⁺)`. -/
theorem IsSheafyRing.isSheafyForEveryPresentation_completionPlus (h : IsSheafyRing A)
    {Aplus : Subring A} (hAplus : IsRingOfIntegralElements Aplus) :
    IsSheafyForEveryPresentation (completionPlus Aplus) :=
  completionPlus_def Aplus ▸ isSheafyRing_iff.mp h _ hAplus.completion

end TauCeti.Huber

end
