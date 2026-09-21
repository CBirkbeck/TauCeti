/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Completion.Homeomorph
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Homeomorph
public import TauCeti.Topology.Homeomorph.SetCongr

/-!
# The adic spectrum of `A⟨T/s⟩` is the rational subset

For a rational subset `R(T/s)` of `Spa (A, A⁺)`, pullback along the structure map
`ρ : A → A⟨T/s⟩` is a homeomorphism

```text
Spa (A⟨T/s⟩, A_U⁺) ≃ₜ R(T/s).
```

`Spa.Localization.Homeomorph` identifies the adic spectrum of the *uncompleted* topological
localization `A(T/s)` with `R(T/s)` and leaves the completed coordinate ring aside; this file
supplies the remaining step, which is the completion homeomorphism of `Spa.Completion.Homeomorph`
applied to `A(T/s)`.

That is also Wedhorn's own argument. He factors `ρ` as

```text
A → A(T/s) → A⟨T/s⟩,
```

observes that the second map induces a homeomorphism by **Proposition 7.48**, and is left with
the first, which is `spaLocalizationHomeomorph`. Nothing further is needed here: the plus ring
`A_U⁺` of `A⟨T/s⟩` is by construction the closure of the image of `C`, the integral closure of
`A⁺[T/s]` in `A(T/s)`, and that is exactly the plus ring Proposition 7.48 puts on a completion.
`completedPlusSubring_eq_completionPlus` records that agreement.

The two homeomorphisms being composed do not meet on the nose, and the mismatches are pure
bookkeeping: the middle adic spectrum is presented with two different but equal plus rings, and
`spaLocalizationHomeomorph` is stated at `locTopology` while the completion presents `A(T/s)` at
the topology `locUniformSpace` induces. Both equations are equations of *subsets* of the
valuation spectrum — which is topologized by the ring structure alone — so both are crossed by
`Homeomorph.setCongr`, whose forward map is the identity on underlying valuations. That is what
keeps `spaCompletedLocalizationHomeomorph_apply` a computation rather than a transport.

No completeness, Tate or Noetherian hypothesis is needed, and `A⁺` is an arbitrary subring
subject only to the hypothesis `A₀ ≤ A⁺` that `spaLocalizationHomeomorph` already carries.

## Main definitions

* `TauCeti.ValuationSpectrum.spaCompletedLocalizationHomeomorph`: the homeomorphism
  `Spa (A⟨T/s⟩, A_U⁺) ≃ₜ R(T/s)`.

## Main results

* `TauCeti.ValuationSpectrum.completedPlusSubring_eq_completionPlus`: `A_U⁺` is the completion
  plus ring of `C`.
* `TauCeti.ValuationSpectrum.spaCompletedLocalizationHomeomorph_apply` and
  `TauCeti.ValuationSpectrum.coe_spaCompletedLocalizationHomeomorph`: the homeomorphism is the
  canonical map `spaLocToRationalSubset`, so it is that map which is a homeomorphism.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2 (2), first
  assertion, and Proposition 7.48.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.Localization UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **`A_U⁺` is the completion plus ring of `C`.** Both are the closure, in `A⟨T/s⟩`, of the image
of the integral closure `C` of `A⁺[T/s]` in `A(T/s)`, so the plus ring that `completedPlusSubring`
puts on the completed localization is the one `completionPlus` builds from `C` — the plus ring of
Wedhorn's Proposition 7.48. Neither definition is exposed outside the module that introduces it,
so neither side unfolds here and the agreement has to be stated rather than left to `rfl`. -/
theorem completedPlusSubring_eq_completionPlus (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    completedPlusSubring P Aplus T s S hden = completionPlus (integralClosure ↥(Algebra.adjoin Aplus
      (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  exact SetLike.coe_injective <| by
    rw [coe_completedPlusSubring, completionPlus_def,
      Completion.coe_topologicalClosure_map_coeRingHom, Subalgebra.coe_toSubring]

/-- **The adic spectrum of `A⟨T/s⟩` is the rational subset `R(T/s)`** — Wedhorn Proposition
8.2 (2), first assertion. Pullback along the structure map `A → A⟨T/s⟩` is a homeomorphism onto
`R(T/s)`.

It is the composite of the completion homeomorphism of Proposition 7.48, applied to the
topological localization `A(T/s)`, with `spaLocalizationHomeomorph`. The two `Homeomorph.setCongr`
steps cross `completedPlusSubring_eq_completionPlus`, which renames the plus ring, and
`locUniformSpace_toTopologicalSpace`, which moves the middle adic spectrum from the topology
`locUniformSpace` induces to `locTopology`; neither moves a point. -/
noncomputable def spaCompletedLocalizationHomeomorph (P : PairOfDefinition A) (Aplus : Subring A)
    (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    spa (completedPlusSubring P Aplus T s S hden) ≃ₜ
      (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) :=
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  (Homeomorph.setCongr (by rw [completedPlusSubring_eq_completionPlus])).trans <|
    (spaCompletionHomeomorph (integralClosure ↥(Algebra.adjoin Aplus
        (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring).trans <|
      (Homeomorph.setCongr (by rw [locUniformSpace_toTopologicalSpace])).trans
        (spaLocalizationHomeomorph P Aplus hP T s S hden)

/-- The homeomorphism is the canonical map `spaLocToRationalSubset`: pullback along the structure
map `ρ : A → A⟨T/s⟩`. This is what makes `spaCompletedLocalizationHomeomorph` a statement about
`A⟨T/s⟩` itself rather than about some homeomorphic replacement of it. -/
@[simp]
theorem spaCompletedLocalizationHomeomorph_apply (P : PairOfDefinition A) (Aplus : Subring A)
    (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ v : spa (completedPlusSubring P Aplus T s S hden),
      spaCompletedLocalizationHomeomorph P Aplus hP T s S hden v =
        spaLocToRationalSubset P Aplus T s S hden v := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  -- the structure map is the localisation map followed by the completion map, so pulling back
  -- along it is pulling back along the two in turn
  have hrho : toCompletionLoc P T s S hden = Completion.coeRingHom.comp (algebraMap A S) :=
    RingHom.ext (toCompletionLoc_apply P T s S hden)
  refine fun v ↦ Subtype.ext <| Subtype.ext ?_
  simp [spaCompletedLocalizationHomeomorph, hrho]

/-- The homeomorphism, as a function, is pullback along the structure map `ρ : A → A⟨T/s⟩`. This is
the functional companion of the pointwise `spaCompletedLocalizationHomeomorph_apply`, in the form
that rewrites under `Set.preimage` and `Set.image`. -/
@[simp]
theorem coe_spaCompletedLocalizationHomeomorph (P : PairOfDefinition A) (Aplus : Subring A)
    (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ⇑(spaCompletedLocalizationHomeomorph P Aplus hP T s S hden) =
      spaLocToRationalSubset P Aplus T s S hden :=
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  funext (spaCompletedLocalizationHomeomorph_apply P Aplus hP T s S hden)

end TauCeti.ValuationSpectrum

end
