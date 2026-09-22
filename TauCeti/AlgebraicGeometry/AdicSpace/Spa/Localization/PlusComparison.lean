/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PresentationIndependence
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Integral
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedHomeomorph

/-!
# The comparison map of a containment of rational subsets is a map of Huber pairs

For a containment `R(T'/s') ⊆ R(T/s)` of rational subsets of `Spa (A, A⁺)`,
`TauCeti.ValuationSpectrum.ringHomOfRationalSubsetSubset` is the unique continuous ring
homomorphism `σ : A⟨T/s⟩ → A⟨T'/s'⟩` compatible with the structure maps from `A`. It is so far a
map of rings only. This file makes it a map of *Huber pairs*: `σ` carries `A_U⁺` into `A_U'⁺`, so
it induces a map of adic spectra

```text
Spa (A⟨T'/s'⟩, A_U'⁺) → Spa (A⟨T/s⟩, A_U⁺)
```

in the other direction, and under the identifications of Wedhorn's Proposition 8.2(2) that map is
the inclusion `R(T'/s') ⊆ R(T/s)`.

Downstream, this is the stability of the plus structure under restriction to a smaller rational
subset. The plus rings `A_U⁺` are built one rational subset at a time, and the results here
relate two of them along a containment: `σ` carries `A_U⁺` into `A_U'⁺`. That is the form taken
by the condition "power-bounded, with all values `≤ 1`" on sections of the structure presheaf,
whose restriction maps along `R(T'/s') ⊆ R(T/s)` land in the plus ring of the smaller subset, so
that the sub-presheaf `𝒪_X⁺` they cut out is a presheaf of rings; and it is the upgrade of `σ`
from a map of rings to a map of Huber pairs that makes `comap σ` a map of adic spectra.

## Main definitions

All names below are in the `TauCeti.ValuationSpectrum` namespace.

* `pairHomOfRationalSubsetSubset` : the comparison map as a morphism of Huber pairs
  `(A⟨T/s⟩, A_U⁺) → (A⟨T'/s'⟩, A_U'⁺)`. The map of adic spectra is
  `TauCeti.Huber.Pair.Hom.spaComap` of this morphism; that generic construction and its API are
  used directly, with no specialised wrapper.

## Main results

* `comap_ringHomOfRationalSubsetSubset_mem_spa` : pullback along the comparison map takes points
  of `Spa (A⟨T'/s'⟩, A_U'⁺)` to points of `Spa (A⟨T/s⟩, A_U⁺)`.
* `ringHomOfRationalSubsetSubset_mem_completedPlusSubring` : the comparison map carries `A_U⁺`
  into `A_U'⁺`, so it is a map of Huber pairs.
* `toRingHom_pairHomOfRationalSubsetSubset` : the underlying ring homomorphism of the morphism of
  Huber pairs is the comparison map.
* `spaCompletedLocalizationHomeomorph_spaComap_pairHomOfRationalSubsetSubset` : across the
  homeomorphisms `Spa (A⟨T/s⟩, A_U⁺) ≃ₜ R(T/s)`, the induced map of adic spectra is the
  inclusion `R(T'/s') ⊆ R(T/s)`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Propositions 8.2 and 7.52.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Pullback along the comparison map lands in the adic spectrum of `A⟨T/s⟩`.** For a
containment `R(T'/s') ⊆ R(T/s)` of rational subsets, every point of `Spa (A⟨T'/s'⟩, A_U'⁺)` pulls
back along the comparison map `σ : A⟨T/s⟩ → A⟨T'/s'⟩` to a point of `Spa (A⟨T/s⟩, A_U⁺)`. -/
theorem comap_ringHomOfRationalSubsetSubset_mem_spa (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ w ∈ spa (completedPlusSubring P Aplus T' s' S' hden'),
      comap (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub) w ∈
        spa (completedPlusSubring P Aplus T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  intro w hw
  have hψ : ∀ a : A, ((ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden'
      hsub).comp Completion.coeRingHom) (algebraMap A S a) =
      toCompletionLoc P T' s' S' hden' a := fun a ↦ by
    rw [RingHom.comp_apply, Completion.coe_coeRingHom, ← toCompletionLoc_apply P T s S hden,
      ← RingHom.comp_apply, ringHomOfRationalSubsetSubset_comp_toCompletionLoc]
  have hfac : comap (toCompletionLoc P T' s' S' hden') w ∈ rationalSubset Aplus T s :=
    hsub (by simpa using spaComapLoc_mem_rationalSubset P Aplus T' s' S' hden' ⟨w, hw⟩)
  -- `s` is already inverted in `S` by the `IsLocalization.Away` binder, so its image is a unit
  have hu : IsUnit (toCompletionLoc P T' s' S' hden' s) :=
    hψ s ▸ (IsLocalization.Away.algebraMap_isUnit (S := S) s).map _
  have hcont := ((mem_spa_iff _ _).mp hw).1.comap
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub)
  rw [completedPlusSubring_eq_completionPlus, completionPlus_def, spa_topologicalClosure,
    mem_spa_map_iff Completion.continuous_coeRingHom _ hcont]
  refine (mem_spa_iff _ _).mpr ⟨hcont.comap Completion.continuous_coeRingHom, fun x hx ↦ ?_⟩
  simpa only [comap_vle, map_one, RingHom.comp_apply] using
    vle_one_of_mem_integralClosure_adjoin_plus Aplus T s S hψ
      (fun a ha ↦ ((mem_spa_iff _ _).mp hw).2 _
        (toCompletionLoc_mem_completedPlusSubring P Aplus T' s' S' hden' ha))
      hu (fun _ ↦ vle_one_of_comap_mem_rationalSubset hu hfac) hx

/-- **The comparison map is a map of Huber pairs** (Wedhorn's Proposition 8.2(1)): for a
containment `R(T'/s') ⊆ R(T/s)` of rational subsets, the comparison map
`σ : A⟨T/s⟩ → A⟨T'/s'⟩` carries `A_U⁺` into `A_U'⁺`. Together with
`continuous_ringHomOfRationalSubsetSubset` this makes `σ` a morphism of complete Huber pairs
`(A⟨T/s⟩, A_U⁺) → (A⟨T'/s'⟩, A_U'⁺)`. -/
theorem ringHomOfRationalSubsetSubset_mem_completedPlusSubring (P : PairOfDefinition A)
    (Aplus : Subring A)
    (hIplus : ∀ j : P.ringOfDefinition, j ∈ P.idealOfDefinition → (j : A) ∈ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ f ∈ completedPlusSubring P Aplus T s S hden,
      ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub f ∈
        completedPlusSubring P Aplus T' s' S' hden' := by
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P T' s' S' hden'
  have hB := isRingOfIntegralElements_completedPlusSubring P Aplus hIplus hAplus T' s' S' hden'
  have _ := hB.isIntegrallyClosedIn
  refine fun f hf ↦ mem_of_forall_vle_one hB.isOpen fun w hw ↦ ?_
  simpa only [comap_vle, map_one] using
    ((mem_spa_iff _ _).mp (comap_ringHomOfRationalSubsetSubset_mem_spa P Aplus hAplus
      T s S hden T' s' S' hden' hsub w hw)).2 f hf

/-- **The comparison map as a morphism of Huber pairs** (Wedhorn's Proposition 8.2(1)): the
comparison map `σ : A⟨T/s⟩ → A⟨T'/s'⟩` of a containment `R(T'/s') ⊆ R(T/s)`, bundled with its
continuity and with `ringHomOfRationalSubsetSubset_mem_completedPlusSubring` as a morphism
`(A⟨T/s⟩, A_U⁺) → (A⟨T'/s'⟩, A_U'⁺)` of Huber pairs.

The two Huber pairs are the plus rings `completedPlusSubring` together with
`TauCeti.Huber.PairOfDefinition.isRingOfIntegralElements_completedPlusSubring`; that is what
`hIplus` pays for, since it is the hypothesis making `A_U⁺` open.
`toRingHom_pairHomOfRationalSubsetSubset` recovers `σ`, and `TauCeti.Huber.Pair.Hom.spaComap` of
this morphism is the induced map `Spa (A⟨T'/s'⟩, A_U'⁺) → Spa (A⟨T/s⟩, A_U⁺)`, with the generic
`spaComap` API — its value, continuity and functoriality lemmas — applying to it unchanged. -/
noncomputable def pairHomOfRationalSubsetSubset (P : PairOfDefinition A) (Aplus : Subring A)
    (hIplus : ∀ j : P.ringOfDefinition, j ∈ P.idealOfDefinition → (j : A) ∈ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    letI := isHuberRing_completion_locTopology P T' s' S' hden'
    Huber.Pair.Hom
      ⟨completedPlusSubring P Aplus T s S hden,
        isRingOfIntegralElements_completedPlusSubring P Aplus hIplus hAplus T s S hden⟩
      ⟨completedPlusSubring P Aplus T' s' S' hden',
        isRingOfIntegralElements_completedPlusSubring P Aplus hIplus hAplus T' s' S' hden'⟩ :=
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_completion_locTopology P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
  letI := isHuberRing_completion_locTopology P T' s' S' hden'
  { toRingHom := ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub
    continuous_toRingHom :=
      continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub
    map_mem_plus := ringHomOfRationalSubsetSubset_mem_completedPlusSubring P Aplus hIplus hAplus
      T s S hden T' s' S' hden' hsub }

/-- The underlying ring homomorphism of `pairHomOfRationalSubsetSubset` is the comparison map. -/
@[simp]
theorem toRingHom_pairHomOfRationalSubsetSubset (P : PairOfDefinition A) (Aplus : Subring A)
    (hIplus : ∀ j : P.ringOfDefinition, j ∈ P.idealOfDefinition → (j : A) ∈ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    letI := isHuberRing_completion_locTopology P T' s' S' hden'
    (pairHomOfRationalSubsetSubset P Aplus hIplus hAplus T s S hden T' s' S' hden' hsub).toRingHom =
      ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub := (rfl)

/-- **The induced map of adic spectra is the inclusion of rational subsets.** Across the
homeomorphisms `Spa (A⟨T/s⟩, A_U⁺) ≃ₜ R(T/s)` of Wedhorn's Proposition 8.2(2), the map
`TauCeti.Huber.Pair.Hom.spaComap` of `pairHomOfRationalSubsetSubset` is the inclusion
`R(T'/s') ⊆ R(T/s)`. -/
theorem spaCompletedLocalizationHomeomorph_spaComap_pairHomOfRationalSubsetSubset
    (P : PairOfDefinition A)
    (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    letI := isHuberRing_completion_locTopology P T' s' S' hden'
    ∀ w : spa (completedPlusSubring P Aplus T' s' S' hden'),
      spaCompletedLocalizationHomeomorph P Aplus hP T s S hden
          ((pairHomOfRationalSubsetSubset P Aplus (fun j _ ↦ hP j.property) hAplus T s S hden
            T' s' S' hden' hsub).spaComap w) =
        Set.inclusion (Set.preimage_mono (f := Subtype.val) hsub)
          (spaCompletedLocalizationHomeomorph P Aplus hP T' s' S' hden' w) := by
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P T' s' S' hden'
  refine fun w ↦ Subtype.ext (Subtype.ext ?_)
  simp only [spaCompletedLocalizationHomeomorph_apply, spaLocToRationalSubset_val,
    spaComapLoc_val, Huber.Pair.Hom.spaComap_val, toRingHom_pairHomOfRationalSubsetSubset]
  rw [← Function.comp_apply (f := comap (toCompletionLoc P T s S hden)), ← comap_comp,
    ringHomOfRationalSubsetSubset_comp_toCompletionLoc]

end TauCeti.ValuationSpectrum
