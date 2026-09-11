/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Surjective
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Support

/-!
# Standard rational families that cover the adic spectrum

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Corollary 7.53.**

For a finite subset `T` of a complete Hausdorff Huber pair `(A, A⁺)`, the standard rational
family `(R(T/t))_{t ∈ T}` is a covering of `Spa (A, A⁺)` exactly when `T` generates the unit
ideal:

```text
Ideal.span T = ⊤  ↔  Spa (A, A⁺) = ⋃ t ∈ T, R(T/t).
```

The `→` direction holds over an arbitrary commutative ring and is
`TauCeti.ValuationSpectrum.spa_eq_biUnion_rationalSubset_of_span_eq_top`. The `←` direction is
the one that needs the pair: a point of the cover is nonzero on some `t ∈ T`, so no point of the
spectrum kills all of `T`, and the support criterion
`TauCeti.ValuationSpectrum.span_eq_top_iff_forall_mem_spa_exists_notMem_supp` turns that into the
spanning statement. Completeness enters only through that criterion.

## Main results

* `TauCeti.ValuationSpectrum.span_eq_top_of_spa_eq_biUnion_rationalSubset` : the `←` direction.
* `TauCeti.ValuationSpectrum.span_eq_top_iff_spa_eq_biUnion_rationalSubset` : **Wedhorn Corollary
  7.53**, the two directions together.
* `TauCeti.ValuationSpectrum.exists_smul_top_ne_top_of_isMaximal` : no maximal ideal of `A`
  expands every member of a rational cover.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Corollary 7.53.

## Provenance

Developed here; nothing is ported.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [IsHuberRing A]

/-- **The converse half of Wedhorn Corollary 7.53.** If the standard rational family
`(R(T/t))_{t ∈ T}` covers `Spa (A, A⁺)` for a complete Hausdorff Huber pair, then `T` generates
the unit ideal. -/
theorem span_eq_top_of_spa_eq_biUnion_rationalSubset (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) {T : Finset A}
    (hcov : spa Aplus = ⋃ t ∈ T, rationalSubset Aplus T t) :
    Ideal.span (T : Set A) = ⊤ := by
  refine (span_eq_top_iff_forall_mem_spa_exists_notMem_supp Aplus hplus).mpr fun v hv ↦ ?_
  obtain ⟨t, ht, hmem⟩ := Set.mem_iUnion₂.mp (hcov ▸ hv)
  exact ⟨t, ht, fun hsupp ↦
    ((mem_rationalSubset_iff Aplus T t v).mp hmem).2.2 ((mem_supp_iff v t).mp hsupp)⟩

/-- **Wedhorn Corollary 7.53.** A finite set `T` in a complete Hausdorff Huber pair generates the
unit ideal exactly when the standard family `(R(T/t))_{t ∈ T}` covers `Spa (A, A⁺)`. -/
theorem span_eq_top_iff_spa_eq_biUnion_rationalSubset (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) {T : Finset A} :
    Ideal.span (T : Set A) = ⊤ ↔ spa Aplus = ⋃ t ∈ T, rationalSubset Aplus T t :=
  ⟨spa_eq_biUnion_rationalSubset_of_span_eq_top Aplus,
    span_eq_top_of_spa_eq_biUnion_rationalSubset Aplus hplus⟩

/-- **No maximal ideal expands every piece of a rational cover.** For a cover
`(R(T/t))_{t ∈ T}` — that is, `T` generating the unit ideal — and a maximal ideal `𝔪` of `A`,
some member of the cover has `𝔪 · A_t ≠ A_t`.

The maximal ideal is the support of a point of `Spa (A, A⁺)`
(`exists_mem_spa_supp_eq_of_isMaximal`), that point lies in some member of the cover
(`spa_eq_biUnion_rationalSubset_of_span_eq_top`), and a point's support does not expand the
piece containing it (`smul_top_ne_top_of_supp_eq_of_mem_rationalSubset`).

This is exactly the hypothesis of `Module.FaithfullyFlat.pi_of_exists_submodule_ne_top`, so it
is what a rational cover contributes to the faithful flatness in Wedhorn's Corollary 8.32. The
flatness of each `A → A_t`, which that criterion also needs, is a separate matter. -/
theorem exists_smul_top_ne_top_of_isMaximal (P : PairOfDefinition A) (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (hP : P.ringOfDefinition ≤ Aplus) {T : Finset A}
    (hT : Ideal.span (T : Set A) = ⊤) (S : ∀ _ : T, Type*) [∀ t : T, CommRing (S t)]
    [∀ t : T, Algebra A (S t)] [∀ t : T, IsLocalization.Away (t : A) (S t)]
    (hden : ∀ t : T, HasDenominatorPower P T (t : A) (S t)) (𝔪 : Ideal A) [𝔪.IsMaximal] :
    ∃ t : T, 𝔪 • (⊤ : Submodule A (S t)) ≠ ⊤ := by
  obtain ⟨v, hv, hsupp⟩ := exists_mem_spa_supp_eq_of_isMaximal Aplus hplus 𝔪
  rw [spa_eq_biUnion_rationalSubset_of_span_eq_top Aplus hT] at hv
  obtain ⟨t, ht, hvt⟩ := Set.mem_iUnion₂.mp hv
  refine ⟨⟨t, ht⟩, ?_⟩
  exact smul_top_ne_top_of_supp_eq_of_mem_rationalSubset P Aplus hP T ((⟨t, ht⟩ : T) : A)
    (S ⟨t, ht⟩) (hden ⟨t, ht⟩) hsupp hvt

end TauCeti.ValuationSpectrum

end
