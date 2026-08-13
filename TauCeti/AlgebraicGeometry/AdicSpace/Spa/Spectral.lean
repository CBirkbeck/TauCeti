/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Cont.OfIdeal
public import TauCeti.AlgebraicGeometry.AdicSpace.SpvOfIdeal.Spectral

/-!
# The adic spectrum is spectral: Wedhorn's Theorem 7.35

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Theorem 7.35.**

`Spa (A, A⁺)` is pro-constructible in `Spv (A, IA)` and is therefore a spectral space: by
Theorem 7.10 its trace on the subspace is the intersection of the trace of `Cont A` — closed
there, by Corollary 7.12 — with the trace of the sub-unit locus of `A⁺`, pro-constructible by
`isProConstructible_val_preimage_setOfPred_forall_vle_one`, and pro-constructible subspaces
of spectral spaces are spectral.

Neither trace statement descends from `Spv A`: the inclusion `Spv (A, I) → Spv A` is not
spectral, which is exactly why the two inputs are proved on the subspace side.

## Main results

* `TauCeti.ValuationSpectrum.spa_subset_spvOfIdeal` : `Spa (A, A⁺) ⊆ Spv (A, IA)`.
* `TauCeti.ValuationSpectrum.isProConstructible_val_preimage_spa` : **Theorem 7.35**, the
  pro-constructibility of `Spa (A, A⁺)` in `Spv (A, IA)`.
* `TauCeti.ValuationSpectrum.spectralSpace_spa` : **Theorem 7.35**, the conclusion:
  `Spa (A, A⁺)` is a spectral space.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- `Spa (A, A⁺) ⊆ Spv (A, IA)`: the adic spectrum consists of continuous points, and
continuous points lie in `Spv (A, IA)` (Theorem 7.10's inclusion). -/
theorem spa_subset_spvOfIdeal (P : PairOfDefinition A) (Aplus : Subring A) :
    spa Aplus ⊆ spvOfIdeal P.extendedIdealOfDefinition
      ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩ :=
  (spa_def Aplus ▸ Set.inter_subset_left).trans
    (cont_subset_spvOfIdeal_extendedIdealOfDefinition P)

/-- **Wedhorn Theorem 7.35, the pro-constructibility**: the trace of `Spa (A, A⁺)` on
`Spv (A, IA)` is pro-constructible — the intersection of the closed trace of `Cont A`
(Corollary 7.12) with the pro-constructible trace of the sub-unit locus of `A⁺`. -/
theorem isProConstructible_val_preimage_spa (P : PairOfDefinition A) (Aplus : Subring A) :
    IsProConstructible (Subtype.val ⁻¹' spa Aplus :
      Set (spvOfIdeal P.extendedIdealOfDefinition
        ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩)) := by
  have := spectralSpace_spvOfIdeal P.extendedIdealOfDefinition
    ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩
  rw [spa_def, Set.preimage_inter]
  exact (isClosed_val_preimage_cont P).isProConstructible.inter
    (isProConstructible_val_preimage_setOfPred_forall_vle_one _ _ (Aplus : Set A))

/-- **Wedhorn Theorem 7.35**: the adic spectrum `Spa (A, A⁺)` is a spectral space. Its trace
on the spectral space `Spv (A, IA)` is pro-constructible, pro-constructible subspaces of
spectral spaces are spectral, and `Spa (A, A⁺)` is homeomorphic to that trace. -/
theorem spectralSpace_spa (P : PairOfDefinition A) (Aplus : Subring A) :
    SpectralSpace (spa Aplus) := by
  have := spectralSpace_spvOfIdeal P.extendedIdealOfDefinition
    ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩
  have := (isProConstructible_val_preimage_spa P Aplus).spectralSpace
  -- Subtype of a subtype is a subtype: both sides carry the topology induced from `Spv A`.
  let e : (Subtype.val ⁻¹' spa Aplus : Set (spvOfIdeal P.extendedIdealOfDefinition
      ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩)) ≃ₜ spa Aplus :=
    { toFun := fun x ↦ ⟨x.1.1, x.2⟩
      invFun := fun v ↦ ⟨⟨v.1, spa_subset_spvOfIdeal P Aplus v.2⟩, v.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  -- `Topology.IsOpenEmbedding.spectralSpace` transfers along `e`, once `e` has carried
  -- compactness across; a homeomorphism is in particular an open embedding.
  have : CompactSpace (spa Aplus) := e.compactSpace
  exact e.symm.isOpenEmbedding.spectralSpace

end TauCeti.ValuationSpectrum
