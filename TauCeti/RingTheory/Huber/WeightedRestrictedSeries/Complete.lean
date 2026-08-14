/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion
public import TauCeti.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.UniformFilterBasis

/-!
# Completeness of the restricted power series over a complete base

Over a complete Hausdorff uniform ring `A`, the ordinary restricted power-series ring — the
weighted ring `TauCeti.Huber.weightedRestrictedSubring` at the trivial weight family — is
itself complete and Hausdorff. At trivial weights `Tν · U = U`
(`TauCeti.Huber.weightMul_one_weight`), so the coefficient maps are uniformly continuous: a
Cauchy filter of restricted series is coefficientwise Cauchy, its coefficientwise limit is
restricted, and the filter converges to it. This is the trivial-weight case of Wedhorn's
completeness statement for `A⟨X⟩_T` (*Adic Spaces*, arXiv:1910.05934v1, 5.49); the weighted
case needs bounded weights and is not treated here.

Consequently `TauCeti.Huber.restrictedMvPowerSeriesCompletion k A` collapses for such `A`:
`TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` identifies `A⟨X₁,…,Xₖ⟩` with the
plain restricted-series ring — the "comparison with the usual completed restricted
power-series algebra" milestone of roadmap Layer 0.5. It is packaged twice over one and the
same underlying map — as that ring isomorphism and as the `A`-algebra equivalence
`TauCeti.Huber.restrictedMvPowerSeriesCompletionAlgEquiv`, the two tied together by
`TauCeti.Huber.coe_restrictedMvPowerSeriesCompletionAlgEquiv` and
`TauCeti.Huber.coe_restrictedMvPowerSeriesCompletionAlgEquiv_symm` — and both it and its
inverse are uniformly continuous, hence continuous by `UniformContinuous.continuous`.

## Main results

* `TauCeti.Huber.uniformContinuous_coeff_one_weight` : at trivial weights the coefficient
  maps are uniformly continuous.
* `TauCeti.Huber.instT0Space_one_weight` : the restricted series over a Hausdorff base are
  Hausdorff.
* `TauCeti.Huber.exists_mem_forall_sub_mem_weightedNhd` : a Cauchy filter on `A⟨X⟩_T` is
  uniformly Cauchy on each defining subgroup — the step that identifies the subring's
  uniformity with the one its subgroup basis induces.
* `TauCeti.Huber.instCompleteSpace_one_weight` : the restricted series over a complete base
  are complete.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` : the comparison —
  `A⟨X₁,…,Xₖ⟩` is the plain restricted-series ring over a complete Hausdorff base.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionAlgEquiv` : the same comparison as an
  `A`-algebra equivalence.
* `TauCeti.Huber.uniformContinuous_restrictedMvPowerSeriesCompletionEquiv` and
  `TauCeti.Huber.uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm` : the
  comparison and its inverse are uniformly continuous. The inverse is the canonical map into
  the completion, which is `TauCeti.Huber.coe_restrictedMvPowerSeriesCompletionEquiv_symm`.
-/

public section

namespace TauCeti.Huber

open Filter

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A]

/-- At the trivial weight family the coefficient maps of `A⟨X⟩` are uniformly continuous:
the neighbourhood subgroup `U⟨X⟩` maps into `U` coefficientwise. -/
theorem uniformContinuous_coeff_one_weight (ν : Fin k →₀ ℕ) :
    UniformContinuous fun f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) := by
  refine uniformContinuous_addMonoidHom_of_continuous (f := AddMonoidHom.mk'
    (fun f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ↦
      MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)) fun _ _ ↦ by simp) ?_
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero,
    (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).tendsto_left_iff]
  intro V hV
  obtain ⟨U, hUV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
  exact ⟨U, trivial, fun f hf ↦ hUV (by simpa using mem_weightedNhd.mp hf ν)⟩

/-- Restricted series over a Hausdorff base are Hausdorff: points are separated
coefficientwise. -/
instance instT0Space_one_weight [T0Space A] :
    T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :=
  t0Space_of_injective_of_continuous
    (f := fun f ν ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A))
    (fun _ _ h ↦ Subtype.ext (MvPowerSeries.ext fun ν ↦ congrFun h ν))
    (continuous_pi fun ν ↦ (uniformContinuous_coeff_one_weight ν).continuous)

omit [IsUniformAddGroup A] in
/-- **A Cauchy filter on `A⟨X⟩_T` is uniformly Cauchy on each defining subgroup.** This is
Mathlib's `AddGroupFilterBasis.cauchy_iff` at the basis `weightedNhd_subgroups_basis`
registers, and it exists to name that step once: the uniformity carried by
`weightedRestrictedSubring` and the one the filter basis induces are the same structure, but
only definitionally, and the completeness proof below should not depend on that unfolding. -/
theorem exists_mem_forall_sub_mem_weightedNhd {T : Fin k → Set A} {hT : IsWeightFamily T}
    {F : Filter (weightedRestrictedSubring T hT)} (hF : Cauchy F) (U : OpenAddSubgroup A) :
    ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), y - x ∈ weightedNhd T hT U.toAddSubgroup :=
  ((weightedNhd_subgroups_basis hT).toRingFilterBasis.toAddGroupFilterBasis.cauchy_iff.mp hF).2 _
    ((weightedNhd_subgroups_basis hT).mem_addGroupFilterBasis U)

/-- The trivial-weight restricted-series subring has a `CompleteSpace` instance whenever the
base uniform nonarchimedean commutative ring is complete. -/
instance instCompleteSpace_one_weight [CompleteSpace A] :
    CompleteSpace (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) := by
  refine ⟨fun {F} hF ↦ ?_⟩
  have : F.NeBot := hF.1
  choose a ha using fun ν ↦ CompleteSpace.complete
    (hF.map (uniformContinuous_coeff_one_weight (A := A) ν))
  obtain ⟨g, hg⟩ : ∃ g : MvPowerSeries (Fin k) A, ∀ ν, MvPowerSeries.coeff ν g = a ν :=
    ⟨a, fun ν ↦ MvPowerSeries.coeff_apply a ν⟩
  -- Every open subgroup `U` has an `F`-set all of whose coefficients are `U`-close to `g`.
  have key : ∀ U : OpenAddSubgroup A, ∃ t ∈ F, ∀ f ∈ t, ∀ ν,
      MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) - a ν ∈ U := by
    intro U
    obtain ⟨t, htF, ht⟩ := exists_mem_forall_sub_mem_weightedNhd hF U
    refine ⟨t, htF, fun f hf ν ↦ ?_⟩
    have h : a ν - MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ U :=
      U.isClosed.mem_of_tendsto (Filter.Tendsto.sub (ha ν) tendsto_const_nhds)
        (Filter.eventually_of_mem htF fun f' hf' ↦ by
          simpa using mem_weightedNhd.mp (ht f hf f' hf') ν)
    simpa using neg_mem h
  -- The coefficientwise limit is again restricted, since it is `U`-close to a restricted series.
  have hres : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) g := by
    rw [isWeightedRestricted_iff]
    intro U
    obtain ⟨t, htF, ht⟩ := key U
    obtain ⟨f₀, hf₀⟩ := hF.1.nonempty_of_mem htF
    filter_upwards [isWeightedRestricted_iff.mp (mem_weightedRestrictedSubring.mp f₀.2) U] with ν hν
    have h₀ : MvPowerSeries.coeff ν (f₀ : MvPowerSeries (Fin k) A) ∈ U := by simpa using hν
    simpa [hg] using sub_mem h₀ (ht f₀ hf₀ ν)
  refine ⟨⟨g, mem_weightedRestrictedSubring.mpr hres⟩, ?_⟩
  rw [← tendsto_id', ← tendsto_sub_nhds_zero_iff,
    (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).tendsto_right_iff]
  intro U _
  obtain ⟨t, htF, ht⟩ := key U
  filter_upwards [htF] with f hf
  rw [SetLike.mem_coe, mem_weightedNhd]
  intro ν
  simpa [map_sub, hg] using ht f hf ν

/-- **The comparison equivalence of roadmap Layer 0.5**: over a complete Hausdorff base the
completed restricted power-series algebra is the plain restricted-series ring. -/
noncomputable def restrictedMvPowerSeriesCompletionEquiv (k : ℕ) (A : Type*) [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
    [T0Space A] :
    restrictedMvPowerSeriesCompletion k A ≃+*
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  UniformSpace.Completion.completeRingEquivSelf _

@[simp]
theorem restrictedMvPowerSeriesCompletionEquiv_coe {k : ℕ} {A : Type*} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
    [T0Space A]
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedMvPowerSeriesCompletionEquiv k A (f : restrictedMvPowerSeriesCompletion k A)
      = f :=
  UniformSpace.Completion.completeRingEquivSelf_coe _ f

@[simp]
theorem restrictedMvPowerSeriesCompletionEquiv_symm_apply {k : ℕ} {A : Type*} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
    [T0Space A]
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    (restrictedMvPowerSeriesCompletionEquiv k A).symm f
      = (f : restrictedMvPowerSeriesCompletion k A) :=
  UniformSpace.Completion.completeRingEquivSelf_symm_apply _ f

/-- **The comparison as an `A`-algebra equivalence**: over a complete Hausdorff base the
completed restricted power-series algebra is the plain restricted-series ring, structure map
included. It is `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` rebundled, so the two
share an underlying map and the coercion lemmas for the latter apply to it. -/
noncomputable def restrictedMvPowerSeriesCompletionAlgEquiv (k : ℕ) (A : Type*) [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
    [T0Space A] :
    restrictedMvPowerSeriesCompletion k A ≃ₐ[A]
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  AlgEquiv.ofRingEquiv (f := restrictedMvPowerSeriesCompletionEquiv k A) fun a ↦ by
    rw [UniformSpace.Completion.algebraMap_def]
    exact restrictedMvPowerSeriesCompletionEquiv_coe _

@[simp]
theorem coe_restrictedMvPowerSeriesCompletionAlgEquiv {k : ℕ} {A : Type*} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
    [T0Space A] :
    ⇑(restrictedMvPowerSeriesCompletionAlgEquiv k A)
      = ⇑(restrictedMvPowerSeriesCompletionEquiv k A) := (rfl)

@[simp]
theorem coe_restrictedMvPowerSeriesCompletionAlgEquiv_symm {k : ℕ} {A : Type*} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
    [T0Space A] :
    ⇑(restrictedMvPowerSeriesCompletionAlgEquiv k A).symm
      = ⇑(restrictedMvPowerSeriesCompletionEquiv k A).symm := (rfl)

/-- The comparison is uniformly continuous: composing it with the uniformly inducing map into
the completion gives back the identity. -/
theorem uniformContinuous_restrictedMvPowerSeriesCompletionEquiv {k : ℕ} {A : Type*} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
    [T0Space A] :
    UniformContinuous ⇑(restrictedMvPowerSeriesCompletionEquiv k A) := by
  have h : ((↑) : _ → restrictedMvPowerSeriesCompletion k A) ∘
      ⇑(restrictedMvPowerSeriesCompletionEquiv k A) = id := funext fun x ↦
    (restrictedMvPowerSeriesCompletionEquiv_symm_apply _).symm.trans
      ((restrictedMvPowerSeriesCompletionEquiv k A).symm_apply_apply x)
  rw [(UniformSpace.Completion.isUniformInducing_coe _).uniformContinuous_iff, h]
  exact uniformContinuous_id

/-- The inverse comparison **is** the canonical map into the completion, as a function. -/
theorem coe_restrictedMvPowerSeriesCompletionEquiv_symm {k : ℕ} {A : Type*} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
    [T0Space A] :
    ⇑(restrictedMvPowerSeriesCompletionEquiv k A).symm
      = ((↑) : _ → restrictedMvPowerSeriesCompletion k A) :=
  funext restrictedMvPowerSeriesCompletionEquiv_symm_apply

/-- The inverse comparison is uniformly continuous: it is the canonical map into the
completion. -/
theorem uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm {k : ℕ} {A : Type*}
    [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
    [T0Space A] :
    UniformContinuous ⇑(restrictedMvPowerSeriesCompletionEquiv k A).symm := by
  rw [coe_restrictedMvPowerSeriesCompletionEquiv_symm]
  exact UniformSpace.Completion.uniformContinuous_coe _

end TauCeti.Huber
