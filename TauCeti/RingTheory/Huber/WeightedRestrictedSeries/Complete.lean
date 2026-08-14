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

Over a Hausdorff nonarchimedean ring `A`, the ordinary restricted power-series ring — the
weighted ring `TauCeti.Huber.weightedRestrictedSubring` at the trivial weight family — is
itself Hausdorff, and over a complete uniform `A` it is complete. At trivial weights
`Tν · U = U` (`TauCeti.Huber.weightMul_one_weight`), so the coefficient maps are continuous,
and uniformly continuous once `A` carries a uniformity: points are separated coefficientwise,
and a Cauchy filter of restricted series is coefficientwise Cauchy, its coefficientwise limit
is restricted, and the filter converges to it. Both facts are the trivial-weight case of
Wedhorn's Proposition 5.49 (*Adic Spaces*, arXiv:1910.05934v1) — Hausdorffness is its part
(2), and completeness is the step its part (3) is proved by, the one that then identifies
`A⟨X⟩_T` with the completion of `A[X]_T`. Its part (1), density of the polynomials, is
`TauCeti.Huber.dense_weightedPolynomials` in the parent module. The weighted case of (2) and
(3) needs bounded weights and is not treated here.

Hausdorffness is purely topological — it uses only continuity of the coefficient maps — so it
is proved in a section over a nonarchimedean ring with no uniformity of its own, which is the
setting the rest of the Huber development works in; the uniform hypotheses on `A` enter only
with completeness.

Consequently `TauCeti.Huber.restrictedMvPowerSeriesCompletion k A` collapses:
`TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` identifies `A⟨X₁,…,Xₖ⟩` with the
plain restricted-series ring — the "comparison with the usual completed restricted
power-series algebra" milestone of roadmap Layer 0.5. Its hypotheses are completeness and
Hausdorffness of that ring itself rather than of `A`, which the instances here supply over a
complete Hausdorff base and which hold over a discrete base too, so that the comparison also
covers `TauCeti.Huber.IsStronglyNoetherian.of_discreteTopology`. It is packaged twice over
one and the same underlying map — as that ring isomorphism and as the `A`-algebra equivalence
`TauCeti.Huber.restrictedMvPowerSeriesCompletionAlgEquiv`, the two tied together by
`TauCeti.Huber.coe_restrictedMvPowerSeriesCompletionAlgEquiv` and
`TauCeti.Huber.coe_restrictedMvPowerSeriesCompletionAlgEquiv_symm` — and both it and its
inverse are uniformly continuous, hence continuous by `UniformContinuous.continuous`. Nothing
in that block is special to restricted series: every declaration in it specializes a generic
statement about `UniformSpace.Completion.completeRingEquivSelf` proved in
`TauCeti.Topology.Algebra.UniformRing`.

The completeness proof names its one definitional step — that the subring's uniformity is the
one its subgroup basis induces — as a `private` lemma, so that the argument does not silently
depend on the two being reducibly equal. It is private because it is a specialization of
Mathlib's `AddGroupFilterBasis.cauchy_iff` with a single use here, not new API.

## Main results

* `TauCeti.Huber.continuous_coeff_one_weight` and
  `TauCeti.Huber.uniformContinuous_coeff_one_weight` : at trivial weights the coefficient
  maps are continuous, and uniformly continuous over a uniform base.
* `TauCeti.Huber.t0Space_weightedRestrictedSubring_one_weight` : the restricted series over a
  Hausdorff base are Hausdorff.
* `TauCeti.Huber.completeSpace_weightedRestrictedSubring_one_weight` : the restricted series
  over a complete base are complete.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` : the comparison — `A⟨X₁,…,Xₖ⟩` is
  the plain restricted-series ring, whenever that ring is complete and Hausdorff.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionAlgEquiv` : the same comparison as an
  `A`-algebra equivalence.
* `TauCeti.Huber.uniformContinuous_restrictedMvPowerSeriesCompletionEquiv` and
  `TauCeti.Huber.uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm` : the
  comparison and its inverse are uniformly continuous. The inverse is the canonical map into
  the completion, which is `TauCeti.Huber.coe_restrictedMvPowerSeriesCompletionEquiv_symm`.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) is the roadmap's designated prior
formalisation for this row. At commit `2baa76f742bdb4fb8ee323fabba41203bd390e08` its file
`projects/AdicSpaces/Adic spaces/RestrictedPowerSeries.lean` states nothing about
completeness, Hausdorffness, or the completion of the restricted-series ring, so there was
nothing to port here; nothing was copied.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.49(2) and (3), at the trivial —
  hence bounded — weight family `Tᵢ = {1}`.
-/

public section

namespace TauCeti.Huber

open Filter

/-! ### The coefficient maps and Hausdorffness

Neither fact needs a uniformity on `A`: they hold over any nonarchimedean topological ring,
which is how `A` is fixed throughout the rest of the Huber development. -/

section Topology

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- At the trivial weight family the coefficient maps of `A⟨X⟩` are continuous: the
neighbourhood subgroup `U⟨X⟩` maps into `U` coefficientwise. -/
theorem continuous_coeff_one_weight (ν : Fin k →₀ ℕ) :
    Continuous fun f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) := by
  refine continuous_of_continuousAt_zero (AddMonoidHom.mk'
    (fun f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ↦
      MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)) fun _ _ ↦ by simp) ?_
  rw [ContinuousAt, map_zero,
    (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).tendsto_left_iff]
  intro V hV
  obtain ⟨U, hUV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
  exact ⟨U, trivial, fun f hf ↦ hUV (by simpa using mem_weightedNhd.mp hf ν)⟩

/-- **Restricted series over a Hausdorff base are Hausdorff** (Wedhorn 5.49(2) at the trivial
weight family): points are separated coefficientwise. -/
instance t0Space_weightedRestrictedSubring_one_weight [T0Space A] :
    T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :=
  t0Space_of_injective_of_continuous
    (f := fun f ν ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A))
    (fun _ _ h ↦ Subtype.ext (MvPowerSeries.ext fun ν ↦ congrFun h ν))
    (continuous_pi fun ν ↦ continuous_coeff_one_weight ν)

/-- **A Cauchy filter on `A⟨X⟩_T` is uniformly Cauchy on each defining subgroup.** This is
Mathlib's `AddGroupFilterBasis.cauchy_iff` at the basis `weightedNhd_subgroups_basis`
registers, and it exists to name that step once: the uniformity carried by
`weightedRestrictedSubring` and the one the filter basis induces are the same structure, but
only definitionally, and the completeness proof below should not depend on that unfolding. -/
private theorem exists_mem_forall_sub_mem_weightedNhd {T : Fin k → Set A} {hT : IsWeightFamily T}
    {F : Filter (weightedRestrictedSubring T hT)} (hF : Cauchy F) (U : OpenAddSubgroup A) :
    ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), y - x ∈ weightedNhd T hT U.toAddSubgroup :=
  ((weightedNhd_subgroups_basis hT).toRingFilterBasis.toAddGroupFilterBasis.cauchy_iff.mp hF).2 _
    ((weightedNhd_subgroups_basis hT).mem_addGroupFilterBasis U)

end Topology

/-! ### Completeness -/

section Uniform

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A]

/-- At the trivial weight family the coefficient maps of `A⟨X⟩` are uniformly continuous:
they are continuous additive group homomorphisms. -/
theorem uniformContinuous_coeff_one_weight (ν : Fin k →₀ ℕ) :
    UniformContinuous fun f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) :=
  uniformContinuous_addMonoidHom_of_continuous (f := AddMonoidHom.mk'
    (fun f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ↦
      MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)) fun _ _ ↦ by simp)
    (continuous_coeff_one_weight ν)

/-- **The trivial-weight restricted-series subring is complete** whenever the base uniform
nonarchimedean commutative ring is complete. This is the step Wedhorn 5.49(3) is proved by. -/
instance completeSpace_weightedRestrictedSubring_one_weight [CompleteSpace A] :
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

end Uniform

/-! ### The comparison with `A⟨X₁,…,Xₖ⟩`

The hypotheses are completeness and Hausdorffness of the restricted-series ring itself, not
of `A`: the instances above supply them over a complete Hausdorff base, and over a discrete
base they hold because the ring is then discrete. Each declaration specializes a generic
statement about `UniformSpace.Completion.completeRingEquivSelf`. -/

section Comparison

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CompleteSpace (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
    isWeightFamily_one_weight)]
  [T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)]

variable (k A) in
/-- **The comparison equivalence of roadmap Layer 0.5**: when the plain restricted-series ring
is complete and Hausdorff, the completed restricted power-series algebra `A⟨X₁,…,Xₖ⟩` is that
ring. -/
noncomputable def restrictedMvPowerSeriesCompletionEquiv :
    restrictedMvPowerSeriesCompletion k A ≃+*
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  UniformSpace.Completion.completeRingEquivSelf _

@[simp]
theorem restrictedMvPowerSeriesCompletionEquiv_coe
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedMvPowerSeriesCompletionEquiv k A (f : restrictedMvPowerSeriesCompletion k A)
      = f :=
  UniformSpace.Completion.completeRingEquivSelf_coe _ f

@[simp]
theorem restrictedMvPowerSeriesCompletionEquiv_symm_apply
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    (restrictedMvPowerSeriesCompletionEquiv k A).symm f
      = (f : restrictedMvPowerSeriesCompletion k A) :=
  UniformSpace.Completion.completeRingEquivSelf_symm_apply _ f

/-- The inverse comparison **is** the canonical map into the completion, as a function. -/
theorem coe_restrictedMvPowerSeriesCompletionEquiv_symm :
    ⇑(restrictedMvPowerSeriesCompletionEquiv k A).symm
      = ((↑) : _ → restrictedMvPowerSeriesCompletion k A) :=
  UniformSpace.Completion.coe_completeRingEquivSelf_symm _

/-- The comparison is uniformly continuous: it is the uniform bijection between a complete
Hausdorff space and its completion. -/
theorem uniformContinuous_restrictedMvPowerSeriesCompletionEquiv :
    UniformContinuous ⇑(restrictedMvPowerSeriesCompletionEquiv k A) :=
  UniformSpace.Completion.uniformContinuous_completeRingEquivSelf _

/-- The inverse comparison is uniformly continuous: it is the canonical map into the
completion. -/
theorem uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm :
    UniformContinuous ⇑(restrictedMvPowerSeriesCompletionEquiv k A).symm :=
  UniformSpace.Completion.uniformContinuous_completeRingEquivSelf_symm _

variable (k A) in
/-- **The comparison as an `A`-algebra equivalence**: the same identification, structure map
included. It is `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` rebundled, so the two
share an underlying map and the coercion lemmas for the latter apply to it. -/
noncomputable def restrictedMvPowerSeriesCompletionAlgEquiv :
    restrictedMvPowerSeriesCompletion k A ≃ₐ[A]
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  UniformSpace.Completion.completeAlgEquivSelf _ A

@[simp]
theorem coe_restrictedMvPowerSeriesCompletionAlgEquiv :
    ⇑(restrictedMvPowerSeriesCompletionAlgEquiv k A)
      = ⇑(restrictedMvPowerSeriesCompletionEquiv k A) :=
  UniformSpace.Completion.coe_completeAlgEquivSelf _ A

@[simp]
theorem coe_restrictedMvPowerSeriesCompletionAlgEquiv_symm :
    ⇑(restrictedMvPowerSeriesCompletionAlgEquiv k A).symm
      = ⇑(restrictedMvPowerSeriesCompletionEquiv k A).symm :=
  UniformSpace.Completion.coe_completeAlgEquivSelf_symm _ A

end Comparison

end TauCeti.Huber
