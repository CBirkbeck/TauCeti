/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries
public import TauCeti.Topology.Algebra.UniformRing
public import TauCeti.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Strong noetherianness of a nonarchimedean ring

The completed restricted power-series algebras `A⟨X₁,…,Xₖ⟩` of a nonarchimedean commutative
ring `A`, and the predicate they support: `A` is *strongly noetherian* when every one of them
is noetherian. This is the hypothesis of Wedhorn's Theorem 8.28 (*Adic Spaces*,
arXiv:1910.05934v1) — the strongly noetherian form of Tate acyclicity — which Wedhorn states
for Tate rings; the predicate itself needs only the nonarchimedean topology, so it is stated
here in that generality.

`A` is not assumed complete or Hausdorff: following the roadmap, `A⟨X₁,…,Xₖ⟩` is *defined* as
the separated completion of the ring `TauCeti.Huber.weightedRestrictedSubring` of restricted
power series at the trivial weight family `Tᵢ = {1}` (Wedhorn Example 5.54), so for zero
variables it is the separated completion of `A` itself. Being a completion, it is a complete
Hausdorff topological `A`-algebra, with all of that structure found by instance search.

## Main definitions

* `TauCeti.Huber.restrictedMvPowerSeriesCompletion`: the completed restricted power-series
  algebra `A⟨X₁,…,Xₖ⟩`.
* `TauCeti.Huber.IsStronglyNoetherian`: every `A⟨X₁,…,Xₖ⟩` is a noetherian ring.
* `TauCeti.Huber.weightedRestrictedSubringFinZeroEquiv` and
  `TauCeti.Huber.restrictedMvPowerSeriesCompletionFinZeroEquiv`: the zero-variable
  identifications, of the restricted-series ring with `A` and of `A⟨⟩` with `Â`.

## Main results

* `TauCeti.Huber.continuous_algebraMap_restrictedMvPowerSeriesCompletion`: the structure map
  `A → A⟨X₁,…,Xₖ⟩` is continuous.
* `TauCeti.Huber.IsStronglyNoetherian.of_discreteTopology`: a noetherian ring with the
  discrete topology is strongly noetherian — over a discrete ring the restricted series are
  the polynomials, already complete, and the Hilbert basis theorem applies. In particular
  `ℤ`, every field, and every noetherian ring discretely topologised witness the predicate.
* `TauCeti.Huber.isNoetherianRing_completion_of_isStronglyNoetherian`: at zero variables the
  predicate says exactly that the separated completion `Â` is noetherian. The identification
  behind it is topological, not merely a ring isomorphism: the weight at `k = 0` is the empty
  product, so `Tν · U` is `U` and the two neighbourhood bases correspond.

The second half of that roadmap sentence — that `A` itself is noetherian when it is already
complete and Hausdorff — needs completeness stated against the group uniformity introduced
below rather than an ambient instance, and is not proved here. Neither is the comparison of
`A⟨X₁,…,Xₖ⟩` with the plain restricted-series ring for complete Hausdorff `A`, the iteration
`A⟨X⟩⟨Y⟩ ≅ A⟨X,Y⟩`, nor the stability of noetherianness under quotients; those belong to the
later roadmap milestones of Layer 0.5.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08` formalises an `IsStronglyNoetherian` class in
`projects/AdicSpaces/Adic spaces/RestrictedPowerSeries.lean` and `TateAcyclicity.lean`. It
was consulted and not ported: AINTLIB quantifies over the *uncompleted* restricted-series
subring, which matches Wedhorn only for complete Hausdorff rings, whereas the roadmap — and
this file — define `A⟨X₁,…,Xₖ⟩` through the separated completion so that the predicate is
meaningful for arbitrary Tate rings. Nothing was copied.
-/

public section

namespace TauCeti.Huber

variable (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- The completed restricted power-series algebra `A⟨X₁,…,Xₖ⟩` of a nonarchimedean commutative
ring `A`: the separated completion of the ring of restricted power series in `k` variables —
the weighted ring `TauCeti.Huber.weightedRestrictedSubring` at the trivial weight family
`Tᵢ = {1}` — with respect to the uniformity of its ring topology. For `k = 0` this is the
separated completion of `A` itself. -/
noncomputable abbrev restrictedMvPowerSeriesCompletion : Type _ :=
  UniformSpace.Completion
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)

/-- The structure map `A → A⟨X₁,…,Xₖ⟩` is continuous. -/
theorem continuous_algebraMap_restrictedMvPowerSeriesCompletion :
    Continuous (algebraMap A (restrictedMvPowerSeriesCompletion k A)) := by
  have h : Continuous (algebraMap A (weightedRestrictedSubring
      (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)) :=
    (continuous_weightedC isWeightFamily_one_weight).congr fun a ↦ Subtype.ext (by simp)
  exact ((UniformSpace.Completion.continuous_coe _).comp h).congr fun a ↦
    (UniformSpace.Completion.algebraMap_def _ _ a).symm

/-- A nonarchimedean commutative ring is **strongly noetherian** when every completed
restricted power-series algebra `A⟨X₁,…,Xₖ⟩` over it is noetherian. For `k = 0` this asks
that the separated completion of `A` be noetherian.

This is the hypothesis of Wedhorn's Theorem 8.28, the strongly noetherian form of Tate
acyclicity; Wedhorn states it for Tate rings, and every complete rank-one nonarchimedean
field satisfies it (BGR 5.2.6 — not yet formalised). -/
@[mk_iff]
class IsStronglyNoetherian : Prop where
  isNoetherianRing (k : ℕ) : IsNoetherianRing (restrictedMvPowerSeriesCompletion k A)

/-- The defining property, as an instance: with `[IsStronglyNoetherian A]` in scope, each
`A⟨X₁,…,Xₖ⟩` is a noetherian ring by typeclass resolution. -/
instance (k : ℕ) [IsStronglyNoetherian A] :
    IsNoetherianRing (restrictedMvPowerSeriesCompletion k A) :=
  IsStronglyNoetherian.isNoetherianRing k

/-! ### The discrete case -/

/-- **A noetherian ring with the discrete topology is strongly noetherian.** This is the
nondegenerate family of witnesses for `IsStronglyNoetherian` — `ℤ`, any field, any noetherian
ring, all discretely topologised. -/
instance IsStronglyNoetherian.of_discreteTopology [DiscreteTopology A] [IsNoetherianRing A] :
    IsStronglyNoetherian A where
  isNoetherianRing k := by
    have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
    have : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight) := DiscreteUniformity.of_discreteTopology
    exact isNoetherianRing_of_ringEquiv _
      ((weightedPolynomialEquiv _ isWeightFamily_one_weight).trans
        (UniformSpace.Completion.completeRingEquivSelf _).symm)

/-! ### Zero variables -/

section ZeroVariables

variable {A}

/-- **At zero variables every power series is restricted.** There is only one monomial, so the
coefficient family is indexed by a subsingleton and converges to zero along the cofinite filter
vacuously. -/
theorem weightedRestrictedSubring_fin_zero :
    weightedRestrictedSubring (fun _ : Fin 0 ↦ ({1} : Set A)) isWeightFamily_one_weight = ⊤ := by
  ext f
  simp [isWeightedRestricted_one_weight_iff, Filter.cofinite_eq_bot]

omit [TopologicalSpace A] [NonarchimedeanRing A] in
/-- At zero variables the weight subgroup `Tν · U` is just `U`: the weight is the empty product
`{1}`, and the subgroup that generates absorbs into `U`. -/
theorem weightMul_fin_zero (ν : Fin 0 →₀ ℕ) (U : AddSubgroup A) :
    weightMul (fun _ : Fin 0 ↦ ({1} : Set A)) ν U = U := by
  rw [weightMul_def, weightPow_def]
  simp

/-- **`A⟨⟩ = A`**: the restricted power series in no variables are `A` itself, as a ring. -/
noncomputable def weightedRestrictedSubringFinZeroEquiv :
    weightedRestrictedSubring (fun _ : Fin 0 ↦ ({1} : Set A)) isWeightFamily_one_weight ≃+* A :=
  (RingEquiv.subringCongr weightedRestrictedSubring_fin_zero).trans <|
    Subring.topEquiv.trans (MvPowerSeries.isEmptyEquiv (Fin 0) A).toRingEquiv

/-- The zero-variable comparison is the constant coefficient. -/
@[simp]
theorem weightedRestrictedSubringFinZeroEquiv_apply
    (f : weightedRestrictedSubring (fun _ : Fin 0 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    weightedRestrictedSubringFinZeroEquiv f =
      MvPowerSeries.constantCoeff (f : MvPowerSeries (Fin 0) A) := (rfl)

/-- The zero-variable comparison is continuous. -/
theorem continuous_weightedRestrictedSubringFinZeroEquiv :
    Continuous (weightedRestrictedSubringFinZeroEquiv (A := A)) := by
  refine continuous_of_continuousAt_zero
    weightedRestrictedSubringFinZeroEquiv.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero,
    (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).tendsto_left_iff]
  intro V hV
  obtain ⟨U, hUV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
  refine ⟨U, trivial, fun f hf ↦ hUV ?_⟩
  have h := mem_weightedNhd.mp hf 0
  rw [weightMul_fin_zero] at h
  simpa using h

/-- The inverse comparison sends `a` to the constant series. -/
@[simp]
theorem coe_weightedRestrictedSubringFinZeroEquiv_symm (a : A) :
    ((weightedRestrictedSubringFinZeroEquiv.symm a :
        weightedRestrictedSubring (fun _ : Fin 0 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
      MvPowerSeries (Fin 0) A) = MvPowerSeries.C a := (rfl)

/-- The inverse of the zero-variable comparison is continuous. -/
theorem continuous_weightedRestrictedSubringFinZeroEquiv_symm :
    Continuous (weightedRestrictedSubringFinZeroEquiv (A := A)).symm := by
  refine continuous_of_continuousAt_zero
    (weightedRestrictedSubringFinZeroEquiv (A := A)).symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero,
    (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).tendsto_right_iff]
  intro U _
  filter_upwards [U.isOpen.mem_nhds U.zero_mem] with a ha
  refine mem_weightedNhd.mpr fun ν ↦ ?_
  rw [weightMul_fin_zero]
  simpa [Subsingleton.elim ν 0] using ha

/-- **`A⟨⟩` is the separated completion of `A`.** The zero-variable comparison is a topological
ring isomorphism, so it extends to the completions, where it is an isomorphism because
`UniformSpace.Completion.mapRingHom` is functorial. -/
noncomputable def restrictedMvPowerSeriesCompletionFinZeroEquiv :
    letI := IsTopologicalAddGroup.rightUniformSpace A
    letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    restrictedMvPowerSeriesCompletion 0 A ≃+* UniformSpace.Completion A :=
  letI := IsTopologicalAddGroup.rightUniformSpace A
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  UniformSpace.Completion.mapRingEquiv weightedRestrictedSubringFinZeroEquiv
    continuous_weightedRestrictedSubringFinZeroEquiv
    continuous_weightedRestrictedSubringFinZeroEquiv_symm

/-- **At zero variables, strong noetherianness says that the separated completion `Â` is
noetherian.** This is the `k = 0` reading of `TauCeti.Huber.IsStronglyNoetherian`, transported
along the identification of `A⟨⟩` with `Â`. -/
theorem isNoetherianRing_completion_of_isStronglyNoetherian [IsStronglyNoetherian A] :
    letI := IsTopologicalAddGroup.rightUniformSpace A
    letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    IsNoetherianRing (UniformSpace.Completion A) :=
  let _ := IsTopologicalAddGroup.rightUniformSpace A
  let _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  isNoetherianRing_of_ringEquiv _ restrictedMvPowerSeriesCompletionFinZeroEquiv

end ZeroVariables

end TauCeti.Huber
