/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Hom

/-!
# The evaluation of `A⟨X⟩_T` is continuous

`WeightedEval/Hom.lean` packages Wedhorn's evaluation as a ring homomorphism `A⟨X⟩_T →+* B`. This
file proves it continuous for the topology of `A⟨X⟩_T`, which is the last property Proposition
5.50 asks of the extension apart from its uniqueness.

The argument is the one that made the terms summable, run at a fixed series rather than along the
cofinite filter. A basic neighbourhood `U⟨X⟩` of zero bounds *every* coefficient of `f` by
`Tν · U`, so — once `φ(U)` is small enough to shrink the weighted monomials into a prescribed open
subgroup `G` of `B` — *every* term of the evaluation lies in `G`. The partial sums then lie in `G`
because it is a subgroup, and the sum lies in `G` because an open subgroup is closed.

## Main results

* `TauCeti.Huber.weightedEvalTerm_mem_of_mem_weightMul`: the term-level bound just described.
* `TauCeti.Huber.continuous_weightedEvalHom`: the evaluation homomorphism is continuous.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50.
-/

public section

open Filter Pointwise Topology

namespace TauCeti.Huber

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B]
  [T3Space B] {φ : A →+* B} {T : Fin k → Set A} {b : Fin k → B}

omit [TopologicalSpace A] [NonarchimedeanRing A] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T3Space B] in
/-- **Every term of the evaluation is small when every coefficient is.** If the `ν`-th coefficient
of `f` lies in `Tν · U`, and `φ(U)` multiplied by the bounded family of weighted monomials lands
in `G`, then the `ν`-th term of the evaluation lies in `G`.

This is the fixed-series form of the estimate behind
`TauCeti.Huber.tendsto_weightedEvalTerm_cofinite_zero`; there it is applied to the cofinitely many
coefficients that satisfy the bound, here to all of them at once. -/
theorem weightedEvalTerm_mem_of_mem_weightMul {U : AddSubgroup A} {V : Set B}
    {G : OpenAddSubgroup B} (hUV : (φ : A → B) '' U ⊆ V)
    (hVG : V * (⋃ ν : Fin k →₀ ℕ, (fun t ↦ φ t * ∏ i, b i ^ ν i) '' weightPow T ν) ⊆ (G : Set B))
    {f : MvPowerSeries (Fin k) A} {ν : Fin k →₀ ℕ}
    (hf : MvPowerSeries.coeff ν f ∈ weightMul T ν U) :
    weightedEvalTerm φ b f ν ∈ G := by
  classical
  let ψ : A →+ B := (AddMonoidHom.mulRight (∏ i, b i ^ ν i)).comp (φ : A →+ B)
  have hgen : ∀ t ∈ weightPow T ν, ∀ u ∈ U, t * u ∈ G.toAddSubgroup.comap ψ := by
    intro t ht u hu
    have hval : ψ (t * u) = φ u * (φ t * ∏ i, b i ^ ν i) := by
      simp only [ψ, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulRight,
        AddMonoidHom.coe_coe, map_mul]
      ring
    simp only [AddSubgroup.mem_comap, hval]
    exact hVG (Set.mul_mem_mul (hUV ⟨u, hu, rfl⟩) (Set.mem_iUnion.mpr ⟨ν, ⟨t, ht, rfl⟩⟩))
  have hcomap : MvPowerSeries.coeff ν f ∈ G.toAddSubgroup.comap ψ := weightMul_le.mpr hgen hf
  -- `ψ` applied to the coefficient is the term; say so rather than lean on the wrapper.
  simpa only [weightedEvalTerm_def, ψ, AddSubgroup.mem_comap, AddMonoidHom.coe_comp,
    Function.comp_apply, AddMonoidHom.coe_mulRight, AddMonoidHom.coe_coe, SetLike.mem_coe,
    OpenAddSubgroup.mem_toAddSubgroup] using hcomap

/-- **The evaluation homomorphism is continuous.** A basic neighbourhood `U⟨X⟩` bounds every
coefficient, hence every term, inside a prescribed open subgroup `G`; the partial sums stay in `G`
because it is a subgroup, and the sum stays in `G` because an open subgroup is closed. -/
theorem continuous_weightedEvalHom (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) : Continuous (weightedEvalHom hT hφ hb) := by
  have _ : IsTopologicalRing (weightedRestrictedSubring T hT) :=
    isTopologicalRing_weightedTopology
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  refine Filter.tendsto_def.mpr fun W hW ↦ ?_
  obtain ⟨G, hGW⟩ := NonarchimedeanAddGroup.is_nonarchimedean W hW
  obtain ⟨V, hV, hVG⟩ := isBounded_iff.mp ((isWeightBounded_iff φ T b).mp hb) (G : Set B)
    (G.isOpen.mem_nhds G.zero_mem)
  obtain ⟨U, hUV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (hφ.preimage_mem_nhds (by simpa only [map_zero] using hV))
  refine Filter.mem_of_superset
    ((hasBasis_nhds_zero_weightedTopology hT).mem_of_mem (i := U) trivial) fun f hf ↦ ?_
  refine hGW ?_
  rw [coe_weightedEvalHom]
  refine G.isClosed.mem_of_tendsto
    (hasSum_weightedEval hφ hb (mem_weightedRestrictedSubring.mp f.property)) ?_
  filter_upwards with s
  exact G.toAddSubgroup.sum_mem fun ν _ ↦
    weightedEvalTerm_mem_of_mem_weightMul (fun _ ⟨u, hu, hval⟩ ↦ hval ▸ hUV hu) hVG
      (mem_weightedNhd.mp hf ν)

end TauCeti.Huber

end
