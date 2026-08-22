/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Matrix
public import TauCeti.RingTheory.Huber.OpenMapping

/-!
# Dense submodules of a module-finite complete Tate-module

A dense submodule of a module-finite, complete, metrisable module over a complete Tate ring is
the whole module. This is Bosch–Güntzer–Remmert §3.7.2/1 in its intrinsic form, and it is the
step that makes finitely generated submodules closed on the route to Wedhorn 6.17/6.18.

The argument is the open mapping theorem followed by Nakayama. A finite spanning family presents
`V` as an *open* quotient of `Aⁿ`
(`TauCeti.Huber.IsTateRing.isOpenMap_linearCombination`), so the image of a neighbourhood of zero
consisting of topologically nilpotent scalars is a neighbourhood of zero in `V`. Density writes
each generator as `gᵥ = mᵥ + ∑ⱼ aᵥⱼ • gⱼ` with `mᵥ` in the submodule and every `aᵥⱼ` topologically
nilpotent, and matrix Nakayama in the quotient
(`TauCeti.Huber.eq_zero_of_isTopologicallyNilpotent_entries_of_forall_eq_sum_smul`) forces every
generator into the submodule.

The neighbourhood of topologically nilpotent scalars is the image of the ideal of definition: it
is open (`TauCeti.Huber.PairOfDefinition.isOpen_idealImage`) and its elements are topologically
nilpotent (`TauCeti.Huber.PairOfDefinition.isTopologicallyNilpotent_of_mem_idealImage`), so no
pseudouniformiser needs to be chosen.

## Main results

* `TauCeti.Huber.eq_top_of_dense_of_module_finite`: a dense submodule of a module-finite complete
  Tate-module is everything.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch_guntzer_remmert], §3.7.2/1.
* [Wedhorn, *Adic Spaces*][wedhorn_adic], Propositions 6.17–6.18.
-/

open Filter Topology
open scoped Uniformity

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [(𝓤 A).IsCountablyGenerated] [T2Space A] [NonarchimedeanRing A] [IsTateRing A]
  {V : Type*} [AddCommGroup V] [UniformSpace V] [IsUniformAddGroup V] [CompleteSpace V]
  [(𝓤 V).IsCountablyGenerated] [T0Space V] [Module A V] [ContinuousSMul A V]

/-- A neighbourhood of zero consisting of topologically nilpotent elements: the image of the
ideal of definition. Private because it is immediate from the pair-of-definition API and exists
only to keep the density argument below readable. -/
private theorem exists_nhds_zero_forall_isTopologicallyNilpotent (A : Type*) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] :
    ∃ W ∈ nhds (0 : A), ∀ a ∈ W, IsTopologicallyNilpotent a := by
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  exact ⟨P.idealImage 1, (P.isOpen_idealImage 1).mem_nhds (P.idealImage 1).zero_mem,
    fun _ ha ↦ P.isTopologicallyNilpotent_of_mem_idealImage one_ne_zero ha⟩

/-- **A dense submodule of a module-finite complete Tate-module is everything**
(Bosch–Güntzer–Remmert §3.7.2/1).

The open mapping theorem dilates a neighbourhood of zero in `Aⁿ` onto one in `V`, so density
writes each generator as `gᵥ = mᵥ + ∑ⱼ aᵥⱼ • gⱼ` with `mᵥ ∈ N` and every `aᵥⱼ` topologically
nilpotent; matrix Nakayama in `V ⧸ N` then forces every `gᵥ ∈ N`. -/
theorem eq_top_of_dense_of_module_finite [Module.Finite A V] (N : Submodule A V)
    (hN : Dense (N : Set V)) : N = ⊤ := by
  classical
  obtain ⟨n, g, hspan⟩ := Module.Finite.exists_fin (R := A) (M := V)
  obtain ⟨W, hW_nhds, hW_tn⟩ := exists_nhds_zero_forall_isTopologicallyNilpotent A
  have hopen : IsOpenMap (Fintype.linearCombination A g : (Fin n → A) → V) :=
    IsTateRing.isOpenMap_linearCombination g hspan
  have hWpi_nhds : Set.univ.pi (fun _ : Fin n ↦ W) ∈ nhds (0 : Fin n → A) :=
    set_pi_mem_nhds Set.finite_univ fun i _ ↦ by simpa using hW_nhds
  have hΩ_nhds :
      (Fintype.linearCombination A g) '' Set.univ.pi (fun _ : Fin n ↦ W) ∈ nhds (0 : V) := by
    have := hopen.image_mem_nhds (x := (0 : Fin n → A)) hWpi_nhds
    rwa [map_zero] at this
  -- Density writes each generator as an `N`-element plus a topologically nilpotent combination.
  have hextract : ∀ v : Fin n, ∃ a : Fin n → A, (∀ j, a j ∈ W) ∧
      ∃ m ∈ N, g v = m + ∑ j, a j • g j := by
    intro v
    have hnb : (fun z : V ↦ g v - z) ⁻¹'
        ((Fintype.linearCombination A g) '' Set.univ.pi (fun _ : Fin n ↦ W)) ∈ nhds (g v) := by
      refine (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hΩ_nhds
    obtain ⟨w, hwU, hwN⟩ := mem_closure_iff_nhds.mp (hN (g v)) _ hnb
    obtain ⟨a, haW, ha_eq⟩ := hwU
    refine ⟨a, fun j ↦ Set.mem_univ_pi.mp haW j, w, hwN, ?_⟩
    have hpa : (∑ j, a j • g j) = g v - w := by
      rw [← Fintype.linearCombination_apply]; exact ha_eq
    rw [hpa]; abel
  choose a haW m hmN hrel using hextract
  -- Matrix Nakayama in `V ⧸ N`.
  have hy : ∀ v, N.mkQ (g v) = ∑ j, Matrix.of a v j • N.mkQ (g j) := by
    intro v
    have hq0 : N.mkQ (m v) = 0 := (Submodule.Quotient.mk_eq_zero N).2 (hmN v)
    simp only [Matrix.of_apply]
    rw [hrel v, map_add, hq0, map_sum, zero_add]
    simp only [map_smul]
  have hzero := eq_zero_of_isTopologicallyNilpotent_entries_of_forall_eq_sum_smul
    (B := Matrix.of a)
    (fun i j ↦ hW_tn _ (haW i j)) hy
  refine eq_top_iff.2 ?_
  rw [← hspan]
  exact Submodule.span_le.2 (Set.range_subset_iff.2 fun v ↦
    (Submodule.Quotient.mk_eq_zero N).1 (by simpa using congrFun hzero v))

end TauCeti.Huber
