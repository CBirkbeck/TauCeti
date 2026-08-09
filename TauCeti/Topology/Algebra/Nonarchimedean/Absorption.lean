/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Absorption of fixed elements in a nonarchimedean ring

In a nonarchimedean ring multiplication by a fixed element `a` is continuous, so every
neighbourhood `V` of zero absorbs `a`: some open additive subgroup `Z` satisfies `a * Z ⊆ V`.
Mathlib's `NonarchimedeanRing.left_mul_subset` says this for a bundled `OpenAddSubgroup` target;
the two results here are the unbundled and the finite-family forms, which is the shape an
estimate over a finite set of coefficients needs.

Neither result mentions a weight family, a power series or a Huber ring, so they are stated
here rather than alongside the theory that uses them.

## Main results

* `NonarchimedeanRing.exists_openAddSubgroup_mul_subset`: an additive subgroup that is a
  neighbourhood of zero absorbs any fixed element.
* `NonarchimedeanRing.exists_openAddSubgroup_forall_mul_subset`: finitely many fixed elements
  are absorbed into their own targets by a single open subgroup.

## References

* Mathlib's `Mathlib/Topology/Algebra/Nonarchimedean/Basic.lean`, whose
  `NonarchimedeanRing.left_mul_subset` both proofs run on.
-/

public section

namespace NonarchimedeanRing

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- An additive subgroup that is a neighbourhood of zero absorbs any fixed element: there is an
open subgroup `Z` with `a * Z ⊆ V`. This is `NonarchimedeanRing.left_mul_subset` with the target
unbundled, using that a subgroup which is a neighbourhood of zero is open. -/
theorem exists_openAddSubgroup_mul_subset (a : A) (V : AddSubgroup A)
    (hV : (V : Set A) ∈ nhds (0 : A)) : ∃ Z : OpenAddSubgroup A, ∀ z ∈ Z, a * z ∈ V := by
  obtain ⟨Z, hZ⟩ := left_mul_subset ⟨V, V.isOpen_of_mem_nhds hV⟩ a
  exact ⟨Z, fun z hz ↦ hZ ⟨z, hz, rfl⟩⟩

/-- The finite-family form of `NonarchimedeanRing.exists_openAddSubgroup_mul_subset`: one open
subgroup absorbs each of finitely many fixed elements into its own target. -/
theorem exists_openAddSubgroup_forall_mul_subset {ι : Type*} (s : Finset ι) (a : ι → A)
    (V : ι → AddSubgroup A) (hV : ∀ i ∈ s, (V i : Set A) ∈ nhds (0 : A)) :
    ∃ Z : OpenAddSubgroup A, ∀ i ∈ s, ∀ z ∈ Z, a i * z ∈ V i := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨⊤, by simp⟩
  | insert i s' hi ih =>
      obtain ⟨Z', hZ'⟩ := ih fun j hj ↦ hV j (Finset.mem_insert_of_mem hj)
      obtain ⟨Z, hZ⟩ :=
        exists_openAddSubgroup_mul_subset (a i) (V i) (hV i (Finset.mem_insert_self i s'))
      refine ⟨Z ⊓ Z', fun j hj z hz ↦ ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact hZ z hz.1
      · exact hZ' j hj' z hz.2

end NonarchimedeanRing
