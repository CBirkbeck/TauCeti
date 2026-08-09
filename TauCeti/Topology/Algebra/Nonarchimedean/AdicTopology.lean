/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Transporting an adic topology along a ring equivalence

An `IsAdic` hypothesis moves across a ring equivalence that is also an inducing map. Nothing
here mentions a Huber ring or a pair of definition — it is a statement about Mathlib's `IsAdic`
and `Ideal.comap` — so it is stated in the root namespace, mirroring the home of `IsAdic` itself.

The use downstream is that `TauCeti.Huber.PairOfDefinition` asks for an `Ideal A₀` whose adic
topology is the subspace topology, while the ideal at hand usually lives in a ring that is only
equivalent to `A₀`.

## Main results

* `IsAdic.comap`: an adic topology transports along an inducing ring equivalence.

## References

* Mathlib's `Mathlib/Topology/Algebra/Nonarchimedean/AdicTopology.lean`, which defines `IsAdic`
  and supplies the `isAdic_iff` characterisation both halves of the proof run on.
-/

public section

open Topology

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

omit [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B] in
/-- The powers of a comapped ideal are the comapped powers, along a ring equivalence. -/
private theorem comap_pow_of_equiv (e : B ≃+* A) (I : Ideal A) (n : ℕ) :
    (I ^ n).comap e = I.comap e ^ n := by
  rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]

/-- An adic topology transports along a ring equivalence that is also an inducing map.

This is what lets a ring of definition carry an ideal of definition: `PairOfDefinition` asks for
an `Ideal A₀` whose adic topology is the subspace topology, while the ideal at hand usually lives
in a ring that is only equivalent to `A₀`. -/
theorem IsAdic.comap (e : B ≃+* A) (he : IsInducing e) {I : Ideal A} (h : IsAdic I) :
    IsAdic (I.comap e) := by
  rw [isAdic_iff] at h ⊢
  obtain ⟨hopen, hnhds⟩ := h
  have hset : ∀ n : ℕ,
      ((I.comap e ^ n : Ideal B) : Set B) = e ⁻¹' ((I ^ n : Ideal A) : Set A) := by
    intro n
    ext b
    rw [← comap_pow_of_equiv e I n, SetLike.mem_coe, Ideal.mem_comap, Set.mem_preimage,
      SetLike.mem_coe]
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · rw [hset n, he.isOpen_iff]
    exact ⟨_, hopen n, rfl⟩
  · rw [he.nhds_eq_comap (0 : B), map_zero, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    obtain ⟨n, hn⟩ := hnhds t ht
    exact ⟨n, by rw [hset n]; exact fun b hb ↦ hts (hn hb)⟩
