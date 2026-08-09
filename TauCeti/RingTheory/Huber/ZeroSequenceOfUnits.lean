/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.Basic

/-!
# Rings with a zero sequence of units

Henkel's open mapping theorem is stated for a topological ring carrying a *zero sequence of
units*: a sequence of units converging to zero. This file isolates that hypothesis and records
the two facts about it that the theorem uses — that a Tate ring satisfies it, and that in a ring
that satisfies it every element is absorbed into every neighbourhood of zero, so the dilates of
a neighbourhood cover the ring.

The covering is the point. Henkel's proof applies a Baire argument to the sets `uₙ⁻¹ • U`, and
what makes that argument start is exactly that they exhaust the ring.

## Main definitions

* `TauCeti.Huber.HasZeroSequenceOfUnits`: the ring admits a sequence of units tending to zero.

## Main results

* `TauCeti.Huber.IsTateRing.hasZeroSequenceOfUnits`: a Tate ring has one, namely the powers of a
  pseudouniformiser.
* `TauCeti.Huber.HasZeroSequenceOfUnits.exists_unit_mul_mem`: some term of the sequence carries a
  given element into a given neighbourhood of zero.
* `TauCeti.Huber.HasZeroSequenceOfUnits.iUnion_smul_eq_univ`: the dilates of a neighbourhood of
  zero cover the ring.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Theorem 6.16 and Propositions 6.17–6.18, which are
  proved from Henkel's open mapping theorem; this file states the hypothesis that theorem places
  on the base ring.
-/

public section

open Filter Topology Pointwise

namespace TauCeti.Huber

variable (A : Type*) [CommRing A] [TopologicalSpace A]

/-- Henkel's hypothesis on the base ring: there is a sequence of units converging to zero.

A discrete ring has none unless it is trivial, and that is the intended exclusion: the theorem
needs to shrink a neighbourhood by an invertible factor. -/
def HasZeroSequenceOfUnits : Prop :=
  ∃ u : ℕ → Aˣ, Tendsto (fun n ↦ ((u n : A))) atTop (nhds 0)

/-- Unfolding lemma for `TauCeti.Huber.HasZeroSequenceOfUnits`. -/
theorem hasZeroSequenceOfUnits_iff :
    HasZeroSequenceOfUnits A ↔ ∃ u : ℕ → Aˣ, Tendsto (fun n ↦ ((u n : A))) atTop (nhds 0) :=
  (Iff.rfl)

variable {A}

/-- **A Tate ring has a zero sequence of units**: the powers of a pseudouniformiser.

This is where the Tate condition enters Henkel's theorem — a Huber ring that is not Tate need
not admit such a sequence, `ℤ_[p]` being the example. -/
theorem IsPseudoUniformizer.hasZeroSequenceOfUnits {a : A} (ha : IsPseudoUniformizer a) :
    HasZeroSequenceOfUnits A :=
  ⟨fun n ↦ ha.isUnit.unit ^ n, by
    -- `IsTopologicallyNilpotent` is a `def`, so ascribe its `Tendsto` form for `simp` to see.
    have hnil : Tendsto (fun n ↦ a ^ n) atTop (nhds 0) := ha.isTopologicallyNilpotent
    simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using hnil⟩

/-- A Tate ring satisfies Henkel's hypothesis on the base ring. -/
theorem IsTateRing.hasZeroSequenceOfUnits [IsTopologicalRing A] [IsTateRing A] :
    HasZeroSequenceOfUnits A :=
  let ⟨_, ha⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  ha.hasZeroSequenceOfUnits

namespace HasZeroSequenceOfUnits

variable [IsTopologicalRing A] (h : HasZeroSequenceOfUnits A)
include h

/-- Every element is absorbed into every neighbourhood of zero by some unit of the sequence.

Only continuity of multiplication by a constant is used: `uₙ · x → 0 · x = 0`. -/
theorem exists_unit_mul_mem (x : A) {U : Set A} (hU : U ∈ nhds (0 : A)) :
    ∃ u : Aˣ, (u : A) * x ∈ U := by
  obtain ⟨u, hu⟩ := h
  have hmul : Tendsto (fun n ↦ ((u n : A)) * x) atTop (nhds ((0 : A) * x)) := hu.mul_const x
  rw [zero_mul] at hmul
  obtain ⟨n, hn⟩ := (hmul.eventually_mem hU).exists
  exact ⟨u n, hn⟩

/-- **The covering Henkel's Baire argument runs on**: the dilates `u⁻¹ • U` of a neighbourhood of
zero, as `u` ranges over the units, exhaust the ring. -/
theorem iUnion_smul_eq_univ {U : Set A} (hU : U ∈ nhds (0 : A)) :
    ⋃ u : Aˣ, (u⁻¹ : Aˣ) • U = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
  obtain ⟨u, hu⟩ := h.exists_unit_mul_mem x hU
  exact ⟨u, ⟨(u : A) * x, hu, by simp [smul_eq_mul, ← mul_assoc]⟩⟩

end HasZeroSequenceOfUnits

end TauCeti.Huber
