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

The covering is the point, and it must be **countable**. Henkel's proof applies a Baire argument
to the sets `uₙ⁻¹ • U` indexed by `n : ℕ`; a cover indexed by all of `Aˣ` would exhaust the ring
just as well but could not start that argument. So a sequence is chosen once, as
`HasZeroSequenceOfUnits.seq`, and the absorption step and the covering both range over it.

## Main definitions

* `TauCeti.Huber.HasZeroSequenceOfUnits`: the ring admits a sequence of units tending to zero.

## Main results

* `TauCeti.Huber.IsTateRing.hasZeroSequenceOfUnits`: a Tate ring has one, namely the powers of a
  pseudouniformiser.
* `TauCeti.Huber.HasZeroSequenceOfUnits.seq`: a choice of such a sequence, fixed once so that
  everything below ranges over the same countable family.
* `TauCeti.Huber.HasZeroSequenceOfUnits.exists_seq_mul_mem`: some term of the sequence carries a
  given element into a given neighbourhood of zero.
* `TauCeti.Huber.HasZeroSequenceOfUnits.iUnion_seq_inv_smul_eq_univ`: the dilates `uₙ⁻¹ • U` cover
  the ring, indexed by `ℕ`.

## References

* A. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647). The hypothesis formalised here, the
  terminology, and both results below are its setup.
* [Wedhorn, *Adic Spaces*][wedhorn_adic], Theorem 6.16 and Propositions 6.17–6.18, which are
  proved from Henkel's theorem; downstream context for this file rather than its source.
-/

public section

open Filter Topology Pointwise

namespace TauCeti.Huber

variable (A : Type*) [MonoidWithZero A] [TopologicalSpace A]

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

/-- **The powers of a pseudouniformiser are a zero sequence of units.** No Huber or Tate
hypothesis is needed: a topologically nilpotent unit is exactly what the definition asks for. -/
theorem IsPseudoUniformizer.hasZeroSequenceOfUnits {a : A} (ha : IsPseudoUniformizer a) :
    HasZeroSequenceOfUnits A :=
  ⟨fun n ↦ ha.isUnit.unit ^ n, by
    -- `IsTopologicallyNilpotent` is a `def`, so ascribe its `Tendsto` form for `simp` to see.
    have hnil : Tendsto (fun n ↦ a ^ n) atTop (nhds 0) := ha.isTopologicallyNilpotent
    simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using hnil⟩

/-- **A Tate ring satisfies Henkel's hypothesis on the base ring**, via the powers of a
pseudouniformiser.

This is where the Tate condition enters Henkel's theorem: a Huber ring that is not Tate need not
admit such a sequence, `ℤ_[p]` being the example. -/
theorem IsTateRing.hasZeroSequenceOfUnits {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsTateRing A] : HasZeroSequenceOfUnits A :=
  let ⟨_, ha⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  ha.hasZeroSequenceOfUnits

namespace HasZeroSequenceOfUnits

variable [ContinuousMul A] (h : HasZeroSequenceOfUnits A)
include h

/-- A choice of zero sequence of units, fixed once.

The absorption step and the covering below must range over the *same* countable family: Baire
needs a countable cover, and a cover indexed by all of `Aˣ` — which may be uncountable — would
not serve. Everything downstream therefore goes through this sequence rather than through an
unquantified unit. -/
noncomputable def seq : ℕ → Aˣ := h.choose

omit [ContinuousMul A] in
/-- The chosen sequence converges to zero. This is the characteristic property of
`TauCeti.Huber.HasZeroSequenceOfUnits.seq`; its body is not exposed. -/
theorem tendsto_seq : Tendsto (fun n ↦ ((seq h n : A))) atTop (nhds 0) := h.choose_spec

/-- Every element is absorbed into every neighbourhood of zero by some term of the sequence.

Only continuity of multiplication by a constant is used: `uₙ · x → 0 · x = 0`. -/
theorem exists_seq_mul_mem (x : A) {U : Set A} (hU : U ∈ nhds (0 : A)) :
    ∃ n : ℕ, ((seq h n : A)) * x ∈ U := by
  have hmul : Tendsto (fun n ↦ ((seq h n : A)) * x) atTop (nhds ((0 : A) * x)) :=
    (tendsto_seq h).mul_const x
  rw [zero_mul] at hmul
  exact (hmul.eventually_mem hU).exists

/-- **The countable covering Henkel's Baire argument runs on**: the dilates `uₙ⁻¹ • U` of a
neighbourhood of zero, over the chosen sequence, exhaust the ring. The index is `ℕ`, which is
what makes the cover usable in a Baire argument. -/
theorem iUnion_seq_inv_smul_eq_univ {U : Set A} (hU : U ∈ nhds (0 : A)) :
    ⋃ n : ℕ, ((seq h n)⁻¹ : Aˣ) • U = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
  obtain ⟨n, hn⟩ := exists_seq_mul_mem h x hU
  exact ⟨n, Set.mem_inv_smul_set_iff.mpr (by rwa [Units.smul_def, smul_eq_mul])⟩

end HasZeroSequenceOfUnits

end TauCeti.Huber
