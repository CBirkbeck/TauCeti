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
just as well but could not start that argument. Both results are therefore stated for an
arbitrary zero sequence, so that a caller holding a concrete one — the powers of a
pseudouniformiser, say — keeps it rather than trading it for an opaque choice.

## Main definitions

* `TauCeti.Huber.HasZeroSequenceOfUnits`: the ring admits a sequence of units tending to zero.

## Main results

* `TauCeti.Huber.exists_mul_mem_of_tendsto_zero`: along any zero sequence of units, some term
  carries a given element into a given neighbourhood of zero.
* `TauCeti.Huber.iUnion_inv_smul_eq_univ_of_tendsto_zero`: its dilates `uₙ⁻¹ • U` cover the ring,
  indexed by `ℕ`.
* `TauCeti.Huber.IsPseudoUniformizer.tendsto_pow_unit`,
  `TauCeti.Huber.IsPseudoUniformizer.hasZeroSequenceOfUnits` and
  `TauCeti.Huber.IsTateRing.hasZeroSequenceOfUnits`: the powers of a pseudouniformiser converge
  to zero as units, so a pseudouniformiser — hence a Tate ring, by instance search — satisfies
  the hypothesis.
* `TauCeti.Huber.HasZeroSequenceOfUnits.exists_unit_mul_mem`: the weaker unit-only form of
  absorption — it produces some `v : Aˣ`, with no sequence and no term index. The covering is
  *not* restated at class level: destructing `exists_tendsto` and applying
  `iUnion_inv_smul_eq_univ_of_tendsto_zero` is the same two steps.

## References

* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
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
class HasZeroSequenceOfUnits : Prop where
  /-- Some sequence of units converges to zero. -/
  exists_tendsto : ∃ u : ℕ → Aˣ, Tendsto (fun n ↦ ((u n : A))) atTop (𝓝 0)

/-- Destructor for `TauCeti.Huber.HasZeroSequenceOfUnits`: it is a class so that a Tate ring
supplies it by instance search, and this is how a proof reaches the sequence. -/
@[simp]
theorem hasZeroSequenceOfUnits_iff :
    HasZeroSequenceOfUnits A ↔ ∃ u : ℕ → Aˣ, Tendsto (fun n ↦ ((u n : A))) atTop (𝓝 0) :=
  ⟨fun h ↦ h.exists_tendsto, fun h ↦ ⟨h⟩⟩

variable {A}

/-- **The powers of a pseudouniformiser converge to zero, as units.** This is the concrete zero
sequence, kept nameable so a caller holding `ϖ` can feed *it* to the results below instead of
destructing an existential. -/
theorem IsPseudoUniformizer.tendsto_pow_unit {a : A} (ha : IsPseudoUniformizer a) :
    Tendsto (fun n ↦ ((ha.isUnit.unit ^ n : Aˣ) : A)) atTop (𝓝 0) := by
  -- `IsTopologicallyNilpotent` is a `def`, so ascribe its `Tendsto` form for `simp` to see.
  have hnil : Tendsto (fun n ↦ a ^ n) atTop (𝓝 0) := ha.isTopologicallyNilpotent
  simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using hnil

/-- **A pseudouniformiser makes the ring admit a zero sequence of units.** No Huber or Tate
hypothesis is needed: a topologically nilpotent unit is exactly what the class asks for. The
witness is `TauCeti.Huber.IsPseudoUniformizer.tendsto_pow_unit`, which a caller wanting the
powers themselves should use instead. -/
theorem IsPseudoUniformizer.hasZeroSequenceOfUnits {a : A} (ha : IsPseudoUniformizer a) :
    HasZeroSequenceOfUnits A :=
  ⟨_, ha.tendsto_pow_unit⟩

/-- **A Tate ring satisfies Henkel's hypothesis on the base ring**, via the powers of a
pseudouniformiser.

This is where the Tate condition enters Henkel's theorem: a Huber ring that is not Tate need not
admit such a sequence, `ℤ_[p]` being the example. -/
instance IsTateRing.hasZeroSequenceOfUnits {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsTateRing A] : HasZeroSequenceOfUnits A :=
  let ⟨_, ha⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  ha.hasZeroSequenceOfUnits

section Absorption

variable [ContinuousConstSMul Aᵐᵒᵖ A] {u : ℕ → Aˣ}
  (hu : Tendsto (fun n ↦ ((u n : A))) atTop (𝓝 0))
include hu

/-- **Absorption.** Along a zero sequence of units, every element is carried into every
neighbourhood of zero by some term of the sequence.

Stated for an arbitrary such sequence rather than a chosen one, so a caller holding a concrete
sequence — the powers of a pseudouniformiser, say — gets the conclusion for *that* sequence.
Only continuity of right multiplication by the fixed `x` is used — `uₙ · x → 0 · x = 0` — which
is why the hypothesis is the opposite-action `ContinuousConstSMul Aᵐᵒᵖ A` rather than
`SeparatelyContinuousMul A`; the latter implies it, so a topological ring still qualifies. -/
theorem exists_mul_mem_of_tendsto_zero (x : A) {U : Set A} (hU : U ∈ 𝓝 (0 : A)) :
    ∃ n : ℕ, ((u n : A)) * x ∈ U := by
  have hmul : Tendsto (fun n ↦ ((u n : A)) * x) atTop (𝓝 ((0 : A) * x)) := by
    simpa only [op_smul_eq_mul] using hu.const_smul (MulOpposite.op x)
  rw [zero_mul] at hmul
  exact (hmul.eventually_mem hU).exists

/-- **The countable covering Henkel's Baire argument runs on**: the dilates `uₙ⁻¹ • U` of a
neighbourhood of zero exhaust the ring. The index is `ℕ`, which is what makes the cover usable
in a Baire argument — a cover by all of `Aˣ` would exhaust the ring too but could not start
that argument. -/
theorem iUnion_inv_smul_eq_univ_of_tendsto_zero {U : Set A} (hU : U ∈ 𝓝 (0 : A)) :
    ⋃ n : ℕ, ((u n)⁻¹ : Aˣ) • U = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
  obtain ⟨n, hn⟩ := exists_mul_mem_of_tendsto_zero hu x hU
  exact ⟨n, Set.mem_inv_smul_set_iff.mpr (by rwa [Units.smul_def, smul_eq_mul])⟩

end Absorption

namespace HasZeroSequenceOfUnits

variable [ContinuousConstSMul Aᵐᵒᵖ A] [HasZeroSequenceOfUnits A]

/-- Some unit carries a given element into a given neighbourhood of zero.

Deliberately not phrased with a sequence: quantifying over an unconstrained `u : ℕ → Aˣ` would
say no more than this, since a constant sequence witnesses it. The sequence matters only for
`iUnion_inv_smul_eq_univ_of_tendsto_zero`, which is stated for a given sequence carrying its own
convergence hypothesis rather than restated at class level. -/
theorem exists_unit_mul_mem (x : A) {U : Set A} (hU : U ∈ 𝓝 (0 : A)) :
    ∃ v : Aˣ, (v : A) * x ∈ U := by
  obtain ⟨u, hu⟩ := ‹HasZeroSequenceOfUnits A›.exists_tendsto
  obtain ⟨n, hn⟩ := exists_mul_mem_of_tendsto_zero hu x hU
  exact ⟨u n, hn⟩

end HasZeroSequenceOfUnits

end TauCeti.Huber
