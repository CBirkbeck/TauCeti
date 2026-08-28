/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RingTheory.Valuation.LtAddSubgroup
public import TauCeti.RingTheory.Valuation.Continuous.Basic

/-!
# A sublevel set of a valuation is open once it is a neighbourhood of zero

The sets `{a | v a < γ}` cutting out continuity are additive subgroups
(`Valuation.ltAddSubgroupOfNeZero`), and a subgroup that is a neighbourhood of `0` is open. So such
a set never has to be checked for openness at every point: one open set around `0` inside it
suffices.

That is the reusable content here. The corollary recorded is the test against an **open subring**
`B`: if the trace of each sublevel set on `B` is open, then `v` is continuous. Only openness of `B`
and `0 ∈ B` are used — no ring structure — which is why the two general lemmas take a bare set and
the subring form is derived from them.

## The quantifier is over attained values

`Valuation.isContinuous_of_forall_isOpen_subring_lt` quantifies over the values `v b` that `v`
attains, matching `Valuation.IsContinuous` itself. The per-`γ` lemma applies at each `γ`
separately, so demanding openness at every `γ` of the codomain would be strictly stronger for no
gain — and, as `Valuation.Continuous.Basic` documents with a `ℤ_p` counterexample, the
whole-codomain condition is not even an invariant of the equivalence class of `v`.

## Relation to Wedhorn's Lemma 7.44(2)

Wedhorn's 7.44(2) is the equality `Cont(A) = g⁻¹(Cont(B))` for `B` an open subring, with
`g : Spv A → Spv B` induced by the inclusion. This file does **not** prove it. One inclusion is
`Valuation.IsContinuous.comap` along the inclusion, already available and needing nothing of `B`;
the criterion here is the other direction in a *sufficient* form.

The gap is that Wedhorn quantifies over `γ ∈ Γ_v = Γ_w` and obtains that equality from part **(1)**
of the same lemma — `B_q → A_p` is an isomorphism. Reaching a general `γ` from the values attained
on `B` means writing it as a ratio, which needs a value *group* rather than a monoid and needs `B`
to absorb elements of `A` after multiplication by a topologically nilpotent element; Wedhorn states
7.44 for an `f`-adic `A` precisely because that is what supplies such elements. Both are outside
this file.

## Main results

* `Valuation.isOpen_lt_of_mem_nhds_zero` : a sublevel set is open once it is a neighbourhood of `0`.
* `Valuation.isOpen_lt_of_isOpen_of_zero_mem_of_subset` : the same, from any open set containing
  `0` inside it.
* `Valuation.isOpen_lt_of_isOpen_subring_lt` : the open-subring instance.
* `Valuation.isContinuous_of_forall_isOpen_subring_lt` : hence continuity, tested on an open
  subring at the attained values.

## Provenance

The subring corollary is adapted from AINTLIB
([`github.com/CBirkbeck/AINTLIB`](https://github.com/CBirkbeck/AINTLIB), Apache-2.0,
Chris Birkbeck) at commit `37bbdaeb9`, file `projects/AdicSpaces/Adic spaces/Lemma745.lean`
line 144, `PairOfDefinition.isContinuous_of_restriction_isContinuous`, which names Wedhorn's
Lemma 7.44(2) in its docstring while assuming openness at every `γ` of the codomain. The argument
is the same; the statement here is weaker on four axes — an arbitrary subring rather than a
`PairOfDefinition`'s ring of definition, a `LinearOrderedCommMonoidWithZero` codomain rather than a
group, `SeparatelyContinuousAdd` rather than a topological ring, and the attained values rather
than the whole codomain.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.44(2), towards which
  this is the topological step.
-/

public section

namespace Valuation

open Set Topology

variable {A : Type*} [Ring A] [TopologicalSpace A]
  {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **A sublevel set of a valuation is open as soon as it is a neighbourhood of `0`.** The set is
an additive subgroup (`Valuation.ltAddSubgroupOfNeZero`), and a subgroup which is a neighbourhood
of `0` is open, so no other point has to be checked. This is the reusable content of the file; the
subring criterion below is one way of supplying the neighbourhood. -/
theorem isOpen_lt_of_mem_nhds_zero [SeparatelyContinuousAdd A] {v : Valuation A Γ₀} {γ : Γ₀}
    (h : {a : A | v a < γ} ∈ 𝓝 (0 : A)) : IsOpen {a : A | v a < γ} := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  have hopen := (v.ltAddSubgroupOfNeZero hγ).isOpen_of_mem_nhds (g := 0)
    (by rwa [coe_ltAddSubgroupOfNeZero])
  rwa [coe_ltAddSubgroupOfNeZero] at hopen

/-- **A sublevel set is open once any open set around `0` sits inside it.** The convenient form of
`Valuation.isOpen_lt_of_mem_nhds_zero`: the witness need only be open and contain `0`. -/
theorem isOpen_lt_of_isOpen_of_zero_mem_of_subset [SeparatelyContinuousAdd A]
    {v : Valuation A Γ₀} {γ : Γ₀} {U : Set A} (hU : IsOpen U) (h0 : (0 : A) ∈ U)
    (hsub : U ⊆ {a : A | v a < γ}) :
    IsOpen {a : A | v a < γ} :=
  isOpen_lt_of_mem_nhds_zero (Filter.mem_of_superset (hU.mem_nhds h0) hsub)

/-- **A sublevel set is open as soon as its trace on an open subring is.**

The two sets are not related by the topology — the trace is in general far smaller. What carries
the openness across is `Valuation.isOpen_lt_of_isOpen_of_zero_mem_of_subset`: openness of `B`
makes the trace an open set around `0` inside the sublevel set. Only openness of `B` and `0 ∈ B`
are used, which is why the two lemmas above are stated for a bare set. -/
theorem isOpen_lt_of_isOpen_subring_lt [SeparatelyContinuousAdd A] {B : Subring A}
    (hB : IsOpen (B : Set A)) {v : Valuation A Γ₀} {γ : Γ₀}
    (h : IsOpen {b : B | v (b : A) < γ}) : IsOpen {a : A | v a < γ} := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  refine isOpen_lt_of_isOpen_of_zero_mem_of_subset (hB.isOpenMap_subtype_val _ h)
    ⟨⟨0, B.zero_mem⟩, by simpa using zero_lt_iff.mpr hγ, rfl⟩ ?_
  rintro _ ⟨b, hb, rfl⟩
  exact hb

/-- **A sufficient criterion for continuity, tested on an open subring.** If the trace on the open
subring `B` of every sublevel set at an *attained* value is open, then `v` is continuous.

The quantifier runs over the attained values `v b`, matching `Valuation.IsContinuous` itself:
`Valuation.isOpen_lt_of_isOpen_subring_lt` applies at each `γ` separately, so asking for openness
at every `γ` of the codomain would be strictly stronger for no gain — and, as
`Valuation.Continuous.Basic` documents, the whole-codomain condition is not even an invariant of
the equivalence class of `v`.

This is **not** Wedhorn's Lemma 7.44(2): see the module docstring for the gap and its cost. -/
theorem isContinuous_of_forall_isOpen_subring_lt [SeparatelyContinuousAdd A] {B : Subring A}
    (hB : IsOpen (B : Set A)) {v : Valuation A Γ₀}
    (h : ∀ b : A, IsOpen {x : B | v (x : A) < v b}) : v.IsContinuous :=
  -- `IsContinuous` is sealed outside `Continuous/Basic.lean`, so the quantifier is reached
  -- through `isContinuous_def` rather than by unfolding.
  isContinuous_def.mpr fun b ↦ isOpen_lt_of_isOpen_subring_lt hB (h b)

end Valuation
