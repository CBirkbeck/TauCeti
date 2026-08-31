/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RingTheory.Valuation.Continuous.Basic
public import TauCeti.RingTheory.Valuation.LtAddSubgroup

/-!
# A sufficient criterion for continuity, tested on an open subset

If `U` is an open subset of `A` containing `0` and *every* sublevel set `{a | v a < γ}` has open
trace on `U`, then `v` is continuous on `A`. Continuity of a valuation is thus detected on any one
neighbourhood of `0`.

## The mechanism

The trace `{u : U | v u < γ}` is in general far smaller than `{a : A | v a < γ}`, so openness does
not pass between them for topological reasons. What carries it is that the larger set is an
**additive subgroup** — `Valuation.ltAddSubgroupOfNeZero` — and a subgroup that is a neighbourhood
of `0` is open. Openness of `U` is exactly what promotes the trace, open in the subspace topology,
to a neighbourhood of `0` in `A`.

That argument needs no more than continuity of translation by a fixed element, so it is stated over
`[SeparatelyContinuousAdd A]` and over a `LinearOrderedCommMonoidWithZero` codomain, in keeping with
`TauCeti/RingTheory/Valuation/Continuous/Basic.lean`, which asks for compatibility per result rather
than up front. No Huber-ring hypothesis and no ideal of definition enter.

## Why an open subset and not an open subring

The intended instantiation is a ring of definition `A₀` of a Huber ring `A`, which is an open
subring; that is the shape in which Wedhorn uses the criterion. The argument, however, never
multiplies and never adds: it uses only that `U` is open and that `0 ∈ U`. Stating it for an open
subring would therefore carry a hypothesis the proof does not consume, so the subring case is left
to the caller, who supplies `A₀.zero_mem`.

## What is *not* proved here

This is the topological step towards Wedhorn's Lemma 7.44(2), `Cont(A) = g⁻¹(Cont(B))` for `B` an
open subring — **but it is not that lemma**, and the gap is recorded here rather than papered over.

The hypothesis quantifies `γ` over the whole codomain. Continuity of the restriction
`v.comap B.subtype` is weaker: being the attained-value predicate, it supplies openness only at the
values `v` takes **on `B`**. So this criterion does not combine with `Valuation.IsContinuous.comap`
— which is the easy inclusion, and is already available — to give the equality of Lemma 7.44(2).

Closing that gap means reaching a general `γ` from the values attained on `B`, that is, writing it
as a ratio. That needs a value *group* rather than a monoid, and it needs `B` to absorb elements of
`A` after multiplication by a topologically nilpotent element — Wedhorn states 7.44 for an `f`-adic
`A` precisely because that is what supplies such elements. Both hypotheses are outside this file,
which is why the criterion is stated in the honest, weaker form instead of being advertised as the
lemma.

The same caveat applies to the source: AINTLIB's `isContinuous_of_restriction_isContinuous` carries
the identical codomain-quantified hypothesis, although its docstring names it "Wedhorn Lemma
7.44(2)".

## Main results

* `Valuation.isOpen_lt_of_isOpen_trace_lt` : a sublevel set of `v` is open as soon as its trace on
  an open subset containing `0` is.
* `Valuation.isContinuous_of_isOpen_trace_lt` : hence `v` is continuous as soon as every sublevel
  set has open trace.

## Roadmap

`AdicSpaces`, README §1.5 "Continuous valuations". That section asks for `Cont A`, Theorem 7.10 and
Corollary 7.12, and then for `Cont A` to be shown *independent of the chosen pair of definition*.
Independence is a comparison between the continuity tested on one ring of definition and on
another, both open subrings of `A`; Wedhorn runs it through Lemma 7.44. This file supplies the
topological half of that comparison — the passage from openness on a ring of definition to openness
on `A` — which is the direction the independence argument consumes.

## Provenance

Adapted from AINTLIB ([`github.com/CBirkbeck/AINTLIB`](https://github.com/CBirkbeck/AINTLIB),
Apache-2.0, Chris Birkbeck) at commit `37bbdaeb9`, file
`projects/AdicSpaces/Adic spaces/Lemma745.lean` line 144,
`PairOfDefinition.isContinuous_of_restriction_isContinuous`, which names Wedhorn's Lemma 7.44(2) in
its docstring while assuming, as here, openness for every `γ` of the codomain. The argument is the
same; the statement here is weaker on three axes. That development fixes an ambient
`PairOfDefinition` and phrases the hypothesis through its ring of definition, works over a
`LinearOrderedCommGroupWithZero` codomain, and closes through Mathlib's `Valuation.ltAddSubgroup`,
which is indexed by units of the codomain and so forces that group hypothesis. Here the carrier is
an arbitrary open subset containing `0`, the codomain is a monoid, and the ambient hypothesis is
`SeparatelyContinuousAdd` rather than a topological ring.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.44(2), towards which this
  is the topological step.
-/

public section

namespace Valuation

variable {A : Type*} [Ring A] [TopologicalSpace A] [SeparatelyContinuousAdd A]
  {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **A sublevel set is open as soon as its trace on an open subset containing `0` is.**

The two sets are not related by the topology — the trace is in general far smaller. What carries the
openness across is that `{a | v a < γ}` is an additive subgroup, and a subgroup which is a
neighbourhood of `0` is open; openness of `U` is what makes the trace such a neighbourhood. -/
theorem isOpen_lt_of_isOpen_trace_lt {U : Set A} (hU : IsOpen U) (hU0 : (0 : A) ∈ U)
    {v : Valuation A Γ₀} {γ : Γ₀} (h : IsOpen {u : U | v (u : A) < γ}) :
    IsOpen {a : A | v a < γ} := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  have himage : IsOpen ((↑) '' {u : U | v (u : A) < γ} : Set A) := hU.isOpenMap_subtype_val _ h
  have hzero : (0 : A) ∈ ((↑) '' {u : U | v (u : A) < γ} : Set A) :=
    ⟨⟨0, hU0⟩, by simpa using zero_lt_iff.mpr hγ, rfl⟩
  rw [← coe_ltAddSubgroupOfNeZero (v := v) hγ]
  refine (v.ltAddSubgroupOfNeZero hγ).isOpen_of_mem_nhds (g := 0)
    (Filter.mem_of_superset (himage.mem_nhds hzero) ?_)
  rintro _ ⟨u, hu, rfl⟩
  simpa using hu

/-- **A sufficient criterion for continuity, tested on an open subset containing `0`.** If every
sublevel set of `v` has open trace on `U`, then `v` is continuous.

The hypothesis quantifies `γ` over the whole codomain, which is strictly stronger than continuity of
the restriction of `v` to a subring carried by `U`: the latter is the attained-value predicate and
supplies openness only at values `v` takes on that subring. So this does **not** combine with
`Valuation.IsContinuous.comap` to give Wedhorn's equality `Cont(A) = g⁻¹(Cont(B))` — see the module
docstring for what closing that gap would cost. -/
theorem isContinuous_of_isOpen_trace_lt {U : Set A} (hU : IsOpen U) (hU0 : (0 : A) ∈ U)
    {v : Valuation A Γ₀} (h : ∀ γ : Γ₀, IsOpen {u : U | v (u : A) < γ}) : v.IsContinuous :=
  isContinuous_of_forall_isOpen_lt fun γ ↦ isOpen_lt_of_isOpen_trace_lt hU hU0 (h γ)

end Valuation
