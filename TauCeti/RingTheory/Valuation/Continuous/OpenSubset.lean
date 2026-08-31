/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RingTheory.Valuation.Continuous.Basic
import TauCeti.RingTheory.Valuation.LtAddSubgroup

/-!
# A sufficient criterion for continuity, tested on a neighbourhood of zero

If `U` is a neighbourhood of `0` in `A`, and the sublevel set at each attained value `v b` has open
trace on `U`, then `v` is continuous on `A`. Continuity of a valuation is thus detected on any one
neighbourhood of `0`.

## The mechanism

The threshold `γ = 0` is a separate and trivial case throughout: `{a | v a < 0}` is empty, hence
open, and every result below holds there for that reason alone. The description that follows is of
the case `γ ≠ 0`, which is where all the content sits.

The whole content is that `{a | v a < γ}` is then an **additive subgroup** —
`Valuation.ltAddSubgroupOfNeZero`, which is indexed by a proof of `γ ≠ 0` for exactly this reason —
and a subgroup which is a neighbourhood of `0` is open. That step is isolated as
`Valuation.isOpen_lt_of_mem_nhds_zero`, in which no test set appears at all.

A test set enters only as one way of producing that neighbourhood. The trace `{u : U | v u < γ}` is
in general far smaller than `{a : A | v a < γ}`, so openness does not pass between them for
topological reasons. Openness in the subspace topology says the trace is `V ∩ U` for some ambient
open `V`; that `V` contains `0`, since `v 0 = 0 < γ`, so `V ∩ U` is a neighbourhood of `0` as soon
as `U` is one, and it lies inside the sublevel set.

That argument needs no more than continuity of translation by a fixed element, so it is stated over
`[SeparatelyContinuousAdd A]` and over a `LinearOrderedCommMonoidWithZero` codomain, in keeping with
`TauCeti/RingTheory/Valuation/Continuous/Basic.lean`, which asks for compatibility per result rather
than up front. No Huber-ring hypothesis and no ideal of definition enter.

## Why a neighbourhood and not an open subring

The intended instantiation is a ring of definition `A₀` of a Huber ring `A`, which is an open
subring; that is the shape in which Wedhorn uses the criterion. The argument, however, consumes no
closure property of the test set whatever — neither additive nor multiplicative — and not even
openness: only that `U` is a neighbourhood of `0`. Additive closure *is* essential to the proof, but
of the sublevel set rather than of `U`: it is exactly the subgroup step above. Stating the result
for an open subring would therefore carry hypotheses the proof never uses, so the subring case is
left to the caller, who supplies `A₀.zero_mem` and `IsOpen.mem_nhds`.

## What is *not* proved here

This is the topological step towards Wedhorn's Lemma 7.44(2), `Cont(A) = g⁻¹(Cont(B))` for `B` an
open subring — **but it is not that lemma**, and the gap is recorded here rather than papered over.

The hypothesis asks for open trace at every value `v b` that `v` attains **on `A`**. Continuity of
the restriction `v.comap B.subtype` supplies less: being the attained-value predicate, it gives
openness only at the values `v` attains **on `B`**. So this criterion does not combine with
`Valuation.IsContinuous.comap` — which is the easy inclusion, and is already available — to give the
equality of Lemma 7.44(2).

Closing that gap means reaching a threshold `v a` for `a : A` from the values attained on `B`, that
is, writing it as a ratio. That needs a value *group* rather than a monoid, and it needs `B` to
absorb elements of `A` after multiplication by a topologically nilpotent element — Wedhorn states
7.44 for an `f`-adic `A` precisely because that is what supplies such elements. Both hypotheses are
outside this file, which is why the criterion is stated in the honest, weaker form instead of being
advertised as the lemma.

The same caveat applies to the source: AINTLIB's `isContinuous_of_restriction_isContinuous` carries
a codomain-quantified hypothesis, although its docstring names it "Wedhorn Lemma 7.44(2)".

## Main results

* `Valuation.isOpen_lt_of_mem_nhds_zero` : a sublevel set of `v` is open as soon as it is a
  neighbourhood of `0`.
* `Valuation.isOpen_lt_of_isOpen_trace_lt` : hence it is open as soon as its trace on an open
  subset containing `0` is.
* `Valuation.isContinuous_of_forall_isOpen_trace_lt` : hence `v` is continuous as soon as the
  sublevel set at every attained value has open trace.

## Roadmap

`AdicSpaces`, README §1.5 "Continuous valuations". That section asks for `Cont A`, Theorem 7.10 and
Corollary 7.12, and then for `Cont A` to be shown *independent of the chosen pair of definition*.
Its earlier stages are already in place on `main`: Theorem 7.10 as an equality in
`ValuationSpectrum.cont_eq_spvOfIdeal_inter_setOfPred_forall_vlt_one`, and Corollary 7.12 as
`ValuationSpectrum.isClosed_val_preimage_cont` together with the `SpectralSpace (cont A)` instance
for a Huber ring. Independence is the next item, and is a comparison between continuity tested on
one ring of definition and on another, both open subrings of `A`; Wedhorn runs it through Lemma
7.44. This file supplies the topological half of that comparison — the passage from openness on a
ring of definition to openness on `A` — which is the direction the independence argument consumes.

## Provenance

Adapted from AINTLIB ([`github.com/CBirkbeck/AINTLIB`](https://github.com/CBirkbeck/AINTLIB),
Apache-2.0, Chris Birkbeck) at commit `37bbdaeb9`, file
`projects/AdicSpaces/Adic spaces/Lemma745.lean` line 144,
`PairOfDefinition.isContinuous_of_restriction_isContinuous`, which names Wedhorn's Lemma 7.44(2) in
its docstring. The argument is the same; the statement here is weaker on four axes. That development
fixes an ambient `PairOfDefinition` and phrases the hypothesis through its ring of definition, asks
for openness at *every* `γ` of the codomain, works over a `LinearOrderedCommGroupWithZero` codomain,
and closes through Mathlib's `Valuation.ltAddSubgroup`, which is indexed by units of the codomain
and so forces that group hypothesis. Here the carrier is an arbitrary open subset containing `0`,
the thresholds range only over the attained values `v b`, the codomain is a monoid, and the
ambient hypothesis is `SeparatelyContinuousAdd` rather than a topological ring.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.44(2), towards which this
  is the topological step.
-/

public section

namespace Valuation

open Topology

variable {A : Type*} [Ring A] [TopologicalSpace A] [SeparatelyContinuousAdd A]
  {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **A sublevel set which is a neighbourhood of `0` is open.**

This is the entire mechanism. For `γ ≠ 0` the sublevel set is an additive subgroup, and a subgroup
which is a neighbourhood of `0` is open; for `γ = 0` it is empty, hence open outright, and the
hypothesis is not used. Nothing about a test set enters. -/
theorem isOpen_lt_of_mem_nhds_zero {v : Valuation A Γ₀} {γ : Γ₀}
    (h : {a : A | v a < γ} ∈ 𝓝 (0 : A)) : IsOpen {a : A | v a < γ} := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  rw [← coe_ltAddSubgroupOfNeZero (v := v) hγ]
  exact (v.ltAddSubgroupOfNeZero hγ).isOpen_of_mem_nhds (g := 0)
    (by rwa [coe_ltAddSubgroupOfNeZero hγ])

/-- **A sublevel set is open as soon as its trace on a neighbourhood of `0` is.**

The two sets are not related by the topology — the trace is in general far smaller. `U` itself need
not be open. For `γ ≠ 0`, openness of the trace in the subspace topology exhibits it as `V ∩ U` for
an ambient open `V`; that `V` contains `0` because `v 0 = 0 < γ`, so `V ∩ U` is a neighbourhood of
`0` lying inside the sublevel set, and `isOpen_lt_of_mem_nhds_zero` does the rest. For `γ = 0` both
sets are empty and there is nothing to prove. -/
theorem isOpen_lt_of_isOpen_trace_lt {U : Set A} (hU : U ∈ 𝓝 (0 : A))
    {v : Valuation A Γ₀} {γ : Γ₀} (h : IsOpen {u : U | v (u : A) < γ}) :
    IsOpen {a : A | v a < γ} := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp h
  have h0U : (0 : A) ∈ U := mem_of_mem_nhds hU
  have h0V : (⟨0, h0U⟩ : U) ∈ Subtype.val ⁻¹' V := by
    rw [hVU]; simpa using zero_lt_iff.mpr hγ
  refine isOpen_lt_of_mem_nhds_zero (Filter.mem_of_superset
    (Filter.inter_mem (hV.mem_nhds h0V) hU) ?_)
  rintro a ⟨haV, haU⟩
  have hmem : (⟨a, haU⟩ : U) ∈ Subtype.val ⁻¹' V := haV
  rw [hVU] at hmem
  simpa using hmem

/-- **A sufficient criterion for continuity, tested on a neighbourhood of `0`.** If the
sublevel set at each attained value `v b` has open trace on `U`, then `v` is continuous.

The thresholds range over the values `v` attains on all of `A`, which is strictly more than
continuity of the restriction of `v` to a subring carried by `U` supplies: that is the
attained-value predicate for the subring, so it gives openness only at the values `v` takes on the
subring. So this does **not** combine with `Valuation.IsContinuous.comap` to give Wedhorn's equality
`Cont(A) = g⁻¹(Cont(B))` — see the module docstring for what closing that gap would cost. -/
theorem isContinuous_of_forall_isOpen_trace_lt {U : Set A} (hU : U ∈ 𝓝 (0 : A))
    {v : Valuation A Γ₀} (h : ∀ b : A, IsOpen {u : U | v (u : A) < v b}) : v.IsContinuous :=
  isContinuous_def.mpr fun b ↦ isOpen_lt_of_isOpen_trace_lt hU (h b)

end Valuation
