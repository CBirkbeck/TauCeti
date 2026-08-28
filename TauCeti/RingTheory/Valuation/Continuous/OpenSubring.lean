/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RingTheory.Valuation.Continuous.Basic

/-!
# A sufficient criterion for continuity, tested on an open subring

If `B` is an open subring of `A` and *every* sublevel set `{b : B | v b < γ}` is open in `B`,
then `v` is continuous on `A`. This is the topological step towards Wedhorn's Lemma 7.44(2),
`Cont(A) = g⁻¹(Cont(B))` — **but it is not that lemma**, and the gap is recorded below rather
than papered over.

## What is *not* proved here

The hypothesis quantifies `γ` over the whole codomain. Continuity of the restriction
`v.comap B.subtype` is weaker: being the attained-value predicate, it supplies openness only at
the values `v` takes **on `B`**. So this criterion does not combine with
`Valuation.IsContinuous.comap` — which is the easy inclusion, and is already on `main` — to give
the equality of Lemma 7.44(2).

Closing that gap means reaching a general `γ` from the values attained on `B`, i.e. writing it as
a ratio. That needs a value *group* rather than a monoid, and it needs `B` to absorb elements of
`A` after multiplication by a topologically nilpotent element — Wedhorn states 7.44 for an
`f`-adic `A` precisely because that is what supplies such elements. Both hypotheses are outside
this file, which is why the criterion is stated in the honest, weaker form instead of being
advertised as the lemma.

The same caveat applies to the source: AINTLIB's `isContinuous_of_restriction_isContinuous`
carries the identical codomain-quantified hypothesis, although its docstring names it
"Wedhorn Lemma 7.44(2)".

## The mechanism

The trace `{b : B | v b < γ}` is in general far smaller than `{a : A | v a < γ}`, so openness
does not pass between them for topological reasons. What carries it is that the larger set is an
**additive subgroup** — by the strict triangle inequality `v (x + y) ≤ max (v x) (v y)` — and a
subgroup that is a neighbourhood of `0` is open. Openness of `B` is exactly what promotes the
trace, open in the subspace topology, to a neighbourhood of `0` in `A`.

That argument needs no more than continuity of translation by a fixed element, so it is stated
over `[SeparatelyContinuousAdd A]` and over a `LinearOrderedCommMonoidWithZero` codomain, in
keeping with `Valuation.Continuous.Basic`, which asks for compatibility per result rather than up
front. No Huber-ring hypothesis and no ideal of definition enter.

## Main results

* `Valuation.isOpen_lt_of_isOpen_subring_lt` : a sublevel set of `v` is open as soon as its
  trace on an open subring is.
* `Valuation.isContinuous_of_isOpen_subring_lt` : hence `v` is continuous as soon as every
  sublevel set has open trace.

## Provenance

Adapted from AINTLIB ([`github.com/CBirkbeck/AINTLIB`](https://github.com/CBirkbeck/AINTLIB),
Apache-2.0, Chris Birkbeck) at commit `37bbdaeb9`, file
`projects/AdicSpaces/Adic spaces/Lemma745.lean` line 144,
`PairOfDefinition.isContinuous_of_restriction_isContinuous`, which names Wedhorn's Lemma 7.44(2)
in its docstring while assuming, as here, openness for every `γ` of the codomain.
The argument is the same; the statement here is weaker on three axes. That development fixes an
ambient `PairOfDefinition` and phrases the hypothesis through its ring of definition, works over a
`LinearOrderedCommGroupWithZero` codomain, and closes through Mathlib's `Valuation.ltAddSubgroup`,
which is indexed by units of the codomain and so forces that group hypothesis. Here the subring is
arbitrary, the codomain is a monoid — the sublevel subgroup being built where it is used, as
`TauCeti.Huber.PairOfDefinition.isContinuous_iff_forall_exists_idealImage_subset` also does — and
the ambient hypothesis is `SeparatelyContinuousAdd` rather than a topological ring.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.44(2), towards which
  this is the topological step.
-/

public section

namespace Valuation

open Set Topology

variable {A : Type*} [Ring A] [TopologicalSpace A]
  {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **A sublevel set is open as soon as its trace on an open subring is.**

The two sets are not related by the topology — the trace is in general far smaller. What carries
the openness across is that `{a | v a < γ}` is an additive subgroup, by the strict triangle
inequality, and a subgroup which is a neighbourhood of `0` is open; openness of `B` is what makes
the trace such a neighbourhood. -/
theorem isOpen_lt_of_isOpen_subring_lt [SeparatelyContinuousAdd A] {B : Subring A}
    (hB : IsOpen (B : Set A)) {v : Valuation A Γ₀} {γ : Γ₀}
    (h : IsOpen {b : B | v (b : A) < γ}) : IsOpen {a : A | v a < γ} := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  have h0 : (0 : Γ₀) < γ := zero_lt_iff.mpr hγ
  let S : AddSubgroup A :=
    { carrier := {a : A | v a < γ}
      add_mem' := fun ha hb ↦ lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb)
      zero_mem' := by simpa using h0
      neg_mem' := fun {x} hx ↦ by simpa [v.map_neg] using hx }
  have hopen : IsOpen ((Subtype.val : B → A) '' {b : B | v (b : A) < γ}) :=
    hB.isOpenMap_subtype_val _ h
  have hmem : (0 : A) ∈ (Subtype.val : B → A) '' {b : B | v (b : A) < γ} :=
    ⟨⟨0, B.zero_mem⟩, by simpa using h0, rfl⟩
  refine S.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hopen.mem_nhds hmem) ?_)
  rintro _ ⟨b, hb, rfl⟩
  exact hb

/-- **A sufficient criterion for continuity, tested on an open subring.** If every sublevel set
of `v` has open trace on the open subring `B`, then `v` is continuous.

The hypothesis quantifies `γ` over the whole codomain, which is strictly stronger than continuity
of the restriction `v.comap B.subtype`: the latter is the attained-value predicate and supplies
openness only at values `v` takes on `B`. So this does **not** combine with
`Valuation.IsContinuous.comap` to give Wedhorn's equality `Cont(A) = g⁻¹(Cont(B))` — see the
module docstring for what closing that gap would cost. -/
theorem isContinuous_of_isOpen_subring_lt [SeparatelyContinuousAdd A] {B : Subring A}
    (hB : IsOpen (B : Set A)) {v : Valuation A Γ₀}
    (h : ∀ γ : Γ₀, IsOpen {b : B | v (b : A) < γ}) : v.IsContinuous :=
  isContinuous_of_forall_isOpen_lt fun γ ↦ isOpen_lt_of_isOpen_subring_lt hB (h γ)

end Valuation
