/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.OpenAddSubgroupBasis

/-!
# Cofinite convergence in a nonarchimedean group is a finiteness condition

In a nonarchimedean additive group the open subgroups form a basis of neighbourhoods of zero, so
a family converges to zero along the cofinite filter exactly when each open subgroup omits only
finitely many of its members.

The `→` direction is available in any topological additive group: an open subgroup is a
neighbourhood of zero, so cofinitely many members lie in it. It is nonarchimedeanness that gives
the converse, and with it the upgrade from a *consequence* of convergence to a *criterion* for it.

Nothing here looks at the index type, so it is arbitrary.

## Main results

* `NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem`
* `NonarchimedeanAddGroup.zeroAtFilter_cofinite_tsum_fiber`
-/

public section

open Filter Topology

namespace NonarchimedeanAddGroup

variable {ι : Type*} {G : Type*} [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]

/-- **Cofinite convergence, as a finiteness condition on open subgroups.** A family tends to `0`
along the cofinite filter exactly when, for every open additive subgroup `W`, all but finitely
many of its members lie in `W`.

Both directions are the single fact that the open subgroups are a basis of `𝓝 0`
(`NonarchimedeanAddGroup.nhds_zero_hasBasis_openAddSubgroup`), read through
`Filter.HasBasis.tendsto_right_iff`: convergence along a filter is membership of each basic
neighbourhood eventually, and `Filter.eventually_cofinite` turns "eventually along `cofinite`"
into the finiteness of the exceptional set. -/
theorem zeroAtFilter_cofinite_iff_finite_notMem {f : ι → G} :
    ZeroAtFilter cofinite f ↔ ∀ W : OpenAddSubgroup G, {n | f n ∉ (W : Set G)}.Finite := by
  simp only [ZeroAtFilter, (nhds_zero_hasBasis_openAddSubgroup G).tendsto_right_iff, true_implies,
    Filter.eventually_cofinite]

/-- **Summing along the fibres of an arbitrary map preserves cofinite convergence.** If `F` tends
to `0` along the cofinite filter, then so does `n ↦ ∑' i ∈ p ⁻¹' {n}, F i`, for *any* `p`. No
hypothesis on `p` is needed and the fibres may well be infinite.

The point is that the two finiteness conditions match up: an open subgroup `W` omits only finitely
many `F i`, so only finitely many fibres contain an omitted term, and over every other fibre each
term lies in `W`. Such a fibre sums back into `W` because an open subgroup is also *closed*
(`OpenAddSubgroup.isClosed`), so it contains the limit of its partial sums (`tsum_mem`) — including
in the degenerate case where the fibre is not summable, since then the sum is `0 ∈ W` by
convention.

This is the engine behind convolution: taking `p` to be addition `ι × ι → ι` says that a
coefficientwise convolution of cofinitely-null families is again cofinitely null, with the infinite
antidiagonal costing nothing. Mathlib's `HasSum.tsum_fiberwise` regroups a *summable* family along
the fibres of `p`; this is its cofinite-nullity counterpart, needing neither summability nor a
separation axiom, which is what lets a convolution be defined before completeness enters. -/
theorem zeroAtFilter_cofinite_tsum_fiber {κ : Type*} {H : Type*} [AddCommGroup H]
    [TopologicalSpace H] [NonarchimedeanAddGroup H] {F : ι → H} (hF : ZeroAtFilter cofinite F)
    (p : ι → κ) : ZeroAtFilter cofinite fun n ↦ ∑' i : {i // p i = n}, F i.1 := by
  rw [zeroAtFilter_cofinite_iff_finite_notMem] at hF ⊢
  refine fun W ↦ ((hF W).image p).subset fun n hn ↦ ?_
  by_contra hnot
  exact hn (tsum_mem W.isClosed fun i ↦ not_not.mp fun h ↦ hnot ⟨i.1, h, i.2⟩)

end NonarchimedeanAddGroup
