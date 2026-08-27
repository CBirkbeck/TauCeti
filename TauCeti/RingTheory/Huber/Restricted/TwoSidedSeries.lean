/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.PowerSeries

/-!
# Two-sided restricted series `A⟨X, X⁻¹⟩`

Wedhorn's Example 6.39 introduces, for a Tate ring `A`, the ring of formal series
`∑_{n ∈ ℤ} aₙ Xⁿ` whose coefficients satisfy a convergence condition: for every neighbourhood `U`
of zero, all but finitely many `aₙ` lie in `U`. This module builds the underlying coefficient
object — the `A`-module of such two-sided families — together with its coefficients and
extensionality.

The condition is exactly the one `TauCeti.Huber.IsRestricted` already expresses for the
one-sided series `A⟨X₁, …, Xₖ⟩`: a coefficient family tending to `0` along the cofinite filter,
i.e. Mathlib's `Filter.ZeroAtFilter` at `Filter.cofinite`. Nothing in that predicate refers to the
shape of the index set, so the two-sided object is the same notion indexed by `ℤ` rather than by
`Fin k →₀ ℕ`, and is built from the same Mathlib primitive
(`Filter.zeroAtFilterSubmodule`) that `TauCeti.Huber.restrictedMvPowerSeriesSubmodule` is built
from.

## Why this file is not called `Laurent`

Two neighbouring modules already use that word for different objects, and a third meaning would be
a placement hazard:

* `TauCeti.RingTheory.Huber.Restricted.Laurent` is Wedhorn's **Example 6.38** — the *Laurent
  rational subsets* `{|f| ≤ 1}` and `{|f| ≥ 1}`, whose coordinate rings `A⟨X⟩/(f - X)` and
  `A⟨X⟩/(1 - f X)` are quotients of the **one-sided** `A⟨X⟩`. Those are the two *pieces* of the
  cover whose *overlap* is the ring this file serves.
* `TauCeti.RingTheory.Huber.LaurentSeries` is the formal Laurent series **field** `K⸨X⸩` over a
  *field* `K` with the `X`-adic topology. That is a different object in three ways: its base is a
  field rather than an arbitrary Tate ring, its series have only finitely many negative terms, and
  its topology is `X`-adic rather than coefficientwise. It is **not** reusable here; the
  distinguishing feature is precisely the convergence condition on the coefficients.

## Main definitions

* `TauCeti.Huber.twoSidedRestrictedSubmodule`: the `A`-module of two-sided restricted families,
  the coefficient object underlying `A⟨X, X⁻¹⟩`.

## Main results

* `TauCeti.Huber.zeroAtFilter_cofinite_iff_finite_notMem`: over a nonarchimedean additive group,
  a family tends to `0` cofinitely **iff** all but finitely many of its members lie in each open
  additive subgroup. This is Wedhorn's phrasing of the condition, and the `←` direction is what
  makes it usable as a criterion rather than only as a consequence. Stated for an arbitrary index
  type, since neither direction looks at the index set.
* `TauCeti.Huber.mem_twoSidedRestrictedSubmodule_iff_finite_notMem`: that criterion at `ℤ`, which
  is Example 6.39's defining condition verbatim.
* `TauCeti.Huber.twoSidedRestrictedSubmodule_ext`: coefficientwise extensionality.

## Implementation notes

Only the additive and `A`-module structure is built here. The **ring** structure is deliberately
absent: the coefficient convolution `(fg)ₙ = ∑_{i + j = n} aᵢ bⱼ` is a *finite* sum for one-sided
series — which is what `TauCeti.Huber.IsRestricted.mul` exploits, through
`MvPowerSeries.coeff_mul` over a finite antidiagonal — but over `ℤ` that antidiagonal is infinite,
so multiplication needs a summability argument in a complete ring rather than a rearrangement of a
finite sum. That is separate work and does not belong to this rung.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.39.
-/

public section

open Filter Topology

namespace TauCeti.Huber

section Criterion

variable {ι : Type*} {G : Type*} [AddGroup G] [TopologicalSpace G]

/-- **Restrictedness, as Wedhorn states it.** A family tends to `0` along the cofinite filter
exactly when, for every open additive subgroup `W`, all but finitely many of its members lie in
`W`.

The `→` direction holds in any topological additive group, and is the form
`TauCeti.Huber.IsRestricted.finite_coeff_notMem` records for one-sided series. The `←` direction
is where nonarchimedeanness enters: it supplies an open subgroup inside each neighbourhood of
zero, which turns the family of open subgroups into a neighbourhood basis and so upgrades the
consequence into a criterion.

Neither direction inspects the index set, so `ι` is arbitrary. -/
theorem zeroAtFilter_cofinite_iff_finite_notMem [NonarchimedeanAddGroup G] {f : ι → G} :
    ZeroAtFilter cofinite f ↔ ∀ W : OpenAddSubgroup G, {n | f n ∉ (W : Set G)}.Finite := by
  refine ⟨fun hf W ↦ ?_, fun h ↦ ?_⟩
  · have := (tendsto_nhds.mp hf) _ W.isOpen (SetLike.mem_coe.mpr W.zero_mem)
    rwa [Filter.mem_cofinite] at this
  · refine tendsto_nhds.mpr fun U hU h0 ↦ ?_
    obtain ⟨W, hWU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U (hU.mem_nhds h0)
    rw [Filter.mem_cofinite]
    exact (h W).subset fun n hn ↦ fun hnW ↦ hn (hWU hnW)

end Criterion

section Submodule

variable (A M : Type*) [Semiring A] [AddCommMonoid M] [TopologicalSpace M] [Module A M]
  [ContinuousAdd M] [ContinuousConstSMul A M]

/-- **The two-sided restricted families `A⟨X, X⁻¹⟩`** of Wedhorn's Example 6.39: the `A`-module of
families `ℤ → M` tending to `0` along the cofinite filter, i.e. those `∑_{n ∈ ℤ} aₙ Xⁿ` for which
every neighbourhood of zero omits only finitely many coefficients.

This is `TauCeti.Huber.restrictedMvPowerSeriesSubmodule`'s condition at the index set `ℤ`, and is
built from the same Mathlib primitive. -/
def twoSidedRestrictedSubmodule : Submodule A (ℤ → M) :=
  Filter.zeroAtFilterSubmodule A (Filter.cofinite : Filter ℤ)

variable {A M}

/-- Membership in `A⟨X, X⁻¹⟩` is the convergence condition on the coefficients. -/
@[simp]
theorem mem_twoSidedRestrictedSubmodule {f : ℤ → M} :
    f ∈ twoSidedRestrictedSubmodule A M ↔ ZeroAtFilter cofinite f := (Iff.rfl)

/-- **Coefficientwise extensionality** for `A⟨X, X⁻¹⟩`: a two-sided restricted family is
determined by its coefficients. This is the uniqueness statement the two-piece Laurent cover's
diagram chase consumes when it compares `∑ aₖ ζᵏ` with `∑ bₖ ζ⁻ᵏ`. -/
@[ext]
theorem twoSidedRestrictedSubmodule_ext {f g : twoSidedRestrictedSubmodule A M}
    (h : ∀ n, (f : ℤ → M) n = (g : ℤ → M) n) : f = g :=
  Subtype.ext (funext h)

end Submodule

section WedhornCriterion

variable {A M : Type*} [Semiring A] [AddCommGroup M] [TopologicalSpace M] [Module A M]
  [ContinuousConstSMul A M] [NonarchimedeanAddGroup M]

/-- **Example 6.39's defining condition, verbatim**: a two-sided family lies in `A⟨X, X⁻¹⟩`
exactly when, for every open additive subgroup, only finitely many of its coefficients lie
outside. -/
theorem mem_twoSidedRestrictedSubmodule_iff_finite_notMem {f : ℤ → M} :
    f ∈ twoSidedRestrictedSubmodule A M ↔
      ∀ W : OpenAddSubgroup M, {n | f n ∉ (W : Set M)}.Finite :=
  zeroAtFilter_cofinite_iff_finite_notMem

end WedhornCriterion

end TauCeti.Huber
