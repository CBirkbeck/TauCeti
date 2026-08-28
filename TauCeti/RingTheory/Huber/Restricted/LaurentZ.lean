/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.Restricted.PowerSeries

/-!
# The two-sided restricted Laurent coefficient object

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Example 6.39.** For a Tate ring `A`, the ring
`A⟨X, X⁻¹⟩` consists of the two-sided formal series `∑_{n ∈ ℤ} aₙ Xⁿ` whose coefficients satisfy:
for every neighbourhood `U` of zero, all but finitely many `aₙ` lie in `U`. This file carries the
*coefficient object* — the families themselves, with extensionality — and nothing else. The ring
structure (convolution), its topology, and the presentation `A⟨X, Y⟩/(XY - 1)` are separate.

## Not to be confused with `TauCeti.RingTheory.Huber.Restricted.Laurent`

That module is titled "The Laurent quotients `A⟨X⟩/(f - X)` and `A⟨X⟩/(1 - f X)` are flat" and
serves Wedhorn 8.31(2) and Example 6.38. Its series are indexed by `ℕ` — it works inside
`MvPowerSeries (Fin 1) A` — and its content is `mulX`, `restrictedX` and flatness of two
quotients. The object here is indexed by `ℤ` and is not a quotient of anything. The two share the
word "Laurent" and nothing else; neither subsumes the other.

## Why `Filter.zeroAtFilterSubmodule`

This is the idiom already in use for the one-sided object:
`TauCeti.Huber.IsRestricted` is defined as `Tendsto (coeff f) cofinite (𝓝 0)`, and
`TauCeti.Huber.isRestricted_iff` records that this *is* Mathlib's `Filter.ZeroAtFilter` at
`cofinite`. Wedhorn's condition on a two-sided family is that same condition at index type `ℤ`
rather than `Fin k →₀ ℕ`, so it is built the same way: `restrictedMvPowerSeriesSubmodule` is
`Filter.zeroAtFilterSubmodule A (cofinite : Filter (Fin k →₀ ℕ))`, and this is the same
combinator at `cofinite : Filter ℤ`. `finite_notMem_of_mem_laurentRestricted` recovers Wedhorn's
own phrasing.

## Main definitions

* `TauCeti.Huber.laurentRestricted` : the coefficient families, as a submodule of `ℤ → A`.

## Main results

* `TauCeti.Huber.finite_notMem_of_mem_laurentRestricted` : Wedhorn's condition verbatim.
* `TauCeti.Huber.laurentRestricted_ext` : coefficientwise extensionality.
-/

public section

open Filter

open scoped Topology

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [ContinuousAdd A]
  [ContinuousConstSMul A A]

/-- **Wedhorn Example 6.39**, the coefficient families of `A⟨X, X⁻¹⟩`: two-sided families
`a : ℤ → A` such that for every neighbourhood `U` of zero, `aₙ ∈ U` for all but finitely many
`n` — that is, `a` tends to `0` along `cofinite`. -/
def laurentRestricted (A : Type*) [CommRing A] [TopologicalSpace A] [ContinuousAdd A]
    [ContinuousConstSMul A A] : Submodule A (ℤ → A) :=
  Filter.zeroAtFilterSubmodule A (Filter.cofinite : Filter ℤ)

/-- Membership, unfolded. -/
theorem mem_laurentRestricted_iff {a : ℤ → A} :
    a ∈ laurentRestricted A ↔ ZeroAtFilter cofinite a := (Iff.rfl)

/-- **Wedhorn's condition verbatim**: for every open additive subgroup, all but finitely many
coefficients lie in it. -/
theorem finite_notMem_of_mem_laurentRestricted {a : ℤ → A} (ha : a ∈ laurentRestricted A)
    (W : OpenAddSubgroup A) : {n : ℤ | a n ∉ (W : Set A)}.Finite := by
  have := (tendsto_nhds.mp ha) _ W.isOpen (SetLike.mem_coe.mpr W.zero_mem)
  rwa [Filter.mem_cofinite] at this

/-- **Coefficientwise extensionality.** -/
@[ext]
theorem laurentRestricted_ext {a b : laurentRestricted A}
    (h : ∀ n : ℤ, (a : ℤ → A) n = (b : ℤ → A) n) : a = b :=
  Subtype.ext (funext h)

end TauCeti.Huber
