/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Filter.ZeroAndBoundedAtFilter
public import TauCeti.Topology.Algebra.Nonarchimedean.ZeroAtFilter

/-!
# Two-sided restricted series `A⟨X, X⁻¹⟩`

Wedhorn's Example 6.39 introduces, for a Tate ring `A`, the ring of formal series
`∑_{n ∈ ℤ} aₙ Xⁿ` whose coefficients satisfy a convergence condition: for every neighbourhood `U`
of zero, all but finitely many `aₙ` lie in `U`. This module builds the underlying coefficient
object — the `A`-module of such two-sided families — together with its coefficients,
extensionality, and the decomposition of that module by degree.

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
* `TauCeti.Huber.disjoint_pi_bot_of_disjoint_compl`: disjoint index sets give disjoint
  submodules of families vanishing outside them. Stated for
  an arbitrary set because nothing in it is about `ℤ` or about the sign of a degree; Mathlib has
  the `Finsupp` analogue, `Finsupp.supported`, but no `Pi` one.

## Main results

* `TauCeti.Huber.mem_twoSidedRestrictedSubmodule_iff_finite_notMem`: Example 6.39's defining
  condition verbatim — membership is the finiteness condition on open additive subgroups. It is
  the `ℤ` case of `NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem`, which is
  stated for an arbitrary index type in
  `TauCeti/Topology/Algebra/Nonarchimedean/ZeroAtFilter.lean` because neither direction of it
  looks at the index set or at series.
* `TauCeti.Huber.twoSidedRestrictedSubmodule_ext`: coefficientwise extensionality.
* `TauCeti.Huber.twoSidedRestrictedSubmodule_eq_sup` and
  `TauCeti.Huber.disjoint_twoSidedRestricted_nonneg_neg`: **the degree decomposition and its
  directness** — `A⟨X, X⁻¹⟩` is the sum of its non-negative and negative parts, and that sum is
  direct. This is fact (i) of Wedhorn's Lemma 8.33 at the level of coefficients, and it is what
  the diagram chase there needs; the Example 6.39 universal property does not supply it.
* `TauCeti.Huber.zeroAtFilter_of_forall_eq_or_eq_zero`: zeroing coefficients keeps a family
  restricted. Stated pointwise rather than for an indicator, so it carries no decidability
  hypothesis; it is what makes the decomposition land inside the submodule rather than merely
  inside `ℤ → M`.

## Implementation notes

Only the additive and `A`-module structure is built here. The **ring** structure is deliberately
absent: the coefficient convolution `(fg)ₙ = ∑_{i + j = n} aᵢ bⱼ` is a *finite* sum for one-sided
series — which is what `TauCeti.Huber.IsRestricted.mul` exploits, through
`MvPowerSeries.coeff_mul` over a finite antidiagonal — but over `ℤ` that antidiagonal is infinite,
so multiplication needs a summability argument in a complete ring rather than a rearrangement of a
finite sum. That is separate work and does not belong to this rung.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.39 and §8.2.1,
  Lemma 8.33.
-/

public section

open Filter Topology

namespace TauCeti.Huber

section Submodule

variable (A M : Type*) [Semiring A] [AddCommMonoid M] [TopologicalSpace M] [Module A M]
  [ContinuousAdd M] [ContinuousConstSMul A M]

/-- **The two-sided restricted `M`-valued families**: the `A`-module of families `ℤ → M` tending
to `0` along the cofinite filter, i.e. those whose coefficients leave every neighbourhood of zero
finitely often.

At `M = A` this is the coefficient object of Wedhorn's `A⟨X, X⁻¹⟩` (Example 6.39). It is only the
*coefficients*: no ring structure is defined here, so this is not yet that algebra — see the
implementation notes.

This is `TauCeti.Huber.restrictedMvPowerSeriesSubmodule`'s condition at the index set `ℤ`, and is
built from the same Mathlib primitive. -/
def twoSidedRestrictedSubmodule : Submodule A (ℤ → M) :=
  Filter.zeroAtFilterSubmodule A (Filter.cofinite : Filter ℤ)

variable {A M}

/-- Membership is the convergence condition on the coefficient family. -/
@[simp]
theorem mem_twoSidedRestrictedSubmodule {f : ℤ → M} :
    f ∈ twoSidedRestrictedSubmodule A M ↔ ZeroAtFilter cofinite f := (Iff.rfl)

/-- **Coefficientwise extensionality**: two members of the submodule that agree at every index are
equal. This is subtype-and-function extensionality, nothing more — in particular it does *not* say
that a coefficient family is recovered from any sum it represents, which would need an evaluation
map that does not exist until there is a ring structure. -/
@[ext]
theorem twoSidedRestrictedSubmodule_ext {f g : twoSidedRestrictedSubmodule A M}
    (h : ∀ n, (f : ℤ → M) n = (g : ℤ → M) n) : f = g :=
  Subtype.ext (funext h)

end Submodule

section WedhornCriterion

variable {A M : Type*} [Semiring A] [AddCommGroup M] [TopologicalSpace M] [Module A M]
  [ContinuousConstSMul A M] [NonarchimedeanAddGroup M]

/-- **The membership criterion in Wedhorn's form**: a family lies in the submodule exactly when,
for every open additive subgroup, only finitely many of its members lie outside. At `M = A` this
is Example 6.39's defining condition on the coefficients, verbatim.

Deliberately **not** `@[simp]`: `mem_twoSidedRestrictedSubmodule` is already `@[simp]` and rewrites
this left-hand side to `ZeroAtFilter cofinite f`, so tagging this one too fails the `simpNF` linter
— simp reaches the membership unfolding first and this lemma can never fire. The `@[simp]` stays on
the membership lemma, matching the one-sided `mem_restrictedMvPowerSeriesSubmodule`. -/
theorem mem_twoSidedRestrictedSubmodule_iff_finite_notMem {f : ℤ → M} :
    f ∈ twoSidedRestrictedSubmodule A M ↔
      ∀ W : OpenAddSubgroup M, {n | f n ∉ (W : Set M)}.Finite := by
  rw [mem_twoSidedRestrictedSubmodule]
  exact NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem

end WedhornCriterion

section DegreeSplit

variable (A M : Type*) [Semiring A] [AddCommMonoid M] [TopologicalSpace M] [Module A M]

variable {A M}

omit [TopologicalSpace M] in
/-- **Disjoint sets of indices give disjoint submodules of families vanishing outside them.**
A family vanishing outside `s` and outside `t` at once, for `s` and `t` disjoint, vanishes
everywhere. The submodules are Mathlib's `Submodule.pi` at the zero submodule. -/
theorem disjoint_pi_bot_of_disjoint_compl {ι : Type*} {s t : Set ι} (h : Disjoint s t) :
    Disjoint (Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule A M))
      (Submodule.pi tᶜ fun _ ↦ (⊥ : Submodule A M)) :=
  Submodule.disjoint_def.mpr fun f hs ht ↦ funext fun i ↦ by
    by_cases hi : i ∈ s
    · exact ht i (Set.disjoint_left.mp h hi)
    · exact hs i hi

variable (A M) [ContinuousAdd M] [ContinuousConstSMul A M]

/-- **Wedhorn's degree decomposition, Lemma 8.33(i).** A two-sided restricted family is the sum of
its non-negative part and its negative part: `A⟨z, z⁻¹⟩ = A⟨z⟩ + z⁻¹A⟨z⁻¹⟩` at the level of
coefficients. Each summand is again restricted by `zeroAtFilter_of_forall_eq_or_eq_zero`. -/
theorem twoSidedRestrictedSubmodule_eq_sup :
    twoSidedRestrictedSubmodule A M =
      (twoSidedRestrictedSubmodule A M ⊓
          Submodule.pi {n : ℤ | 0 ≤ n}ᶜ fun _ ↦ (⊥ : Submodule A M)) ⊔
        (twoSidedRestrictedSubmodule A M ⊓
          Submodule.pi {n : ℤ | n < 0}ᶜ fun _ ↦ (⊥ : Submodule A M)) := by
  refine le_antisymm (fun f hf ↦ ?_) (sup_le inf_le_left inf_le_left)
  have hcompl : {n : ℤ | n < 0} = {n : ℤ | 0 ≤ n}ᶜ := by ext n; simp [not_le]
  refine Submodule.mem_sup.mpr
    ⟨{n : ℤ | 0 ≤ n}.indicator f, ⟨?_, ?_⟩, {n : ℤ | n < 0}.indicator f, ⟨?_, ?_⟩, ?_⟩
  · exact hf.of_forall_eq_or_eq_zero fun n ↦ by
      by_cases h : n ∈ {n : ℤ | 0 ≤ n} <;> simp [h]
  · intro n hn; simpa [Set.indicator_apply] using fun h ↦ absurd h (by simpa using hn)
  · exact hf.of_forall_eq_or_eq_zero fun n ↦ by
      by_cases h : n ∈ {n : ℤ | n < 0} <;> simp [h]
  · intro n hn; simpa [Set.indicator_apply] using fun h ↦ absurd h (by simpa using hn)
  · rw [hcompl]; exact Set.indicator_self_add_compl _ f

/-- **The decomposition is direct.** A family supported in non-negative degrees and in negative
degrees at once is zero, so the two summands of `twoSidedRestrictedSubmodule_eq_sup` meet in `⊥`.
Together they exhibit `A⟨z, z⁻¹⟩` as the internal direct sum of the two half-line pieces. -/
theorem disjoint_twoSidedRestricted_nonneg_neg :
    Disjoint
      (twoSidedRestrictedSubmodule A M ⊓
        Submodule.pi {n : ℤ | 0 ≤ n}ᶜ fun _ ↦ (⊥ : Submodule A M))
      (twoSidedRestrictedSubmodule A M ⊓
        Submodule.pi {n : ℤ | n < 0}ᶜ fun _ ↦ (⊥ : Submodule A M)) :=
  by
  have hst : Disjoint {n : ℤ | 0 ≤ n} {n : ℤ | n < 0} := by
    rw [Set.disjoint_left]
    intro n hn hn'
    exact lt_irrefl n (lt_of_lt_of_le hn' hn)
  exact (disjoint_pi_bot_of_disjoint_compl (A := A) (M := M) hst).mono inf_le_right inf_le_right

end DegreeSplit

end TauCeti.Huber
