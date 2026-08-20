/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Topology.Basic

/-!
# Lifting a convergent family along a surjection

A family `g : ι → N` converges to `n₀` along the cofinite filter when all but finitely many of its
members lie in any given neighbourhood of `n₀`. This file shows that a surjection which carries a
neighbourhood basis of `m₀` onto neighbourhoods of `n₀` lifts such a family to one converging to
`m₀`: the lift can be chosen convergent, not merely made to exist.

**Openness is not the hypothesis, and would not suffice on its own.** `IsOpenMap φ` makes `φ '' V n`
open around `φ m₀`, which is a neighbourhood of `n₀` only when `φ m₀ = n₀`. The application is
therefore a *zero-preserving* open surjection — an `A`-linear map, say — and that is the form
`TauCeti.Huber` uses it in.

That the lifts exist pointwise is only surjectivity. The content is that they can be chosen
*uniformly enough to still converge*, and this genuinely needs a construction: choosing a preimage
of `g α` for each `α` independently can leave the lifts spread out even when the `g α` collapse to
zero. The fix is to choose the preimage of `g α` from a neighbourhood whose index grows with `α`,
so that convergence is forced by the choice rather than hoped for.

## Main results

* `exists_lift_tendsto_cofinite_nhds`: the lifting statement.

## Implementation notes

The index of the neighbourhood a lift is drawn from is
`Nat.findGreatest (fun m ↦ g α ∈ φ '' V m) (r α)`, where `r` is an injection of `ι` into `ℕ` —
one exists because `ι` is countable, and it tends to infinity cofinitely because `cofinite` is
`atTop` on `ℕ`. **The cap by `r α` is what makes the definition total.** Without it the natural
index is the largest `m` with `g α ∈ φ '' V m`, which is undefined exactly when `g α` lies in
every `φ '' V m`; capping removes that case rather than splitting on it.

No algebraic structure is used: `M` and `N` carry only a topology and a distinguished point. In
particular the neighbourhoods `V n` are not assumed to be subgroups, which the argument would need
if it ever added two lifts — it never does, choosing each independently.

The hypothesis is `∀ n, φ '' V n ∈ 𝓝 n₀` rather than `IsOpenMap φ`, since that is exactly what the
proof consumes; an open `φ` with `φ m₀ = n₀` is one way to supply it, and a `Filter.map` equality is
another. Nothing about `m₀` and `n₀` is used beyond their neighbourhood filters — no zero, and no
algebra.
-/

namespace TauCeti

open Filter Topology Set

public section

variable {ι : Type*} [Countable ι] {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

omit [Countable ι] [TopologicalSpace M] [TopologicalSpace N] in
/-- Preimages chosen inside a prescribed neighbourhood **whenever one is available there**, and
arbitrary otherwise. Surjectivity gives a preimage in every case; the second component is the part
that matters, and it is vacuous exactly on the finitely many indices the main proof discards. -/
private theorem exists_choice_mem (φ : M → N) (hsurj : Function.Surjective φ) (V : ℕ → Set M)
    (g : ι → N) (n : ι → ℕ) :
    ∃ f : ι → M, ∀ α, φ (f α) = g α ∧ (g α ∈ φ '' V (n α) → f α ∈ V (n α)) := by
  classical
  have pick : ∀ α, ∃ x : M, φ x = g α ∧ (g α ∈ φ '' V (n α) → x ∈ V (n α)) := by
    intro α
    by_cases h : g α ∈ φ '' V (n α)
    · obtain ⟨x, hxV, hxg⟩ := h
      exact ⟨x, hxg, fun _ ↦ hxV⟩
    · obtain ⟨x, hx⟩ := hsurj (g α)
      exact ⟨x, hx, fun hc ↦ absurd hc h⟩
  choose f hf1 hf2 using pick
  exact ⟨f, fun α ↦ ⟨hf1 α, hf2 α⟩⟩

/-- **A convergent family lifts to a convergent family.** If `φ` is surjective and carries each
member of an antitone neighbourhood basis `V` of `m₀` onto a neighbourhood of `n₀`, then any family
tending to `n₀` cofinitely has a `φ`-preimage family tending to `m₀` cofinitely.

Pointwise lifting is surjectivity alone; the statement is that a *single* choice of lifts can be
made to converge. Note that `IsOpenMap φ` supplies the neighbourhood hypothesis only together with
`φ m₀ = n₀`; openness by itself places the images around `φ m₀`, not around `n₀`. -/
theorem exists_lift_tendsto_cofinite_nhds {m₀ : M} {n₀ : N}
    (φ : M → N) (hsurj : Function.Surjective φ)
    (V : ℕ → Set M) (hV : (𝓝 m₀).HasAntitoneBasis V)
    (hVmem : ∀ n, φ '' V n ∈ 𝓝 n₀)
    (g : ι → N) (hg : Tendsto g (Filter.cofinite : Filter ι) (𝓝 n₀)) :
    ∃ f : ι → M, (∀ α, φ (f α) = g α) ∧ Tendsto f (Filter.cofinite : Filter ι) (𝓝 m₀) := by
  classical
  obtain ⟨r, hr⟩ := exists_injective_nat ι
  replace hr : Tendsto r (Filter.cofinite : Filter ι) atTop :=
    Nat.cofinite_eq_atTop ▸ hr.tendsto_cofinite
  obtain ⟨f, hf⟩ := exists_choice_mem φ hsurj V g
    (fun α ↦ Nat.findGreatest (fun m ↦ g α ∈ φ '' V m) (r α))
  refine ⟨f, fun α ↦ (hf α).1, ?_⟩
  rw [hV.toHasBasis.tendsto_right_iff]
  intro N _
  have hfin : {α | g α ∉ φ '' V N}.Finite := by
    simpa [Filter.eventually_cofinite] using hg.eventually_mem (hVmem N)
  have hfin2 : {α | r α < N}.Finite := by
    simpa [Filter.eventually_cofinite, not_le] using hr.eventually_ge_atTop N
  rw [Filter.eventually_cofinite]
  refine (hfin.union hfin2).subset fun α hα ↦ ?_
  by_cases h1 : g α ∈ φ '' V N
  · by_cases h2 : N ≤ r α
    · exact absurd (hV.antitone (Nat.le_findGreatest (P := fun m ↦ g α ∈ φ '' V m) h2 h1)
        ((hf α).2 (Nat.findGreatest_spec (P := fun m ↦ g α ∈ φ '' V m) h2 h1))) hα
    · exact Or.inr (not_le.mp h2)
  · exact Or.inl h1

end

end TauCeti
