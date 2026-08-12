/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.ContinuousValuation
public import TauCeti.RingTheory.Valuation.CharacteristicGroup
public import TauCeti.RingTheory.Valuation.SpanPow

/-!
# Cofinal values on a generating set make a valuation continuous

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), the engine of Theorem 7.10's `⊇` direction.**

A valuation on a Huber ring is continuous as soon as it is bounded by `1` on an ideal of
definition `I` and has cofinal values on a finite generating set of `I`. That is exactly what the
right-hand side of Theorem 7.10 supplies: membership in `Spv (A, IA)` gives the cofinality, by
Wedhorn Lemma 7.4, and `v a < 1` on `I` gives the bound.

## How the two hypotheses combine

Continuity is tested against the basic neighbourhoods `Iⁿ` of zero
(`TauCeti.Huber.PairOfDefinition.isContinuous_iff_forall_exists_idealImage_subset`), so given `b`
with `v b ≠ 0` the task is to find one `n` with `v < v b` on the image of `Iⁿ`.

Take `δ` to be the largest value of `v` on the generating set — attained, because the set is
finite, and this is the only place finiteness is used. Cofinality at that one maximising generator
produces an `n` with `δ ⁿ < v b`. The valuation bound on a power of a spanned ideal
(`Valuation.map_le_pow_of_mem_span_pow_succ`) then gives `v ≤ δ ⁿ` on `Iⁿ⁺¹`, and the two
inequalities compose.

Only the maximising generator needs cofinality for the argument to run; it is asked of all of them
because that is the hypothesis Lemma 7.4 hands over, and asking less would not simplify any call
site.

## Why the bound is taken over `A₀`

The valuation bound is applied through `v.comap P.ringOfDefinition.subtype`, over the ring of
definition rather than over `A`. That is forced rather than cosmetic. An element of `Iⁿ⁺¹` is a
sum of terms `c * t₀ * ⋯ * tₙ` whose coefficient `c` ranges over `A₀`, so the coefficient can be
absorbed into a generator — `c * t₀` lies in `I`, where `v ≤ 1` is available. Over the extension
`I · A` the coefficients range over all of `A` instead, and `v ≤ 1` on `I · A` does not follow
from these hypotheses.

## Main results

* `TauCeti.Huber.PairOfDefinition.isContinuous_of_forall_cofinalValue` : the criterion above.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Theorem 7.10 and Lemma 7.4.
-/

public section

namespace TauCeti.Huber.PairOfDefinition

open TauCeti TauCeti.Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Cofinal values on a generating set make a valuation continuous.** If `v ≤ 1` on an ideal of
definition `I` and `v` has cofinal values at every member of a finite generating set of `I`, then
`v` is continuous.

This is the engine of Wedhorn Theorem 7.10's `⊇` direction: membership in `Spv (A, IA)` supplies
the cofinality through Lemma 7.4, and `v a < 1` on `I` supplies the bound. -/
theorem isContinuous_of_forall_cofinalValue (P : PairOfDefinition A) (v : Valuation A Γ₀)
    {s : Finset P.ringOfDefinition} (hne : s.Nonempty)
    (hgen : Ideal.span (s : Set P.ringOfDefinition) = P.idealOfDefinition)
    (h1 : ∀ a ∈ P.idealOfDefinition, v ((a : P.ringOfDefinition) : A) ≤ 1)
    (hcof : ∀ t ∈ s, CofinalValue v ((t : P.ringOfDefinition) : A)) :
    v.IsContinuous := by
  rw [isContinuous_iff_forall_exists_idealImage_subset P]
  intro b hb
  -- `δ` is the largest value of `v` on the generators, attained at `t₀` because `s` is finite.
  obtain ⟨t₀, ht₀s, ht₀max⟩ := s.exists_max_image (fun t ↦ v ((t : P.ringOfDefinition) : A)) hne
  -- Cofinality at `t₀` alone produces the exponent.
  obtain ⟨n, hn⟩ :=
    cofinalValue_iff.mp (hcof t₀ ht₀s) (v.restrict b) (by simpa using zero_lt_iff.mpr hb)
  have hlt : v ((t₀ : P.ringOfDefinition) : A) ^ n < v b := by
    have hemb := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono hn
    simpa only [map_pow, _root_.Valuation.embedding_restrict] using hemb
  refine ⟨n + 1, fun x hx ↦ ?_⟩
  -- The bound on `Iⁿ⁺¹`, taken over `A₀` so that the coefficients stay inside `I`.
  obtain ⟨y, hy, rfl⟩ := (P.mem_idealImage (n + 1)).mp hx
  set w := v.comap P.ringOfDefinition.subtype with hw
  have hsw : ∀ t ∈ (s : Set P.ringOfDefinition), w t ≤ v ((t₀ : P.ringOfDefinition) : A) := by
    intro t ht
    simpa only [hw, _root_.Valuation.comap_apply, Subring.coe_subtype] using
      ht₀max t (Finset.mem_coe.mp ht)
  have h1w : ∀ a ∈ Ideal.span (s : Set P.ringOfDefinition), w a ≤ 1 := by
    rw [hgen]
    simpa only [hw, _root_.Valuation.comap_apply, Subring.coe_subtype] using h1
  have hbound : w y ≤ v ((t₀ : P.ringOfDefinition) : A) ^ n :=
    _root_.Valuation.map_le_pow_of_mem_span_pow_succ w hsw h1w (by rwa [hgen])
  exact lt_of_le_of_lt
    (by simpa only [hw, _root_.Valuation.comap_apply, Subring.coe_subtype] using hbound) hlt

end TauCeti.Huber.PairOfDefinition

end
