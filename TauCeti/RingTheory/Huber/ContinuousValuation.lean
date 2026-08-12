/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Valuation.Continuous
import TauCeti.RingTheory.Valuation.SpanPow

/-!
# Continuity of a valuation on a Huber ring

On a Huber ring the neighbourhood filter of `0` has a concrete basis — the images of the powers
`Iⁿ` of an ideal of definition (`TauCeti.Huber.PairOfDefinition.hasBasis_nhds_zero`). Continuity
of a valuation, which is openness of the sets `{a ; v a < v b}`, can therefore be tested against
that basis instead of against the topology: **`v` is continuous exactly when each of those sets
swallows some `Iⁿ`.**

That replaces a quantifier over open sets by one over a single natural number, and it is the
form Wedhorn's §7.2 arguments actually use — his proof of Theorem 7.10 produces continuity by
exhibiting, for a given `γ`, an `n` with `v < γ` on `Iⁿ⁺¹`.

## The codomain is a monoid, so `Valuation.ltAddSubgroup` is unavailable

Mathlib's `Valuation.ltAddSubgroup` packages a sublevel set as an additive subgroup, but it is
indexed by `Γ₀ˣ` and so forces a `LinearOrderedCommGroupWithZero` codomain. `IsContinuous` is
stated over a `LinearOrderedCommMonoidWithZero`, matching Mathlib's `Valuation`, and this
criterion is stated over one too — the strict triangle inequality needs no inverses. The
subgroup is therefore built where it is used rather than taken from Mathlib.

## Main results

* `TauCeti.Huber.PairOfDefinition.isContinuous_iff_forall_exists_idealImage_subset` : the
  criterion, in both directions.
* `TauCeti.Huber.PairOfDefinition.map_le_pow_of_mem_idealImage_succ` : the bound on `v` over a
  basic neighbourhood of zero that the criterion is fed with.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition and Definition 6.1, and §7.2.
* AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, `projects/AdicSpaces/Adic spaces/SpvAITopology.lean`,
  was consulted. It names `pow_image_isOpen` and `isContinuous_of_ideal_pow_lt` as consumers of
  exactly this criterion, which is what fixed its downstream-facing shape, but does not state the
  criterion itself and leaves the surrounding Wedhorn 7.10 sub-leaves incomplete.
-/

public section

namespace TauCeti.Huber.PairOfDefinition

open Set Topology TauCeti

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **Continuity, tested against the ideal-of-definition basis.** A valuation on a Huber ring is
continuous exactly when every set `{a ; v a < v b}` contains the image of some power `Iⁿ` of an
ideal of definition.

The `b` with `v b = 0` are excluded because `{a ; v a < 0}` is empty, hence not a subgroup;
`Valuation.isContinuous_iff_forall_ne_zero` shows they cost nothing. -/
theorem isContinuous_iff_forall_exists_idealImage_subset (P : PairOfDefinition A)
    (v : Valuation A Γ₀) :
    v.IsContinuous ↔
      ∀ b : A, v b ≠ 0 → ∃ n : ℕ, (P.idealImage n : Set A) ⊆ {a : A | v a < v b} := by
  rw [Valuation.isContinuous_iff_forall_ne_zero]
  refine ⟨fun h b hb ↦ ?_, fun h b hb ↦ ?_⟩
  · obtain ⟨n, -, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp
      ((h b hb).mem_nhds (by simpa using zero_lt_iff.mpr hb))
    exact ⟨n, hn⟩
  · obtain ⟨n, hn⟩ := h b hb
    -- the sublevel set is an additive subgroup, by the strict triangle inequality
    let S : AddSubgroup A :=
      { carrier := {a : A | v a < v b}
        add_mem' := fun ha hb' ↦ lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb')
        zero_mem' := by simpa using zero_lt_iff.mpr hb
        neg_mem' := fun {x} hx ↦ by simpa [Set.mem_ofPred_eq, v.map_neg] using hx }
    exact AddSubgroup.isOpen_mono (H₁ := P.idealImage n) (H₂ := S) hn (P.isOpen_idealImage n)

omit [IsTopologicalRing A] in
/-- **A valuation on a basic neighbourhood of zero.** If `v ≤ δ` on a generating set of the ideal
of definition and `v ≤ 1` on the ideal itself, then `v ≤ δ ^ n` on the image of `Iⁿ⁺¹`.

This is `Valuation.map_le_pow_of_mem_span_pow_succ` transported to the Huber setting, and it is
the input `isContinuous_iff_forall_exists_idealImage_subset` consumes in Wedhorn's proof of
Theorem 7.10: cofinality supplies an `n` with `δ ^ n` below a given `γ`, and this turns that into
`v < γ` on a basic neighbourhood, which is continuity.

The bound is taken **over the ring of definition**, through `v.comap`. That is not a convenience:
the coefficients occurring in `Iⁿ⁺¹` range over `A₀`, so the hypothesis needed is `v ≤ 1` on `I`,
which Theorem 7.10 supplies. The same bound over the extension `I · A` is not available in
general: `I · A` contains `r * x` for arbitrary `r ∈ A`, so an unbounded `v` violates it. (It is
not *always* violated — the trivial valuation satisfies it — but it does not follow from the
hypotheses here, which is what matters.) -/
theorem map_le_pow_of_mem_idealImage_succ (P : PairOfDefinition A) (v : Valuation A Γ₀)
    {s : Set P.ringOfDefinition} {δ : Γ₀} (hgen : Ideal.span s = P.idealOfDefinition)
    (hs : ∀ t ∈ s, v (t : A) ≤ δ)
    (h1 : ∀ a ∈ P.idealOfDefinition, v ((a : P.ringOfDefinition) : A) ≤ 1)
    {n : ℕ} {x : A} (hx : x ∈ P.idealImage (n + 1)) : v x ≤ δ ^ n := by
  obtain ⟨y, hy, rfl⟩ := (P.mem_idealImage (n + 1)).mp hx
  set w := v.comap P.ringOfDefinition.subtype with hw
  have hsw : ∀ t ∈ s, w t ≤ δ := by
    simpa only [hw, Valuation.comap_apply, Subring.coe_subtype] using hs
  have h1w : ∀ a ∈ Ideal.span s, w a ≤ 1 := by
    rw [hgen]; simpa only [hw, Valuation.comap_apply, Subring.coe_subtype] using h1
  simpa only [hw, Valuation.comap_apply, Subring.coe_subtype] using
    Valuation.map_le_pow_of_mem_span_pow_succ w hsw h1w (by rwa [hgen])

end TauCeti.Huber.PairOfDefinition
