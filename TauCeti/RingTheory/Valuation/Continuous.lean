/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.WithZeroTopology

/-!
# Continuous valuations

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.7 and Remark 7.8.**

A valuation `v` on a topological ring `A` is *continuous* if `{a ; v a < γ}` is open in `A` for
every `γ` in the value group `Γ_v` of `v` — equivalently, if the topology of `A` is finer than
the one `v` defines.

Wedhorn works over a topological ring throughout, but the compatibility is only needed where it
is used, so it is asked for per result rather than up front: the definition itself needs no more
than a topology on `A`, `isOpen_lt_div` needs `[ContinuousMul A]`, the two translation results
need `[ContinuousSub A]`, and only `isContinuous_iff_continuous` needs both, as
`[IsTopologicalRing A]`. Commutativity is never used, so `A` is a `Ring`.

## The quantifier ranges over the value group, not over the codomain

Wedhorn quantifies `γ` over `Γ_v`, and that is load-bearing rather than incidental. Asking
instead for `{a ; v a < γ}` to be open for every `γ` in the ambient codomain `Γ₀` is **strictly
stronger** whenever `Γ₀` is larger than `Γ_v ∪ {0}`, and — crucially — it is then **not an
invariant of the equivalence class** of `v`, so it cannot cut out a subset of `Spv A`.

A witness: take `A = ℤ_p`, and let `w : A → (ℝ_{>0} ×ₗ p^ℤ) ∪ {0}` send `a ≠ 0` to `(1, |a|_p)`,
the order being lexicographic with the first coordinate dominant. Then `w` is equivalent to the
`p`-adic valuation, but for `γ = (1/2, 1)` — nonzero, yet below every value `w` attains — the set
`{a ; w a < γ}` is `{0}`, which is not open. The `p`-adic valuation into its own value group has
no such `γ` available.

So `IsContinuous` is stated by quantifying over the **values** `v b`, which is the same thing:
every element of `Γ_v` is a ratio `v b / v c`, and `IsContinuous.isOpen_lt_div` recovers those.
Phrased that way the defining sets are *literally equal* for equivalent valuations, which is
`Valuation.IsEquiv.isContinuous_iff`.

## Main definitions

* `TauCeti.Valuation.IsContinuous` : **Definition 7.7**, continuity of a valuation on a
  topological ring.

## Main results

* `Valuation.IsEquiv.isContinuous_iff` : continuity depends only on the equivalence class, so it
  descends to the valuation spectrum.
* `TauCeti.Valuation.IsContinuous.isOpen_lt_div` : the defining sets for an arbitrary element
  `v b / v c` of the value group, which is Wedhorn's quantifier in full.
* `TauCeti.Valuation.isContinuous_iff_continuous` : **Remark 7.8(1)**, that on a codomain no
  larger than `Γ_v ∪ {0}` continuity is ordinary continuity into `WithZeroTopology`.
* `TauCeti.Valuation.IsContinuous.isOpen_le` : **Remark 7.8(3)**, the non-strict form.
* `TauCeti.Valuation.isContinuous_of_discreteTopology` : **Remark 7.8(2)**, every valuation on
  a discrete ring is continuous.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.7 and Remark 7.8.
-/

public section

namespace TauCeti.Valuation

open Set Topology TauCeti

variable {A : Type*} [Ring A] [TopologicalSpace A]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀']

/-- **Wedhorn Definition 7.7.** A valuation on a topological ring is *continuous* if every set
`{a ; v a < γ}` with `γ` in the value group of `v` is open, i.e. if the topology of `A` is finer
than the topology `v` defines.

The quantifier is over the **attained values** `v b` rather than over the codomain `Γ₀`; those
generate the value group, and `isOpen_lt_div` reaches the rest of it. See the module docstring
for why quantifying over `Γ₀` would be a different — and equivalence-class-dependent —
condition. The values `b` with `v b = 0` cost nothing here, the set then being empty. -/
def IsContinuous (v : Valuation A Γ₀) : Prop :=
  ∀ b : A, IsOpen {a : A | v a < v b}

/-- Continuity may equivalently be tested only at the `b` outside the support, which is
Wedhorn's `γ ∈ Γ_v`: a `b` in the support contributes the empty set. -/
theorem isContinuous_iff_forall_ne_zero (v : Valuation A Γ₀) :
    v.IsContinuous ↔ ∀ b : A, v b ≠ 0 → IsOpen {a : A | v a < v b} :=
  ⟨fun h b _ ↦ h b, fun h b ↦ (eq_or_ne (v b) 0).elim (fun hb ↦ by simp [hb]) (h b)⟩

/-- Openness of `{a ; v a < γ}` for every `γ` of the codomain is a sufficient — in general
strictly stronger — condition for continuity. -/
theorem isContinuous_of_forall {v : Valuation A Γ₀} (h : ∀ γ : Γ₀, IsOpen {a : A | v a < γ}) :
    v.IsContinuous := fun b ↦ h (v b)

/-- **Continuity is an invariant of the equivalence class.** Equivalent valuations compare the
same pairs of elements, so the sets `{a ; v a < v b}` cutting out continuity are not merely
matched up but literally the same sets. This is what lets continuity be imposed on a point of
the valuation spectrum. -/
theorem _root_.Valuation.IsEquiv.isContinuous_iff {v : Valuation A Γ₀} {w : Valuation A Γ₀'}
    (h : v.IsEquiv w) : v.IsContinuous ↔ w.IsContinuous :=
  forall_congr' fun _ ↦ iff_of_eq (congrArg IsOpen (Set.ext fun _ ↦ h.lt_iff_lt))

/-- **Wedhorn Remark 7.8(2).** Every valuation on a discrete topological ring is continuous. -/
theorem isContinuous_of_discreteTopology [DiscreteTopology A] (v : Valuation A Γ₀) :
    v.IsContinuous := fun _ ↦ isOpen_discrete _

/-- **Wedhorn's quantifier in full.** Every element of the value group `Γ_v` is a ratio
`v b / v c` with `c` outside the support, and continuity makes `{a ; v a < v b / v c}` open for
all of them. -/
theorem IsContinuous.isOpen_lt_div [ContinuousMul A] {v : Valuation A Γ₀} (hv : v.IsContinuous)
    (b : A) {c : A} (hc : v c ≠ 0) : IsOpen {a : A | v a < v b / v c} := by
  -- the set is the preimage of `{x ; v x < v b}` under multiplication by `c`
  simpa [lt_div_iff₀ (zero_lt_iff.mpr hc)] using (hv b).preimage (continuous_mul_const c)

/-- **The translated ball is a neighbourhood.** For `γ` in the value group, `{y ; v (y - a) < γ}`
is an open neighbourhood of `a`, being the preimage of the open `{x ; v x < γ}` under
translation. It is the workhorse of the two results below: on it, `v y` is controlled by `v a`
through the strict triangle inequality. -/
private theorem IsContinuous.sub_lt_mem_nhds [ContinuousSub A] {v : Valuation A Γ₀}
    (hv : v.IsContinuous) (a : A) {b : A} (hb : v b ≠ 0) : {y : A | v (y - a) < v b} ∈ 𝓝 a := by
  refine ((hv b).preimage (continuous_id.sub continuous_const)).mem_nhds ?_
  simpa using zero_lt_iff.mpr hb

/-- **Wedhorn Remark 7.8(3).** For `γ` in the value group, the non-strict set `{a ; v a ≤ γ}` is
open as well: it is a union of translates of the open `{a ; v a < γ}`, since adding an element
of value `< γ` to one of value `≤ γ` keeps the value `≤ γ`. -/
theorem IsContinuous.isOpen_le [ContinuousSub A] {v : Valuation A Γ₀} (hv : v.IsContinuous) {b : A}
    (hb : v b ≠ 0) : IsOpen {a : A | v a ≤ v b} := by
  refine isOpen_iff_mem_nhds.mpr fun a ha ↦ ?_
  filter_upwards [hv.sub_lt_mem_nhds a hb] with y hy
  simpa using v.map_add_le hy.le ha

open scoped WithZeroTopology in
/-- **Wedhorn Remark 7.8(1).** When the codomain is no larger than `Γ_v ∪ {0}` — the hypothesis
`hΓ`, which says every nonzero `γ` is a ratio of values — continuity in the sense of Definition
7.7 is ordinary continuity of `v : A → Γ₀` for the topology of Wedhorn's Remark 1.17, namely
Mathlib's `WithZeroTopology`.

Without `hΓ` only the reverse implication survives, and the module docstring gives a valuation
for which the forward one fails. -/
theorem isContinuous_iff_continuous [IsTopologicalRing A] {v : Valuation A Γ₀}
    (hΓ : ∀ γ : Γ₀, γ ≠ 0 → ∃ b c : A, v c ≠ 0 ∧ v b = γ * v c) :
    v.IsContinuous ↔ Continuous v := by
  refine ⟨fun hv ↦ continuous_iff_continuousAt.mpr fun a ↦ ?_, fun hv ↦ isContinuous_of_forall
    fun γ ↦ hv.isOpen_preimage _ WithZeroTopology.isOpen_Iio⟩
  rcases eq_or_ne (v a) 0 with ha | ha
  · -- at a point of the support, the sets of Definition 7.7 are themselves the basic
    -- neighbourhoods of `0`, once `hΓ` has written `γ` as a ratio of values
    rw [ContinuousAt, ha, WithZeroTopology.tendsto_zero]
    intro γ hγ
    obtain ⟨b, c, hc, hbc⟩ := hΓ γ hγ
    rw [← mul_div_cancel_right₀ γ hc, ← hbc]
    exact (hv.isOpen_lt_div b hc).mem_nhds (by simpa [ha, hbc, hc] using zero_lt_iff.mpr hγ)
  · -- off the support `v` is locally constant, by the strict triangle equality
    rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero ha]
    filter_upwards [hv.sub_lt_mem_nhds a ha] with y hy using v.map_eq_of_sub_lt hy

end TauCeti.Valuation
