/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.RingTheory.Huber.Basic

/-!
# The p-adic integers and numbers as Huber rings

`ℤ_[p]` is a Huber ring which is not Tate, and `ℚ_[p]` is a Tate ring. These are the roadmap's
Layer-0 examples after the discrete case, and the first to separate `IsHuberRing` from
`IsTateRing`: `ℤ_[p]` has no topologically nilpotent unit, because its units are exactly the
elements of norm one.

## Main results

* `TauCeti.Huber.IsAdic.comap`: an adic topology transports along a ring equivalence that is
  also an inducing map, which is what puts a ring of definition's ideal where
  `TauCeti.Huber.PairOfDefinition` wants it.
* `TauCeti.Huber.PadicInt.isAdic_maximalIdeal`: the norm topology of `ℤ_[p]` is the `(p)`-adic
  topology.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Example 6.3.
-/

public section

open Topology IsLocalRing

namespace TauCeti.Huber

section Transport

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

omit [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B] in
/-- Finite generation transports along a ring equivalence.

Stated in the abstract so the `Ideal.map_symm` rewrite is elaborated once here rather than against
a concrete subring instance, where unification is expensive. -/
theorem fg_comap_of_equiv (e : B ≃+* A) {I : Ideal A} (h : I.FG) : (I.comap e).FG := by
  classical
  obtain ⟨s, hs⟩ := h
  refine ⟨s.image e.symm, ?_⟩
  rw [← Ideal.map_symm, ← hs, Finset.coe_image, Ideal.map_span]

omit [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B] in
/-- The powers of a comapped ideal are the comapped powers, along a ring equivalence. -/
private theorem comap_pow_of_equiv (e : B ≃+* A) (I : Ideal A) (n : ℕ) :
    (I ^ n).comap e = I.comap e ^ n := by
  rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]

/-- An adic topology transports along a ring equivalence that is also an inducing map.

This is what lets a ring of definition carry an ideal of definition: `PairOfDefinition` asks for
an `Ideal A₀` whose adic topology is the subspace topology, while the ideal at hand usually lives
in a ring that is only equivalent to `A₀`. -/
theorem IsAdic.comap (e : B ≃+* A) (he : IsInducing e) {I : Ideal A} (h : IsAdic I) :
    IsAdic (I.comap e) := by
  rw [isAdic_iff] at h ⊢
  obtain ⟨hopen, hnhds⟩ := h
  have hset : ∀ n : ℕ,
      ((I.comap e ^ n : Ideal B) : Set B) = e ⁻¹' ((I ^ n : Ideal A) : Set A) := by
    intro n
    ext b
    rw [← comap_pow_of_equiv e I n]
    exact Iff.rfl
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · rw [hset n, he.isOpen_iff]
    exact ⟨_, hopen n, rfl⟩
  · rw [he.nhds_eq_comap (0 : B), map_zero, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    obtain ⟨n, hn⟩ := hnhds t ht
    exact ⟨n, by rw [hset n]; exact fun b hb ↦ hts (hn hb)⟩

end Transport

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The `n`-th power of the maximal ideal of `ℤ_[p]` is the closed ball of radius `p⁻ⁿ`: this is
what ties the norm topology to the `(p)`-adic one. -/
theorem coe_maximalIdeal_pow (n : ℕ) :
    ((maximalIdeal ℤ_[p] ^ n : Ideal ℤ_[p]) : Set ℤ_[p])
      = {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ)} := by
  ext x
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
  rw [_root_.PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    ← _root_.PadicInt.norm_le_pow_iff_mem_span_pow]

/-- Every power of the maximal ideal of `ℤ_[p]` is open: the ultrametric inequality carries the
whole ball of radius `p⁻ⁿ` around any of its points back into it. -/
theorem isOpen_maximalIdeal_pow (n : ℕ) :
    IsOpen ((maximalIdeal ℤ_[p] ^ n : Ideal ℤ_[p]) : Set ℤ_[p]) := by
  have hp0 : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
  rw [coe_maximalIdeal_pow, Metric.isOpen_iff]
  intro x hx
  refine ⟨(p : ℝ) ^ (-n : ℤ), zpow_pos hp0 _, fun y hy ↦ ?_⟩
  rw [Set.mem_ofPred_eq, show y = y - x + x by ring]
  refine (_root_.PadicInt.nonarchimedean _ _).trans (max_le (le_of_lt ?_) hx)
  simpa [dist_eq_norm] using hy

/-- **The norm topology of `ℤ_[p]` is the `(p)`-adic topology.** -/
theorem isAdic_maximalIdeal : IsAdic (maximalIdeal ℤ_[p]) := by
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ <| mod_cast (Fact.out : p.Prime).one_lt
  rw [isAdic_iff]
  refine ⟨isOpen_maximalIdeal_pow, fun s hs ↦ ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp1
  refine ⟨n, fun x hx ↦ hball ?_⟩
  rw [coe_maximalIdeal_pow, Set.mem_ofPred_eq] at hx
  refine Metric.mem_ball.mpr (lt_of_le_of_lt ?_ hn)
  simpa [zpow_neg, zpow_natCast, ← inv_pow, dist_eq_norm] using hx

/-- The pair of definition `(ℤ_[p], (p))` exhibiting `ℤ_[p]` as a Huber ring. The ring of
definition is everything, and the ideal of definition is the maximal ideal carried across
`Subring.topEquiv`. -/
noncomputable def pairOfDefinition : PairOfDefinition ℤ_[p] where
  ringOfDefinition := ⊤
  isOpen_ringOfDefinition := by simp
  idealOfDefinition :=
    (maximalIdeal ℤ_[p]).comap (Subring.topEquiv : (⊤ : Subring ℤ_[p]) ≃+* ℤ_[p])
  fg_idealOfDefinition :=
    fg_comap_of_equiv _ (by
      rw [_root_.PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _)
  isAdic_idealOfDefinition :=
    IsAdic.comap _ Topology.IsInducing.subtypeVal isAdic_maximalIdeal

/-- **`ℤ_[p]` is a Huber ring**, with `(ℤ_[p], (p))` as a pair of definition. -/
instance isHuberRing : IsHuberRing ℤ_[p] :=
  ⟨⟨pairOfDefinition⟩⟩

/-- **`ℤ_[p]` is not a Tate ring.** Its units are exactly the elements of norm one, whose powers
all have norm one, so no unit is topologically nilpotent and there is no pseudouniformiser. -/
theorem not_isTateRing : ¬ IsTateRing ℤ_[p] := by
  intro h
  obtain ⟨a, ha⟩ := h.exists_isPseudoUniformizer
  have hone : ∀ n : ℕ, ‖a ^ n‖ = 1 := fun n ↦ by
    rw [norm_pow, _root_.PadicInt.isUnit_iff.mp ha.isUnit, one_pow]
  have hnorm : Filter.Tendsto (fun n : ℕ ↦ ‖a ^ n‖) Filter.atTop (nhds ‖(0 : ℤ_[p])‖) :=
    (continuous_norm.tendsto _).comp ha.isTopologicallyNilpotent
  rw [norm_zero, Filter.tendsto_congr hone] at hnorm
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hnorm)

end PadicInt

end TauCeti.Huber
