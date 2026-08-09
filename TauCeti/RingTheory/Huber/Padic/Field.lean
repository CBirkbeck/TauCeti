/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import TauCeti.RingTheory.Huber.Padic.Basic

/-!
# The p-adic numbers are a Tate ring

`ℚ_[p]` is a Tate ring, with `(ℤ_[p], (p))` as a pair of definition and `p` as a
pseudouniformiser. Together with `TauCeti.Huber.PadicInt.not_isTateRing` this is the roadmap's
Layer-0 example separating the two notions: the same ideal of definition makes `ℤ_[p]` Huber but
not Tate, and `ℚ_[p]` Tate, the difference being that `p` becomes a unit in `ℚ_[p]`.

No transport is needed here, unlike for `ℤ_[p]`: Mathlib defines `ℤ_[p]` as the subring
`{x : ℚ_[p] | ‖x‖ ≤ 1}`, so `Ideal ℤ_[p]` is already the type
`TauCeti.Huber.PairOfDefinition` asks for.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.padic`: the pair of definition `(ℤ_[p], (p))` of `ℚ_[p]`.

## Main results

* `TauCeti.Huber.Padic.isPseudoUniformizer_p`: `p` is a pseudouniformiser of `ℚ_[p]`.
* `TauCeti.Huber.Padic.isHuberRing` and `TauCeti.Huber.Padic.isTateRing`: `ℚ_[p]` is a Huber
  ring, and a Tate ring.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §6, where Huber and Tate rings are introduced
  (Proposition and Definition 6.1) and `ℚ_[p]` is the standard example of a Tate ring.
-/

public section

open Topology IsLocalRing

namespace TauCeti.Huber

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/-- The unit ball `ℤ_[p]` is open in `ℚ_[p]`. This is Mathlib's
`PadicInt.isOpenEmbedding_coe` read through `Subtype.range_coe`. -/
private theorem isOpen_padicIntSubring :
    IsOpen ((_root_.PadicInt.subring p : Subring ℚ_[p]) : Set ℚ_[p]) := by
  have h := (_root_.PadicInt.isOpenEmbedding_coe (p := p)).isOpen_range
  rwa [Subtype.range_coe_subtype] at h

/-- `p` is a pseudouniformiser of `ℚ_[p]`: it is a unit, and its powers have norm `p⁻ⁿ → 0`. -/
theorem isPseudoUniformizer_p : IsPseudoUniformizer (p : ℚ_[p]) := by
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ <| mod_cast (Fact.out : p.Prime).one_lt
  -- `IsTopologicallyNilpotent` is by definition this convergence, so `exact` accepts it
  have hnil : Filter.Tendsto (fun n : ℕ ↦ (p : ℚ_[p]) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by rw [_root_.Padic.norm_p]; exact hlt)
  exact isPseudoUniformizer_iff.mpr
    ⟨Ne.isUnit (by exact_mod_cast (Fact.out : p.Prime).ne_zero), hnil⟩

/-- The pair of definition `(ℤ_[p], (p))` exhibiting `ℚ_[p]` as a Huber ring. -/
noncomputable def _root_.TauCeti.Huber.PairOfDefinition.padic :
    PairOfDefinition ℚ_[p] where
  ringOfDefinition := _root_.PadicInt.subring p
  isOpen_ringOfDefinition := isOpen_padicIntSubring
  idealOfDefinition := maximalIdeal ℤ_[p]
  fg_idealOfDefinition := by
    rw [_root_.PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _
  isAdic_idealOfDefinition := PadicInt.isAdic_maximalIdeal

/-- The ring of definition of `PairOfDefinition.padic` is `ℤ_[p]`.

There is no companion equation for `idealOfDefinition`: its type is `Ideal ↥ringOfDefinition`, so
an equation with `maximalIdeal ℤ_[p]` only typechecks once `ringOfDefinition` has been rewritten,
which the opaque body does not permit. Rewrite with this lemma first. -/
@[simp]
theorem _root_.TauCeti.Huber.PairOfDefinition.padic_ringOfDefinition :
    (PairOfDefinition.padic (p := p)).ringOfDefinition = _root_.PadicInt.subring p := (rfl)

/-- **The ideal of definition of `PairOfDefinition.padic` is `(p)`**, in membership form.

`idealOfDefinition` has type `Ideal ↥ringOfDefinition`, so an equation with `maximalIdeal ℤ_[p]`
does not typecheck while the body is opaque. Saying which elements belong avoids the dependent
type altogether, and unlike a statement transported along an equivalence it determines the ideal
for a downstream user: `‖x‖ < 1` is checkable. -/
@[simp]
theorem _root_.TauCeti.Huber.PairOfDefinition.mem_padic_idealOfDefinition
    {x : (PairOfDefinition.padic (p := p)).ringOfDefinition} :
    x ∈ (PairOfDefinition.padic (p := p)).idealOfDefinition ↔ ‖(x : ℚ_[p])‖ < 1 := by
  simp only [PairOfDefinition.padic]
  exact _root_.PadicInt.mem_nonunits

/-- **`ℚ_[p]` is a Huber ring**, with `(ℤ_[p], (p))` as a pair of definition. -/
instance isHuberRing : IsHuberRing ℚ_[p] :=
  ⟨⟨PairOfDefinition.padic⟩⟩

/-- **`ℚ_[p]` is a Tate ring**, with `p` as a pseudouniformiser. -/
instance isTateRing : IsTateRing ℚ_[p] :=
  ⟨⟨(p : ℚ_[p]), isPseudoUniformizer_p⟩⟩

end Padic

end TauCeti.Huber
