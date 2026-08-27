/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Ideal
public import TauCeti.RingTheory.Huber.RingOfDefinition
public import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# The unit group of a complete Huber ring is open, and maximal ideals are closed

This is the first half of Wedhorn's Proposition 7.51, whose statement is "*then `𝔪` is closed
and there exists `v ∈ Spa A` with `supp v = 𝔪`*". Only the closedness conjunct is proved here;
the existence conjunct needs nonemptiness of the adic spectrum (Wedhorn Proposition 7.49), which
is a separate development.

The argument is Wedhorn's. The topologically nilpotent elements of a Huber ring form an open set
(`TauCeti.Huber.isOpen_setOf_isTopologicallyNilpotent`), and completeness makes `1 + A°°` consist
of units (`IsTopologicallyNilpotent.isUnit_one_add`). Around a unit `u` the set of `x` with
`u⁻¹x - 1` topologically nilpotent is then an open neighbourhood of `u` made of units, so the unit
group is open. Its complement is therefore closed and contains every proper ideal, so the closure
of a maximal ideal is again a proper ideal containing it, hence equal to it by maximality.

## Why this does not assume a linear topology

`TauCeti.Topology.Algebra.Nonarchimedean.MaximalIdeals` proves the *openness* of maximal ideals, and
everything in it carries `[IsLinearTopology A A]` — a basis of neighbourhoods of zero consisting of
ideals. That is not incidental. An open ideal of a Tate ring is the whole ring
(`TauCeti.Huber.IsTateRing.isOpen_iff_eq_top`), so no *proper* ideal of a nonzero Tate ring is open
and the results in that file are adic-only; over `ℚ_p`, `IsTopologicallyNilpotent.mem_of_isMaximal`
would otherwise put `p` in the zero ideal.

Closedness carries no such hypothesis, so it is available for every complete Huber ring, Tate ones
included. Getting there does take a different argument from the linear-topology one — see the
Provenance section — but the resulting statements are hypothesis-free, which is what makes this the
form of Proposition 7.51 that survives the Tate case.

## Main results

* `Ideal.isClosed_of_isMaximal_of_isOpen_isUnit` : over any topological ring, a maximal ideal is
  closed as soon as the unit group is open. This is the general engine and mentions neither
  completeness nor a Huber structure.
* `TauCeti.Huber.isOpen_setOf_isUnit` : the unit group of a complete Huber ring is open.
* `TauCeti.Huber.isClosed_of_isMaximal` : **Wedhorn Proposition 7.51, closedness half** — every
  maximal ideal of a complete Huber ring is closed.

## Provenance

Adapted from AINTLIB (see References), section `MaximalIdealClosed` and section `OpenUnits` of the
source file, which has both statements as `isClosed_of_isMaximal_of_isOpen_units` and
`isOpen_units_of_isOpen_topologicallyNilpotent`. The closedness argument is that file's, essentially
verbatim.

The openness argument is **not**, and the difference is the point of this file. AINTLIB covers a
unit `u` by the additive translate `u + A°°`, which forces it to rewrite `u + a = u * (1 + u⁻¹a)`
and to know that `u⁻¹a` is again topologically nilpotent — that is
`IsTopologicallyNilpotent.mul_left`, which Mathlib states only under `[IsLinearTopology R R]`, so
AINTLIB carries that hypothesis. It is not removable there: in a Tate ring `A°°` is not an ideal,
and `ℚ_p` is a counterexample, with `p` topologically nilpotent but `p⁻² * p = p⁻¹` not. The
hypothesis is load bearing for that route, not an oversight.

The proof here covers `u` by the *multiplicative* neighbourhood `{x : u⁻¹x - 1 ∈ A°°}` instead. That
needs only continuity of `x ↦ u⁻¹x - 1` and the geometric series, never that `A°°` absorbs
multiplication, so it holds with no linear-topology hypothesis at all and therefore applies to Tate
rings. Separately, this repository already has
`TauCeti.Huber.isOpen_setOf_isTopologicallyNilpotent`, so AINTLIB's `A°°`-openness hypothesis is
discharged rather than carried, and the Huber-level statements need no side conditions.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Propositions 5.38, 7.51.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/AdicSpectrum.lean`.
-/

public section

open Topology

/-- **A maximal ideal of a topological ring is closed once the unit group is open.** The closure
of `𝔪` is an ideal containing `𝔪`, and it is proper because it avoids the units — the units are
open, so their complement is a closed set containing `𝔪` and hence its closure. Maximality then
forces the closure to be `𝔪` itself. -/
theorem Ideal.isClosed_of_isMaximal_of_isOpen_isUnit {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (hU : IsOpen {a : A | IsUnit a}) (𝔪 : Ideal A)
    [𝔪.IsMaximal] : IsClosed (𝔪 : Set A) := by
  rw [← closure_eq_iff_isClosed, ← Ideal.coe_closure]
  congr 1
  have hne : 𝔪.closure ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one]
    exact fun h1 ↦ (closure_minimal (fun x hx ↦ mt (Ideal.eq_top_of_isUnit_mem 𝔪 hx)
      (Ideal.IsMaximal.ne_top ‹_›)) hU.isClosed_compl h1) isUnit_one
  exact (Ideal.IsMaximal.eq_of_le ‹_› hne fun x hx ↦ subset_closure hx).symm

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [IsHuberRing A]

/-- **The unit group of a complete Huber ring is open.** Around a unit `u` the set of `x` with
`u⁻¹x - 1` topologically nilpotent is an open neighbourhood of `u` consisting of units: it is open
because `A°°` is and `x ↦ u⁻¹x - 1` is continuous, it contains `u` because `u⁻¹u - 1 = 0`, and each
of its points is a unit because `u⁻¹x = 1 + (u⁻¹x - 1)` is one by the geometric series
(Proposition 5.38) and `x = u * (u⁻¹x)`. -/
theorem isOpen_setOf_isUnit : IsOpen {a : A | IsUnit a} := by
  rw [isOpen_iff_forall_mem_open]
  rintro u hu
  obtain ⟨u, rfl⟩ := (hu : IsUnit u)
  refine ⟨(fun x : A ↦ (↑u⁻¹ : A) * x - 1) ⁻¹' {a : A | IsTopologicallyNilpotent a},
    fun x hx ↦ ?_, ?_, ?_⟩
  · have h1 : IsUnit ((↑u⁻¹ : A) * x) := by
      simpa using (hx : IsTopologicallyNilpotent ((↑u⁻¹ : A) * x - 1)).isUnit_one_add
    simpa [← mul_assoc, u.mul_inv] using u.isUnit.mul h1
  · exact isOpen_setOf_isTopologicallyNilpotent.preimage
      ((continuous_const.mul continuous_id).sub continuous_const)
  · simp only [Set.mem_preimage, Set.mem_ofPred_eq, u.inv_mul, sub_self]
    exact IsTopologicallyNilpotent.zero

/-- **Wedhorn Proposition 7.51, closedness half**: every maximal ideal of a complete Huber ring
is closed. Wedhorn states it for a complete affinoid ring; the affinoid `A⁺` plays no part in the
argument, so the plus subring is absent here. -/
theorem isClosed_of_isMaximal (𝔪 : Ideal A) [𝔪.IsMaximal] : IsClosed (𝔪 : Set A) :=
  Ideal.isClosed_of_isMaximal_of_isOpen_isUnit isOpen_setOf_isUnit 𝔪

end TauCeti.Huber

end
