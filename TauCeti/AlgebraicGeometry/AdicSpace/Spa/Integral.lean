/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.RingTheory.Huber.ContinuousValuativeCriterion
public import TauCeti.RingTheory.Huber.Pair

/-!
# The ring of integral elements is cut out by the points of the adic spectrum

Wedhorn's Proposition 7.52(1): for a Huber pair `(A, A⁺)`, an element `f` of `A` whose value is
at most `1` at *every* point of `Spa(A, A⁺)` already lies in `A⁺`. The converse is the defining
condition of `spa`, so the two together say that `A⁺` is exactly the sub-unit locus of the adic
spectrum — the half proved here is the one that has content.

## Where it comes from

`spa A⁺` consists of the *continuous* valuations that are at most `1` on `A⁺`
(`TauCeti.ValuationSpectrum.mem_spa_iff`), so the hypothesis is precisely the hypothesis of
Wedhorn's Proposition 7.18(1),
`TauCeti.Huber.isIntegral_of_forall_continuous_valuation_le_one`. That criterion returns
integrality of `f` over `A⁺`, and a ring of integral elements is integrally closed in `A` by
definition, so `f ∈ A⁺` follows.

The all-valuations criterion `TauCeti.isIntegral_of_forall_valuation_le_one` does *not* suffice
here: its hypothesis quantifies over every valuation of `A`, and a point of `Spa(A, A⁺)` supplies
only the continuous ones. Cutting the criterion down to the continuous valuations is exactly what
Wedhorn 7.18(1) does and what this statement consumes.

## The two hypotheses beyond a Huber pair

* `[IsDomain A]`. Wedhorn states 7.52(1) with no such hypothesis; it is inherited from
  `isIntegral_of_forall_continuous_valuation_le_one`, whose construction separates `f` from the
  integral closure of `A⁺` inside `FractionRing A`. Removing it needs the continuous criterion in
  domain-free form — the reduction modulo a prime that
  `TauCeti.isIntegral_of_forall_isPrime_map` performs for the all-valuations criterion, carried
  along the quotient topology.
* `hA₀`, that the chosen ring of definition lies inside `A⁺`. This is a choice, not a
  restriction, in the situations Wedhorn's proof uses: `A⁺` is open, so intersecting any ring of
  definition with it again gives a bounded open subring. Producing a `PairOfDefinition` from that
  intersection is a separate construction, so the containment is asked for here.

## Main results

* `TauCeti.ValuationSpectrum.mem_of_forall_vle_one` : Proposition 7.52(1).
* `TauCeti.ValuationSpectrum.coe_eq_setOf_forall_vle_one` : the same statement as the displayed
  set equality `A⁺ = {a ∈ A : v(a) ≤ 1 for every v ∈ Spa(A, A⁺)}`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Propositions 7.18 and 7.52.

## Provenance

Assembled here from `TauCeti.Huber.isIntegral_of_forall_continuous_valuation_le_one` and
`TauCeti.Huber.IsRingOfIntegralElements`; nothing is ported. AINTLIB reaches 7.52(1) by a
different route, the height-one reduction pairing Wedhorn's Propositions 7.18 and 7.41, which is
not followed.
-/

public section

open TauCeti.Huber

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Wedhorn's Proposition 7.52(1)**: an element of `A` whose value is at most `1` at every
point of `Spa(A, A⁺)` lies in `A⁺`.

The points of `Spa(A, A⁺)` are the continuous valuations that are sub-unit on `A⁺`, so the
hypothesis is the hypothesis of Wedhorn's Proposition 7.18(1); that criterion makes `f` integral
over `A⁺`, and `A⁺` is integrally closed in `A`.

See the module docstring for the two hypotheses that go beyond a Huber pair: `[IsDomain A]`,
inherited from the criterion, and `hA₀`, that the ring of definition lies inside `A⁺`. -/
theorem mem_of_forall_vle_one [NonarchimedeanRing A] [IsDomain A]
    (P : PairOfDefinition A) {Aplus : Subring A} (hplus : IsRingOfIntegralElements Aplus)
    (hA₀ : (P.ringOfDefinition : Set A) ⊆ Aplus) {f : A}
    (hf : ∀ v ∈ spa Aplus, v.toValuativeRel.vle f 1) : f ∈ Aplus :=
  Subring.isIntegrallyClosedIn_iff.mp hplus.isIntegrallyClosedIn
    (isIntegral_of_forall_continuous_valuation_le_one P hplus.isOpen hA₀ fun v hcont hv ↦
      hf v ((mem_spa_iff Aplus v).mpr ⟨hcont, hv⟩))

/-- **Wedhorn's Proposition 7.52(1)** as a set equality: `A⁺` *is* the locus of `A` on which
every point of `Spa(A, A⁺)` is sub-unit.

The inclusion `⊆` is the defining condition of `spa` and needs none of the hypotheses; the
content is `mem_of_forall_vle_one`, which supplies `⊇`. -/
theorem coe_eq_setOf_forall_vle_one [NonarchimedeanRing A] [IsDomain A]
    (P : PairOfDefinition A) {Aplus : Subring A} (hplus : IsRingOfIntegralElements Aplus)
    (hA₀ : (P.ringOfDefinition : Set A) ⊆ Aplus) :
    (Aplus : Set A) = {a | ∀ v ∈ spa Aplus, v.toValuativeRel.vle a 1} :=
  Set.ext fun _ ↦
    ⟨fun ha v hv ↦ ((mem_spa_iff Aplus v).mp hv).2 _ ha, mem_of_forall_vle_one P hplus hA₀⟩

end TauCeti.ValuationSpectrum
