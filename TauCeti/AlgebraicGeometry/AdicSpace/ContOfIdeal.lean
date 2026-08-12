/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Cont
public import TauCeti.AlgebraicGeometry.AdicSpace.SpvOfIdeal.Basic
public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# A continuous point of a Huber ring lies in `Spv (A, I·A)`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Theorem 7.10, the inclusion `Cont A ⊆ Spv(A, IA)`.**

Theorem 7.10 identifies `Cont A` inside `Spv (A, IA)` for a pair of definition `(A₀, I)`. This
file proves the half that says the identification is well posed at all: a continuous point does
lie in `Spv (A, IA)`.

The argument is Wedhorn's and needs no estimate. Membership in `Spv (A, IA)` is
`cΓ_v(IA) = Γ_v`, which by Lemma 7.4 follows from cofinality of `v` at every element of a
*spanning set* of `IA` — and `IA` is spanned by the image of `I`, whose elements are
topologically nilpotent, by
`TauCeti.Huber.PairOfDefinition.isTopologicallyNilpotent_of_mem_idealOfDefinition`. Continuity
turns topological nilpotence into cofinality, by
`TauCeti.Valuation.IsContinuous.cofinalValue_of_isTopologicallyNilpotent`.

Passing through a spanning set is what makes this work, and the spanning form of Lemma 7.4 exists
for exactly this reason. A general element of `IA` is a sum `Σ xᵢ aᵢ` with `xᵢ ∈ I` and `aᵢ ∈ A`
arbitrary, and such a sum need not be topologically nilpotent — the nilpotence is a property of
the generators, not of the extended ideal.

## Main results

* `TauCeti.ValuationSpectrum.mem_spvOfIdeal_extendedIdealOfDefinition_of_isContinuous` : a
  continuous point of `Spv A` lies in `Spv (A, IA)`.
* `TauCeti.ValuationSpectrum.cont_subset_spvOfIdeal_extendedIdealOfDefinition` : the same as an
  inclusion of subsets of `Spv A`.

The converse inclusion, which is the substance of Theorem 7.10, is not proved here: it needs a
uniform exponent across the finitely many generators of `I`, and that estimate is not yet on
`main`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Theorem 7.10 and Lemma 7.4.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti TauCeti.Huber TauCeti.Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Wedhorn Theorem 7.10, the inclusion `Cont A ⊆ Spv (A, IA)`.** A continuous point of the
valuation spectrum of a Huber ring lies in `Spv (A, IA)` for the extended ideal of definition of
any pair of definition.

The hypothesis `hfg` is Wedhorn's standing assumption for §7.1; for this ideal it is always
available, since `IA` is itself finitely generated
(`TauCeti.Huber.PairOfDefinition.fg_extendedIdealOfDefinition`). -/
theorem mem_spvOfIdeal_extendedIdealOfDefinition_of_isContinuous (P : PairOfDefinition A)
    (hfg : ∃ J : Ideal A, J.FG ∧ P.extendedIdealOfDefinition.radical = J.radical) {v : Spv A}
    (hv : v.IsContinuous) : v ∈ spvOfIdeal P.extendedIdealOfDefinition hfg := by
  rw [mem_spvOfIdeal_iff]
  refine (characteristicSubgroupOfIdeal_eq_top_iff_forall_span (v := v.valuation) hfg
    (T := Subtype.val '' (P.idealOfDefinition : Set P.ringOfDefinition)) ?_ rfl).mpr (Or.inl ?_)
  · rw [P.extendedIdealOfDefinition_def, Ideal.map, Subring.coe_subtype]
  · rintro _ ⟨a, ha, rfl⟩
    exact ((isContinuous_def _).mp hv).cofinalValue_of_isTopologicallyNilpotent
      (P.isTopologicallyNilpotent_of_mem_idealOfDefinition ha)

/-- **Wedhorn Theorem 7.10, the inclusion `Cont A ⊆ Spv (A, IA)`**, as an inclusion of subsets. -/
theorem cont_subset_spvOfIdeal_extendedIdealOfDefinition (P : PairOfDefinition A)
    (hfg : ∃ J : Ideal A, J.FG ∧ P.extendedIdealOfDefinition.radical = J.radical) :
    cont A ⊆ spvOfIdeal P.extendedIdealOfDefinition hfg :=
  fun _ hv ↦
    mem_spvOfIdeal_extendedIdealOfDefinition_of_isContinuous P hfg ((mem_cont_iff _).mp hv)

end TauCeti.ValuationSpectrum

end
