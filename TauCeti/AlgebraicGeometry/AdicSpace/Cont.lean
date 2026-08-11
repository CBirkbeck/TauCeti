/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum
public import TauCeti.RingTheory.Valuation.Continuous

/-!
# The space `Cont A` of continuous valuations

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.7 and Remark 7.9.**

`Cont A` is the subspace of `Spv A` cut out by continuity. Wedhorn defines it in one line —
"the subspace of `Spv (A)` of continuous valuations" — but that line only makes sense because
continuity is a property of the *equivalence class*, not of a chosen representative. That is
what this file supplies, and it is the whole of its mathematical content.

## Why this is not automatic

A point of `Spv A` is a valuative relation, so a predicate on valuations descends to it only if
equivalent valuations agree on the predicate. For continuity as Wedhorn states it — the
quantifier running over the value group `Γ_v` — that holds, and
`TauCeti.Valuation.IsEquiv.isContinuous_iff` says so. Had continuity instead been asked of every
`γ` in the ambient codomain, it would **not** descend, and `Cont A` would not be well defined;
the module docstring of `TauCeti.RingTheory.Valuation.Continuous` carries the counterexample.

So `IsContinuous` is defined here by testing the *canonical* valuation of the point, and
`isContinuous_ofValuation` says the test may equally be run on any representative.

## Main definitions

* `TauCeti.ValuationSpectrum.IsContinuous` : continuity of a point of `Spv A`.
* `TauCeti.ValuationSpectrum.cont` : **Wedhorn's `Cont A`**, the set of continuous points.

## Main results

* `TauCeti.ValuationSpectrum.isContinuous_ofValuation` : continuity may be tested on any
  representative, not only the canonical one — the well-definedness making `cont` meaningful.
* `TauCeti.ValuationSpectrum.IsContinuous.comap` : **Remark 7.9**, that a continuous ring
  homomorphism pulls continuous points back to continuous points.
* `TauCeti.ValuationSpectrum.cont_eq_univ` : **Remark 7.8(2)**, `Cont A = Spv A` for discrete `A`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.7 and Remarks 7.8, 7.9.

## Provenance

The corresponding development in AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch
`dev/adic-spaces` at commit `37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, project
`projects/AdicSpaces/`, file `Adic spaces/ContinuousValuations.lean`, was consulted rather than
copied. Its `ValuationSpectrum.IsContinuous` also tests the canonical valuation, but because its
valuation-level predicate quantifies over the ambient codomain it can only offer the one-way
`isContinuous_ofValuation_of`; the `↔` here is what makes `cont` well defined.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti TauCeti.Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Wedhorn Definition 7.7 at a point of `Spv A`.** A point is *continuous* when its canonical
valuation is. Any representative would do — that is `isContinuous_ofValuation` — but the
canonical one makes the definition depend on nothing chosen. -/
def IsContinuous (v : Spv A) : Prop :=
  v.valuation.IsContinuous

/-- Continuity of a point, unfolded to its canonical valuation. -/
@[simp]
theorem isContinuous_def (v : Spv A) : v.IsContinuous ↔ v.valuation.IsContinuous :=
  Iff.rfl

/-- **Wedhorn's `Cont A`**: the continuous points of `Spv A`, with the subspace topology it
inherits as a `Set (Spv A)`. -/
def cont (A : Type*) [CommRing A] [TopologicalSpace A] : Set (Spv A) :=
  {v : Spv A | v.IsContinuous}

@[simp]
theorem mem_cont_iff (v : Spv A) : v ∈ cont A ↔ v.IsContinuous := Iff.rfl

/-- **Continuity may be tested on any representative.** This is what makes `cont` well defined:
the point `ofValuation w` is continuous exactly when `w` is, for every `w` in the class, not
merely for the canonical one. It rests on `TauCeti.Valuation.IsEquiv.isContinuous_iff`, and
would fail for a continuity predicate quantified over the ambient codomain. -/
@[simp]
theorem isContinuous_ofValuation {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    (w : Valuation A Γ₀) : (ofValuation w).IsContinuous ↔ w.IsContinuous :=
  (isEquiv_valuation_ofValuation w).isContinuous_iff

/-- **Wedhorn Remark 7.8(2).** Over a discrete ring every point is continuous. -/
@[simp]
theorem cont_eq_univ [DiscreteTopology A] : cont A = Set.univ :=
  Set.eq_univ_of_forall fun v ↦ isContinuous_of_discreteTopology v.valuation

/-- **Wedhorn Remark 7.9.** A continuous ring homomorphism pulls continuous points back to
continuous points, so it restricts to a map `Cont B → Cont A`. -/
theorem IsContinuous.comap {B : Type*} [CommRing B] [TopologicalSpace B] {φ : A →+* B}
    (hφ : Continuous φ) {v : Spv B} (hv : v.IsContinuous) : (comap φ v).IsContinuous := by
  rw [← ofValuation_valuation v, comap_ofValuation, isContinuous_ofValuation]
  exact (isContinuous_def v |>.mp hv).comap hφ

/-- Remark 7.9 in the form a consumer of the subspaces uses: `Cont B` lands inside the preimage
of `Cont A` along the induced map `comap φ : Spv B → Spv A`, so `comap φ` restricts to
`Cont B → Cont A`. -/
theorem cont_subset_comap_preimage {B : Type*} [CommRing B] [TopologicalSpace B] {φ : A →+* B}
    (hφ : Continuous φ) : cont B ⊆ comap φ ⁻¹' cont A :=
  fun _ hv ↦ IsContinuous.comap hφ hv

end TauCeti.ValuationSpectrum
