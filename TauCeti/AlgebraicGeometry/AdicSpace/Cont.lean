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

* `TauCeti.ValuationSpectrum.IsContinuous` : continuity of a point of `Spv A`, in the
  attained-value sense.
* `TauCeti.ValuationSpectrum.cont` : **Wedhorn's `Cont A`**, the set of continuous points, cut
  out by the attained-value test — see its docstring for how that relates to Wedhorn's
  value-group quantifier.

## Main results

* `TauCeti.ValuationSpectrum.isContinuous_ofValuation` and
  `TauCeti.ValuationSpectrum.ofValuation_mem_cont_iff` : continuity may be tested on any
  representative, not only the canonical one — the well-definedness making `cont` meaningful,
  as a predicate and as set membership.
* `TauCeti.ValuationSpectrum.IsContinuous.comap` : **Remark 7.9**, that a continuous ring
  homomorphism pulls continuous points back to continuous points, so `comap φ` restricts to
  `Cont B → Cont A`.
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

/-- **Continuity of a point of `Spv A`.** A point is *continuous* when its canonical valuation
is, in the attained-value sense of `TauCeti.Valuation.IsContinuous`. Any representative would do
— that is `isContinuous_ofValuation` — but the canonical one makes the definition depend on
nothing chosen.

Under `[SeparatelyContinuousMul A]` this is Wedhorn's Definition 7.7; see `cont`. -/
def IsContinuous (v : Spv A) : Prop :=
  v.valuation.IsContinuous

/-- Continuity of a point, unfolded to its canonical valuation. -/
@[simp]
theorem isContinuous_def (v : Spv A) : v.IsContinuous ↔ v.valuation.IsContinuous :=
  Iff.rfl

/-- **Wedhorn's `Cont A`**: the continuous points of `Spv A`, as a `Set (Spv A)`. Wedhorn calls
it a subspace; here it is the underlying set, and the subspace topology is the one the *coercion*
`↥(cont A)` carries as a subtype of `Spv A`.

Membership is the attained-value test of `TauCeti.Valuation.IsContinuous`, which is Wedhorn's
Definition 7.7 once multiplication is separately continuous —
`isContinuous_iff_forall_isOpen_lt_div` is that step, and it is where
`[SeparatelyContinuousMul A]` is asked for. It is *not* asked for
here: an unused instance argument is a lint violation, and every setting `Cont A` is used in — a
Huber ring, and `Spa` beyond it — is a topological ring, which supplies it at the point of use. -/
def cont (A : Type*) [CommRing A] [TopologicalSpace A] : Set (Spv A) :=
  {v : Spv A | v.IsContinuous}

@[simp]
theorem mem_cont_iff (v : Spv A) : v ∈ cont A ↔ v.IsContinuous := Iff.rfl

/-- **Continuity may be tested on any representative.** This is what makes `cont` well defined:
the point `ofValuation w` is continuous exactly when `w` is, for every `w` in the class, not
merely for the canonical one. It rests on `TauCeti.Valuation.IsEquiv.isContinuous_iff`, and
would fail for a continuity predicate quantified over the ambient codomain.

Not `@[simp]`: `isContinuous_def` already rewrites the left-hand side, so this would not be in
simp-normal form. -/
theorem isContinuous_ofValuation {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation A Γ₀) : (ofValuation w).IsContinuous ↔ w.IsContinuous :=
  (isEquiv_valuation_ofValuation w).isContinuous_iff

/-- **Membership in `Cont A` may be tested on any representative.** The `@[simp]` form of
`isContinuous_ofValuation` at the level of the set: `ofValuation w` is a continuous *point*
exactly when `w` is a continuous *valuation*, for every `w` in the class. Representative
independence is the whole reason `cont` is well defined, so this is its characteristic lemma.

Not `@[simp]`, although it is the characteristic lemma: `mem_cont_iff`, `isContinuous_def` and
`Valuation.isContinuous_def` are already simp lemmas, and together they rewrite this left-hand
side all the way down to the raw quantifier, so no statement about `ofValuation w ∈ cont A` can
be in simp-normal form. -/
theorem ofValuation_mem_cont_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation A Γ₀) : ofValuation w ∈ cont A ↔ w.IsContinuous :=
  isContinuous_ofValuation w

/-- **Wedhorn Remark 7.8(2).** Over a discrete ring every point is continuous. -/
@[simp]
theorem cont_eq_univ [DiscreteTopology A] : cont A = Set.univ :=
  Set.eq_univ_of_forall fun v ↦
    (mem_cont_iff v).mpr ((isContinuous_def v).mpr (isContinuous_of_discreteTopology v.valuation))

/-- **Wedhorn Remark 7.9.** A continuous ring homomorphism pulls continuous points back to
continuous points, so it restricts to a map `Cont B → Cont A`. -/
theorem IsContinuous.comap {B : Type*} [CommRing B] [TopologicalSpace B] {φ : A →+* B}
    (hφ : Continuous φ) {v : Spv B} (hv : v.IsContinuous) : (comap φ v).IsContinuous := by
  rw [← ofValuation_valuation v, comap_ofValuation, isContinuous_ofValuation]
  exact (isContinuous_def v |>.mp hv).comap hφ

/-- **Remark 7.9 at the level of the subspaces.** `Cont B` lands inside the preimage of
`Cont A` along `comap φ`, so `comap φ` restricts to a map `Cont B → Cont A`.

This is the set-level form of `IsContinuous.comap`, and is stated separately because it is the
form a consumer of the subspaces actually applies: the pointwise version has to be threaded
through membership and preimage by hand at each call site, and it is this containment — not the
pointwise implication — that the module docstring claims. -/
theorem cont_subset_comap_preimage {B : Type*} [CommRing B] [TopologicalSpace B]
    {φ : A →+* B} (hφ : Continuous φ) :
    cont B ⊆ comap φ ⁻¹' cont A := fun v hv ↦
  Set.mem_preimage.mpr ((mem_cont_iff _).mpr (IsContinuous.comap hφ ((mem_cont_iff v).mp hv)))

end TauCeti.ValuationSpectrum
