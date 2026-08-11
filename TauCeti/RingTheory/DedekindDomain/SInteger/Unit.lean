/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import TauCeti.GroupTheory.Finiteness

/-!
# Finite generation of the `S`-units

Mathlib defines the group `Set.unit S K` of `S`-units — the `x : Kˣ` with `v x = 1` for every
`v ∉ S` — and identifies it with the units of the ring of `S`-integers, but says nothing about its
size. Its own module docstring records the gap: `Mathlib/RingTheory/DedekindDomain/SInteger.lean`
lists as future work *"finite generation of `S`-units and Dirichlet's `S`-unit theorem"*, and
`Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean` likewise carries *"TODO: proofs of finiteness
for global fields"*. This file supplies the finite-generation half.

## Main results

* `Set.unit_fg`: **if `S` is finite and the `∅`-units are finitely generated, so are the
  `S`-units.**
* `Set.unit_fg_of_units`: the same with the hypothesis over the base ring, `[Group.FG Rˣ]` — the
  form the arithmetic actually applies, since a caller holds `Rˣ` and not the `∅`-units. An
  `instance`.
* `Set.unitValuation_ker`: the kernel of the `S`-valuation map is the `∅`-units, which is the
  left-exactness `1 → 𝒪_K^× → 𝒪_{K,S}^× → ∏_{v∈S} ℤ`. Mathlib records the absence of any such
  finiteness statement as a TODO in `RingTheory/DedekindDomain/SInteger.lean`.

The argument is one application of `Group.fg_of_fg_ker_of_fg_range`. Sending an `S`-unit to its
tuple of valuations at the primes *in* `S` gives `Set.unitValuation`, a homomorphism to `ℤ^S`; its
image is a subgroup of a finitely generated commutative group and so is finitely generated, and its
kernel is the group of `∅`-units (`Set.unitValuation_ker`), which is `Rˣ`
(`Set.unitEmptyEquivUnits`). An extension of finitely generated groups is finitely generated.

`Set.unit_mono` — the `S`-units grow with `S` — is what lets `unit_fg` identify the kernel
subgroup with the `∅`-units along `Subgroup.subgroupOfEquivOfLe`; it is not in Mathlib.

The rank refinement — that the rank is exactly `rank Rˣ + |S|` when the class group is finite — is
a separate topic and is not here.

This is the second of the two finiteness inputs that
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 names for the weak Mordell–Weil theorem:
"`A(S, 2)` is finite because the `S`-class group is finite and **the `S`-units are finitely
generated** (AEC VIII.1)."

## Relation to mathlib4#40791

**The names, statements and proofs here are taken from the open Mathlib pull request
[mathlib4#40791](https://github.com/leanprover-community/mathlib4/pull/40791), "feat(RingTheory/
DedekindDomain): dirichlet's s-unit theorem", by `vvvv-ops`, open since 2026-06-19**, which adds
`Mathlib/RingTheory/DedekindDomain/SUnit.lean` and proves exactly this (and more: the rank formula
and its number-field specialisation). Following that PR rather than inventing a parallel API is
deliberate — when Mathlib bumps past it, almost all of this file is deleted outright instead of
being reconciled name by name. **`unit_fg_of_units` is the exception: it has no #40791 analogue,
so at bump time it must be re-homed onto Mathlib's `Set.unit_fg`, not dropped with the rest.**

**Three declarations here are not that PR's**, and are marked as such where they occur:

* `unitValuation_apply` cannot be `rfl` as it is upstream, because this repository's module
  convention is `public section` without `@[expose]`, so the definition body is not visible even
  inside the file.
* `unit_mono` is stated for an arbitrary `S ⊆ S'`, of which #40791's `unit_empty_le` is the
  `S = ∅` case.
* **`unit_fg_of_units` is new here**, with no counterpart in #40791: upstream gives
  `unitEmptyEquivUnits` its consumer in the rank formula, which is not ported, so without this
  form the theorem is awkward to apply — a caller holds `Rˣ`, not the `∅`-units.

`valuationOfNeZero_eq_one_iff` is also local: Stoll's source uses
`HeightOneSpectrum.valuationOfNeZero_eq_iff`, which does not exist at our pin, and Mathlib has
only the coercion form `valuationOfNeZero_eq`.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` at
the roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll), and then restated to match
mathlib4#40791 as described above. Following this repository's convention for adapted material, the
upstream authorship is credited here rather than in the copyright header.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/-- A unit has trivial `v`-adic `valuationOfNeZero` iff its `v`-adic valuation is `1`. Mathlib
carries this only in the coerced form `valuationOfNeZero_eq`, which this complements; it lives
beside that lemma rather than in `Set`, since it mentions no set. -/
theorem valuationOfNeZero_eq_one_iff {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuationOfNeZero x = 1 ↔ v.valuation K (x : K) = 1 := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq, WithZero.coe_one]

end IsDedekindDomain.HeightOneSpectrum

namespace Set

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Set (HeightOneSpectrum R)) (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The `S`-valuation map on `S`-units: `u ↦ (v(u))_{v ∈ S}`, valued in `↥S → Multiplicative ℤ`. -/
noncomputable def unitValuation : S.unit K →* (↥S → Multiplicative ℤ) :=
  MonoidHom.pi fun v ↦ (v : HeightOneSpectrum R).valuationOfNeZero.comp (S.unit K).subtype

@[simp]
theorem unitValuation_apply (u : S.unit K) (v : ↥S) :
    unitValuation S K u v = (v : HeightOneSpectrum R).valuationOfNeZero ((u : Kˣ)) := by
  -- mathlib4#40791 proves this by `rfl`; here a `public section` without `@[expose]` leaves the
  -- body unexposed, so the definition has to be named explicitly
  simp only [unitValuation, MonoidHom.pi_apply, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype]

/-- The `S`-units grow with `S`: enlarging the set of allowed primes only weakens the condition
`v x = 1` for `v ∉ S`. mathlib4#40791's `unit_empty_le` is the case `S = ∅`. -/
theorem unit_mono {S S' : Set (HeightOneSpectrum R)} (h : S ⊆ S') : S.unit K ≤ S'.unit K :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (h hvS)

/-- **The kernel of the `S`-valuation map is the `∅`-units.** Equivalently, an `S`-unit lies in the
kernel iff it has trivial valuation at every prime — i.e. it is a unit of `𝒪_K`. This is the exact
`1 → 𝒪_K^× → 𝒪_{K,S}^× → ∏_{v∈S} ℤ` left-exactness. The codomain is the product `↥S →
Multiplicative ℤ`; this theorem does not assume `S` finite, so it is not the direct sum. -/
theorem unitValuation_ker :
    (unitValuation S K).ker = ((∅ : Set (HeightOneSpectrum R)).unit K).subgroupOf (S.unit K) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, funext_iff]
  constructor
  · intro h v _
    by_cases hvS : v ∈ S
    · have := h ⟨v, hvS⟩
      rwa [unitValuation_apply, Pi.one_apply, valuationOfNeZero_eq_one_iff] at this
    · exact u.property v hvS
  · intro h v
    rw [unitValuation_apply, Pi.one_apply, valuationOfNeZero_eq_one_iff]
    exact h v (Set.notMem_empty v)

/-- **Finite generation of `S`-units.** If `S` is finite and the `∅`-units `𝒪_K^×` are finitely
generated (e.g. `K` is a number field, by Dirichlet's unit theorem), then the `S`-units `𝒪_{K,S}^×`
are finitely generated. The kernel of `unitValuation` is `𝒪_K^×` (`unitValuation_ker`) and its range
is a subgroup of the finitely generated free *abelian* group `↥S → ℤ` — commutativity is what
makes the subgroup finitely generated — so `𝒪_{K,S}^×` is an extension of
finitely generated by finitely generated. -/
theorem unit_fg [Finite S] (hu : Group.FG ((∅ : Set (HeightOneSpectrum R)).unit K)) :
    Group.FG (S.unit K) := by
  -- `Group.FG (↥S → Multiplicative ℤ)` is Mathlib's `Pi.instGroupFG` composed with
  -- `Group.fg_of_mul_group_fg` and `AddGroup.FG ℤ`; instance search finds it from `[Finite S]`
  have : Group.FG (unitValuation S K).ker := by
    rw [unitValuation_ker]
    exact Group.fg_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe (unit_mono K S.empty_subset)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (unit_mono K S.empty_subset)).symm.surjective
  exact Group.fg_of_fg_ker_of_fg_range (unitValuation S K)

/-- The `∅`-units are exactly the units of the base ring: `Set.unit ∅ K ≃* Rˣ`. The `∅`-integers
are the base ring `R` (`IsDedekindDomain.integer_empty`), and `S`-units are the units of the
`S`-integers (`Set.unitEquivUnitsInteger`).

`private`, unlike mathlib4#40791's, because its only consumer is `unit_fg_of_units` just below:
this repository's bare `public section` leaves the body of a three-fold composite equiv
unexposed, so exporting it without a characteristic lemma would give consumers something they
cannot identify — and upstream's consumer, the rank formula, is not ported. -/
private noncomputable def unitEmptyEquivUnits : (∅ : Set (HeightOneSpectrum R)).unit K ≃* Rˣ :=
  (unitEquivUnitsInteger (∅ : Set (HeightOneSpectrum R)) K).trans
    (Units.mapEquiv
      ((Subalgebra.equivOfEq _ _ (IsDedekindDomain.integer_empty R K)).trans
        (Algebra.botEquivOfInjective (IsFractionRing.injective R K))).toRingEquiv.toMulEquiv)

/-- **Finite generation of the `S`-units, over the base ring.** If `Rˣ` is finitely generated and
`S` is finite, then so is the group of `S`-units. This is `unit_fg` with its hypothesis
transported along `unitEmptyEquivUnits`, and it is the form the arithmetic uses — the `∅`-units
are not what a caller has in hand, `Rˣ` is.

This is *not* Dirichlet's `S`-unit theorem: finite generation of `Rˣ` is assumed, not proved (for
`R = 𝒪_K` that assumption is Dirichlet's unit theorem itself), no rank is computed, and `R` is an
arbitrary Dedekind domain rather than the ring of integers of a global field.

**New here**, with no counterpart in mathlib4#40791: upstream gives `unitEmptyEquivUnits` its
consumer in the rank formula, which is not ported. -/
instance unit_fg_of_units [Finite S] [Group.FG Rˣ] : Group.FG (S.unit K) :=
  unit_fg S K <| Group.fg_of_surjective (f := (unitEmptyEquivUnits K).symm.toMonoidHom)
    (unitEmptyEquivUnits K).symm.surjective

end Set

end
