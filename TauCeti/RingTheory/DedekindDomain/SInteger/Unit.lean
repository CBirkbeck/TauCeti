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

The argument is one application of `Group.fg_of_fg_ker_of_fg_range`. Sending an `S`-unit to its
tuple of valuations at the primes *in* `S` gives `Set.unitValuation`, a homomorphism to `ℤ^S`; its
image is a subgroup of a finitely generated commutative group and so is finitely generated, and its
kernel is the group of `∅`-units (`Set.unitValuation_ker`), which is `Rˣ`
(`Set.unitEmptyEquivUnits`). An extension of finitely generated groups is finitely generated.

`Set.unit_mono` — the `S`-units grow with `S` — is the small monotonicity step the kernel
computation needs, and is not in Mathlib.

The rank refinement — that the rank is exactly `rank Rˣ + |S|` when the class group is finite — is
a separate topic and is not here.

This is the second of the two finiteness inputs that
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 names for the weak Mordell–Weil theorem:
"`A(S, 2)` is finite because the `S`-class group is finite and **the `S`-units are finitely
generated** (AEC VIII.1)."

## Relation to mathlib4#40791

**The names, statements and proofs here are taken from the open Mathlib pull request
[mathlib4#40791](https://github.com/leanprover-community/mathlib4/pull/40791), "feat(RingTheory/
DedekindDomain): dirichlet's s-unit theorem"**, which adds `Mathlib/RingTheory/DedekindDomain/
SUnit.lean` and proves exactly this (and more: the rank formula and its number-field
specialisation). Following that PR rather than inventing a parallel API is deliberate — when Mathlib
bumps past it, this file is deleted outright instead of being reconciled name by name. The two
deviations are recorded at the declarations that carry them: `unitValuation_apply` cannot be `rfl`
here, because this repository's module convention is `public section` without `@[expose]`, so the
definition body is not visible even inside the file; and `unit_mono` is stated for an arbitrary
`S ⊆ S'` rather than only `∅ ⊆ S`, of which #40791's `unit_empty_le` is the special case.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` at
the roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll), and then restated to match
mathlib4#40791 as described above. Following this repository's convention for adapted material, the
upstream authorship is credited here rather than in the copyright header.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Set

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Set (HeightOneSpectrum R)) (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The `S`-valuation map on `S`-units: `u ↦ (v(u))_{v ∈ S}`, valued in `↥S → Multiplicative ℤ`. -/
noncomputable def unitValuation : S.unit K →* (↥S → Multiplicative ℤ) where
  toFun u v := (v : HeightOneSpectrum R).valuationOfNeZero ((u : Kˣ))
  map_one' := by ext v; simp only [Subgroup.coe_one, map_one, Pi.one_apply]
  map_mul' u u' := by ext v; simp only [Subgroup.coe_mul, map_mul, Pi.mul_apply]

@[simp]
theorem unitValuation_apply (u : S.unit K) (v : ↥S) :
    unitValuation S K u v = (v : HeightOneSpectrum R).valuationOfNeZero ((u : Kˣ)) := by
  -- mathlib4#40791 proves this by `rfl`; here a `public section` without `@[expose]` leaves the
  -- body unexposed, so the definition has to be named explicitly
  simp only [unitValuation, MonoidHom.coe_mk, OneHom.coe_mk]

/-- The `S`-units grow with `S`: enlarging the set of allowed primes only weakens the condition
`v x = 1` for `v ∉ S`. mathlib4#40791's `unit_empty_le` is the case `S = ∅`. -/
theorem unit_mono {S S' : Set (HeightOneSpectrum R)} (h : S ⊆ S') : S.unit K ≤ S'.unit K :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (h hvS)

/-- A unit has trivial `v`-adic `valuationOfNeZero` iff its `v`-adic valuation is `1`. Mathlib
carries this only in the coerced form `valuationOfNeZero_eq`. -/
theorem valuationOfNeZero_eq_one_iff (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuationOfNeZero x = 1 ↔ v.valuation K (x : K) = 1 := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq, WithZero.coe_one]

/-- **The kernel of the `S`-valuation map is the `∅`-units.** Equivalently, an `S`-unit lies in the
kernel iff it has trivial valuation at every prime — i.e. it is a unit of `𝒪_K`. This is the exact
`1 → 𝒪_K^× → 𝒪_{K,S}^× → ⊕_{v∈S} ℤ` left-exactness. -/
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
is a subgroup of the finitely generated free group `↥S → ℤ`, so `𝒪_{K,S}^×` is an extension of
finitely generated by finitely generated. -/
theorem unit_fg [Finite S] (hu : Group.FG ((∅ : Set (HeightOneSpectrum R)).unit K)) :
    Group.FG (S.unit K) := by
  have : Group.FG ((∅ : Set (HeightOneSpectrum R)).unit K) := hu
  have : Group.FG (↥S → Multiplicative ℤ) := by
    rw [GroupFG.iff_add_fg, ← Module.Finite.iff_addGroup_fg]
    exact inferInstanceAs (Module.Finite ℤ (↥S → ℤ))
  have : Group.FG (unitValuation S K).ker := by
    rw [unitValuation_ker]
    exact Group.fg_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe (unit_mono K S.empty_subset)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (unit_mono K S.empty_subset)).symm.surjective
  exact Group.fg_of_fg_ker_of_fg_range (unitValuation S K)

/-- The `∅`-units are exactly the units of the base ring: `Set.unit ∅ K ≃* Rˣ`. The `∅`-integers
are the base ring `R` (`IsDedekindDomain.integer_empty`), and `S`-units are the units of the
`S`-integers (`Set.unitEquivUnitsInteger`). -/
noncomputable def unitEmptyEquivUnits : (∅ : Set (HeightOneSpectrum R)).unit K ≃* Rˣ :=
  (unitEquivUnitsInteger (∅ : Set (HeightOneSpectrum R)) K).trans
    (Units.mapEquiv
      ((Subalgebra.equivOfEq _ _ (IsDedekindDomain.integer_empty R K)).trans
        (Algebra.botEquivOfInjective (IsFractionRing.injective R K))).toRingEquiv.toMulEquiv)

/-- **Dirichlet's `S`-unit theorem, weak form**, stated over the base ring: if `Rˣ` is finitely
generated and `S` is finite, then so is the group of `S`-units. This is `unit_fg` with its
hypothesis transported along `unitEmptyEquivUnits`, and it is the form the arithmetic uses — the
`∅`-units are not what a caller has in hand, `Rˣ` is. -/
theorem unit_fg_of_units [Finite S] [Group.FG Rˣ] : Group.FG (S.unit K) :=
  unit_fg S K <| Group.fg_of_surjective (f := (unitEmptyEquivUnits K).symm.toMonoidHom)
    (unitEmptyEquivUnits K).symm.surjective

end Set

end
