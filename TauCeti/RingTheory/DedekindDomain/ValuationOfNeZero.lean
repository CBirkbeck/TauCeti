/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import TauCeti.RingTheory.DedekindDomain.Ideal

/-!
# The `Multiplicative ℤ`-valued adic valuation of a unit

Mathlib attaches to a height one prime `v` of a Dedekind domain `R` a homomorphism
`v.valuationOfNeZero : Kˣ →* Multiplicative ℤ`, the `v`-adic valuation of a unit of the fraction
field read without the adjoined zero, and relates it to `v.valuation K` in one direction only:
`valuationOfNeZero_eq` coerces it into `ℤᵐ⁰`. This file supplies the two complements that make it
usable as a rewriting rule.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_iff`: the `Multiplicative ℤ`-valued
  valuation of a unit is determined by the `ℤᵐ⁰`-valued one.
* `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_one_iff`: its `m = 1` case, that a unit
  has trivial `v`-adic `valuationOfNeZero` exactly when its `v`-adic valuation is `1`.
* `IsDedekindDomain.HeightOneSpectrum.exists_valuationOfNeZero_map_eq`: along a pair of compatible
  embeddings `ψ : B →+* C` of Dedekind domains and `φ : L →+* N` of their fraction fields, the
  `w`-adic valuation of `φ u` is the valuation of `u` at the contracted prime raised to a fixed
  power — the ramification index of `w` over that contraction.
* `IsDedekindDomain.HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map`: consequently divisibility
  of the valuation by `n` transports along such an embedding. Only the *existence* of the exponent
  matters for that, which is why the exponent is left existentially quantified above.

## Implementation notes

These live in their own module rather than beside their first consumer. `valuationOfNeZero` is
declared in `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`, so any host must import that;
but the *generic* completion and `S`-integer APIs that need these two lemmas must not, in
consequence, also inherit this repository's Selmer-group development. Keeping the pair here lets
`TauCeti/RingTheory/DedekindDomain/AdicCompletionExtension.lean` use them without depending on
`TauCeti/RingTheory/DedekindDomain/SelmerGroup.lean`, which is downstream of it.

## Provenance

Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, at the `EllipticCurves` roadmap's pin
`66889eada51a`, Apache 2.0, by Michael Stoll) reaches for a
`HeightOneSpectrum.valuationOfNeZero_eq_iff`; no such lemma exists at our Mathlib pin, so it is
supplied here. `exists_valuationOfNeZero_map_eq` and `dvd_toAdd_valuationOfNeZero_map` are adapted
from the same source (`EllipticCurves/Mathlib/Basic.lean`). Following this repository's convention
for adapted material, the upstream authorship is credited here rather than in the copyright
header.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The `Multiplicative ℤ`-valued valuation of a unit is determined by the `ℤᵐ⁰`-valued one.
Mathlib carries only the coerced form `valuationOfNeZero_eq`, which this complements. -/
@[simp]
theorem valuationOfNeZero_eq_iff (v : HeightOneSpectrum R) (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K (u : K) = (m : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]

/-- A unit has trivial `v`-adic `valuationOfNeZero` iff its `v`-adic valuation is `1`, the case
`m = 1` of `valuationOfNeZero_eq_iff`.

Not `@[simp]`: it is the `m = 1` instance of `valuationOfNeZero_eq_iff`, which carries the
annotation instead. With both marked, `simpNF` rejects this one — "simp can prove this" — because
the general form subsumes it. Every consumer names it explicitly, so nothing depends on the
attribute. -/
theorem valuationOfNeZero_eq_one_iff (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuationOfNeZero x = 1 ↔ v.valuation K (x : K) = 1 := by
  simp

section Transport

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]
  {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
  [Field N] [Algebra C N] [IsFractionRing C N]

/-- Along an embedding `ψ : B →+* C` of Dedekind domains and a compatible embedding `φ : L →+* N`
of their fraction fields, the `w`-adic valuation of `φ u` is the valuation of `u` at the
contracted prime `comapOfNeBot ψ w hne`, raised to a fixed power independent of `u` — namely the
ramification index of `w` over that contraction. -/
theorem exists_valuationOfNeZero_map_eq (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L))
    (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) :
    ∃ e : ℕ, ∀ u : Lˣ, w.valuationOfNeZero (Units.map (φ : L →* N) u) =
      (comapOfNeBot ψ w hne).valuationOfNeZero u ^ e := by
  let _ : Algebra B C := ψ.toAlgebra
  let _ : Algebra L N := φ.toAlgebra
  let _ : Algebra B N := (φ.comp (algebraMap B L)).toAlgebra
  have hψ : Function.Injective ψ := by
    have h : Function.Injective ((algebraMap C N).comp ψ) := by
      rw [hcomp]
      exact φ.injective.comp (IsFractionRing.injective B L)
    exact fun x y hxy ↦ h (by simp only [RingHom.comp_apply, hxy])
  have : IsScalarTower B L N := .of_algebraMap_eq' rfl
  have : IsScalarTower B C N := .of_algebraMap_eq fun x ↦ (RingHom.congr_fun hcomp x).symm
  have : Module.IsTorsionFree B C := Module.isTorsionFree_iff_algebraMap_injective.mpr hψ
  have : w.asIdeal.LiesOver (comapOfNeBot ψ w hne).asIdeal := ⟨rfl⟩
  refine ⟨(comapOfNeBot ψ w hne).asIdeal.ramificationIdx' w.asIdeal, fun u ↦ ?_⟩
  rw [valuationOfNeZero_eq_iff, WithZero.coe_pow, valuationOfNeZero_eq, Units.coe_map,
    MonoidHom.coe_coe]
  exact (valuation_liesOver N (comapOfNeBot ψ w hne) w (u : L)).symm

/-- Divisibility of adic valuations transports along compatible embeddings: if the valuation of
`u` at the contracted prime is divisible by `n`, so is the `w`-adic valuation of `φ u`.

This is the form in which the semilocal comparison of `2`-descent uses
`exists_valuationOfNeZero_map_eq`: ramification multiplies the valuation by a fixed factor, and
multiplication preserves divisibility, so parity — the case `n = 2` — survives in both
directions. -/
theorem dvd_toAdd_valuationOfNeZero_map (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L))
    (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) {n : ℕ} (u : Lˣ)
    (h : (n : ℤ) ∣ Multiplicative.toAdd ((comapOfNeBot ψ w hne).valuationOfNeZero u)) :
    (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero (Units.map (φ : L →* N) u)) := by
  obtain ⟨e, he⟩ := exists_valuationOfNeZero_map_eq φ ψ hcomp w hne
  rw [he u, toAdd_pow, nsmul_eq_mul]
  exact h.mul_left _

end Transport

end IsDedekindDomain.HeightOneSpectrum

end
