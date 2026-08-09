/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The kernel of the principal-ideal map

Complements to `Mathlib/RingTheory/ClassGroup/Basic.lean`, identifying when a principal
fractional ideal is trivial and when a unit fractional ideal has trivial class.

Let `R` be a domain with fraction field `K`. The principal fractional ideal `(x)` is the unit
ideal exactly when `x` is the image of a unit of `R` (`FractionalIdeal.spanSingleton_eq_one_iff`),
so the kernel of `toPrincipalIdeal` is the image of `Rˣ`
(`FractionalIdeal.toPrincipalIdeal_eq_one_iff`). Consequently a unit fractional ideal has trivial
class exactly when it is `toPrincipalIdeal x` for some `x : Kˣ`
(`ClassGroup.mk_eq_one_iff_exists`) — the variant of Mathlib's `ClassGroup.mk_eq_one_iff` that
hands back the generator instead of a `Submodule.IsPrincipal` witness, which is the form the
class-group computations consume.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/FractionalIdeal.lean`
at the roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll). Following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.
-/

public section

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace FractionalIdeal

variable [IsDomain R]

/-- The principal fractional ideal `(x)` is trivial exactly when `x` comes from a unit of `R`.
At `x = 0` both sides are false, so no nonvanishing hypothesis is needed. -/
lemma spanSingleton_eq_one_iff {x : K} :
    spanSingleton R⁰ x = 1 ↔ ∃ a : Rˣ, algebraMap R K a = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [spanSingleton_zero]
    refine ⟨fun h ↦ absurd h zero_ne_one, ?_⟩
    rintro ⟨a, ha⟩
    exact absurd ((_root_.map_eq_zero_iff _ (IsFractionRing.injective R K)).mp ha) a.ne_zero
  constructor
  · intro h
    have hinv : spanSingleton R⁰ x⁻¹ = 1 := by rw [← spanSingleton_inv, h, inv_one]
    obtain ⟨a, ha⟩ := (mem_one_iff R⁰).mp (h ▸ mem_spanSingleton_self R⁰ x)
    obtain ⟨b, hb⟩ := (mem_one_iff R⁰).mp (hinv ▸ mem_spanSingleton_self R⁰ x⁻¹)
    have hab : a * b = 1 := IsFractionRing.injective R K (by
      rw [map_mul, ha, hb, mul_inv_cancel₀ hx, map_one])
    exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩
  · rintro ⟨a, rfl⟩
    rw [← coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr a.isUnit, coeIdeal_top]

/-- `toPrincipalIdeal x = 1` exactly when `x` is a unit of `R`: the kernel of the principal-ideal
map is the image of `Rˣ`. -/
lemma toPrincipalIdeal_eq_one_iff (u : Kˣ) :
    toPrincipalIdeal R K u = 1 ↔ ∃ a : Rˣ, Units.map (algebraMap R K : R →* K) a = u := by
  rw [← Units.val_inj, coe_toPrincipalIdeal, Units.val_one, spanSingleton_eq_one_iff]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, Units.ext ha⟩, fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha]; rfl⟩⟩

/-- `ClassGroup.mk I = 1` exactly when the unit fractional ideal `I` is principal, with the
generator handed back as a unit of `K`. Variant of `ClassGroup.mk_eq_one_iff` avoiding
`Submodule.IsPrincipal`. -/
lemma _root_.ClassGroup.mk_eq_one_iff_exists {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ ∃ x : Kˣ, toPrincipalIdeal R K x = I := by
  rw [ClassGroup.mk_eq_one_iff]
  constructor
  · intro hI
    obtain ⟨x, hx⟩ := hI.principal
    have hx' : (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ x := by
      apply Subtype.coe_injective
      simp only [val_eq_coe, hx, coe_spanSingleton]
    have hx0 : x ≠ 0 := fun h ↦ Units.ne_zero I (by rw [hx', h, spanSingleton_zero])
    exact ⟨Units.mk0 x hx0, by rw [← Units.val_inj, coe_toPrincipalIdeal, hx']; rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(x : K), by rw [coe_toPrincipalIdeal, coe_spanSingleton]⟩⟩

@[simp]
lemma _root_.ClassGroup.mk_toPrincipalIdeal (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K x) = 1 :=
  ClassGroup.mk_eq_one_iff_exists.mpr ⟨x, rfl⟩

end FractionalIdeal

end
