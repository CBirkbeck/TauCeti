/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# The group of fractional ideals is free abelian on the primes

Let `R` be a Dedekind domain with fraction field `K`. The nonzero fractional ideals of `R` form a
group `(FractionalIdeal R⁰ K)ˣ`, every nonzero fractional ideal being invertible, and unique
factorization says that group is free abelian on the height one primes. Mathlib has the valuation
bookkeeping — `IsDedekindDomain.HeightOneSpectrum.count` and the factorization lemmas in
`Mathlib/RingTheory/DedekindDomain/Factorization.lean` — but does not package the isomorphism
itself.

## Main definitions and results

* `FractionalIdeal.prod_count` and `FractionalIdeal.count_injective`: a nonzero fractional ideal
  is the product of `v ^ count v` over the primes, and is determined by its valuations.
* `FractionalIdeal.factorization`: the isomorphism
  `(FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ)`, sending a fractional
  ideal to its tuple of valuations.
* `ClassGroup.mk_eq_one_iff_exists`: a unit fractional ideal has trivial class exactly when it is
  `toPrincipalIdeal x` for a unit `x` of `K` — the variant of `ClassGroup.mk_eq_one_iff` that
  hands back the generator instead of `Submodule.IsPrincipal`.

This is the count/factorization machinery that the `S`-integer class group computation
`Cl(𝒪_S) ≃* Cl(R) ⧸ ⟨[v] : v ∈ S⟩` rests on, which in turn is what
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 needs for weak Mordell–Weil.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/FractionalIdeal.lean`
at the roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll), the source the roadmap's
§Provenance names for the Layer 6 Mordell–Weil lane. Following this repository's convention for
adapted material, the upstream authorship is credited here rather than in the copyright header.
Ported with the source's blanket `import Mathlib` narrowed to the two modules actually used and
its `@[expose]` dropped.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace FractionalIdeal

section PrincipalIdeal

variable [IsDomain R]

/-- The principal fractional ideal `(x)` is trivial exactly when `x` comes from a unit of `R`. -/
lemma spanSingleton_eq_one_iff {x : K} (hx : x ≠ 0) :
    spanSingleton R⁰ x = 1 ↔ ∃ a : Rˣ, algebraMap R K a = x := by
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
  rw [← Units.val_inj, coe_toPrincipalIdeal, Units.val_one, spanSingleton_eq_one_iff u.ne_zero]
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

end PrincipalIdeal

variable [IsDedekindDomain R]

/-- A nonzero fractional ideal is the product `∏ v ^ count v` over the height one primes. -/
theorem prod_count {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v I = I := by
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  simp_rw [fun v ↦ count_well_defined K v hI haJ]
  exact finprod_heightOneSpectrum_factorization hI haJ

/-- The prime `v` as a unit of the group of fractional ideals. -/
noncomputable def unitOfPrime (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp] lemma coe_unitOfPrime (v : HeightOneSpectrum R) :
    ((unitOfPrime v : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = v.asIdeal := by
  simp only [unitOfPrime, Units.val_mk0]

/-- The finitely-supported tuple of valuations of a unit fractional ideal. -/
noncomputable def toFinsupp (I : (FractionalIdeal R⁰ K)ˣ) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v ↦ count K v (I : FractionalIdeal R⁰ K)) (by
    have := finite_factors (I : FractionalIdeal R⁰ K)
    simpa [Function.support, Filter.eventually_cofinite] using this)

@[simp] lemma toFinsupp_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    toFinsupp I v = count K v (I : FractionalIdeal R⁰ K) := by
  simp only [toFinsupp, Finsupp.ofSupportFinite_coe]

/-- The unit fractional ideal `∏ v ^ g v`. -/
noncomputable def ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) : (FractionalIdeal R⁰ K)ˣ :=
  g.prod (fun v e ↦ unitOfPrime v ^ e)

lemma coe_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) :
    ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K)
      = g.prod (fun v e ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ e) := by
  rw [ofFinsupp, ← Units.coeHom_apply, map_finsuppProd]
  simp [Units.coeHom]

lemma count_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) (v : HeightOneSpectrum R) :
    count K v ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = g v := by
  rw [coe_ofFinsupp, count_finsuppProd]

/-- A unit fractional ideal is determined by its valuations. -/
lemma count_injective {I J : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v, count K v (I : FractionalIdeal R⁰ K) = count K v (J : FractionalIdeal R⁰ K)) :
    I = J := by
  apply Units.ext
  rw [← prod_count (Units.ne_zero I), ← prod_count (Units.ne_zero J)]
  exact finprod_congr fun v ↦ by rw [h v]

end FractionalIdeal

end
