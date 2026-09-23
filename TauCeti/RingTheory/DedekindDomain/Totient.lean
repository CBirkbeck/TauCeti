/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Euler's totient for ideals of a Dedekind domain

For an ideal `I` of an infinite Dedekind domain `R` whose quotient `R ⧸ I` is finite, this file
counts the units of `R ⧸ I` in terms of the absolute norm `N = Ideal.absNorm`:
`#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∣ I} (1 - (N 𝔭)⁻¹)`, the product running over the height-one primes
dividing `I`. For `R = ℤ` this is Euler's product formula for the totient.

The set of primes dividing `I` is passed as a `Finset` `S` together with the characterisation
`∀ v, v ∈ S ↔ v.asIdeal ∣ I`, so that any concrete description of the prime divisors of `I` can
be used directly.

## Main results

* `Ideal.card_units_quotient_mul_prod_absNorm`: `#(R ⧸ I)ˣ · ∏_{𝔭 ∈ S} N 𝔭 = N I · ∏_{𝔭 ∈ S}
  (N 𝔭 - 1)` in `ℕ`, the analogue of `Nat.totient_mul_prod_primeFactors`.
* `Ideal.card_units_quotient_eq_absNorm_mul_prod`: `#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∈ S} (1 - (N 𝔭)⁻¹)`
  in any field of characteristic zero, the analogue of `Nat.totient_eq_mul_prod_factors`.
-/

public section

open IsDedekindDomain

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Infinite R]

/-- The units of `R ⧸ P ^ e` for a maximal ideal `P` and `e ≠ 0`:
`#(R ⧸ P ^ e)ˣ · N P = N (P ^ e) · (N P - 1)`. -/
private theorem card_units_quotient_pow_mul_absNorm (P : Ideal R) [P.IsMaximal] {e : ℕ}
    (he : e ≠ 0) [Finite (R ⧸ P ^ e)] :
    Nat.card (R ⧸ P ^ e)ˣ * absNorm P = absNorm (P ^ e) * (absNorm P - 1) := by
  classical
  let f : R ⧸ P ^ e →+* R ⧸ P := Ideal.Quotient.factor (Ideal.pow_le_self he)
  have hunit (x : R ⧸ P ^ e) : IsUnit x ↔ ¬ f x = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.isUnit_mk_pow_iff_notMem P he]
    simp [f, Ideal.Quotient.eq_zero_iff_mem]
  have hA : Nat.card (R ⧸ P ^ e) = Nat.card (R ⧸ P) * Nat.card f.toAddMonoidHom.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.toAddMonoidHom.ker]
    exact congrArg (· * _) (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
      f.toAddMonoidHom (Ideal.Quotient.factor_surjective (pow_le_self he))).toEquiv)
  have hU : Nat.card (R ⧸ P ^ e)ˣ + Nat.card f.toAddMonoidHom.ker = Nat.card (R ⧸ P ^ e) := by
    rw [Nat.card_congr (Equiv.sumCompl fun x : R ⧸ P ^ e ↦ IsUnit x).symm, Nat.card_sum,
      Nat.card_congr (Submonoid.unitsTypeEquivIsUnitSubmonoid (M := R ⧸ P ^ e)).toEquiv]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight (p := (· ∈ f.toAddMonoidHom.ker))
      (q := fun x ↦ ¬ IsUnit x) fun x ↦ by simp [hunit])
  change Nat.card (R ⧸ P ^ e)ˣ * Nat.card (R ⧸ P) =
    Nat.card (R ⧸ P ^ e) * (Nat.card (R ⧸ P) - 1)
  rw [hA] at hU ⊢
  have hu : Nat.card (R ⧸ P ^ e)ˣ = Nat.card f.toAddMonoidHom.ker * (Nat.card (R ⧸ P) - 1) := by
    rw [Nat.mul_sub_one, mul_comm]
    omega
  rw [hu]
  ring

/-- **Euler's totient for ideals**, multiplicative form: if `S` is the set of height-one primes
dividing `I` and `R ⧸ I` is finite, then `#(R ⧸ I)ˣ · ∏_{𝔭 ∈ S} N 𝔭 = N I · ∏_{𝔭 ∈ S} (N 𝔭 - 1)`.
This is the analogue of `Nat.totient_mul_prod_primeFactors`. -/
theorem card_units_quotient_mul_prod_absNorm (I : Ideal R) [Finite (R ⧸ I)]
    {S : Finset (HeightOneSpectrum R)} (hS : ∀ v, v ∈ S ↔ v.asIdeal ∣ I) :
    Nat.card (R ⧸ I)ˣ * ∏ v ∈ S, absNorm v.asIdeal =
      absNorm I * ∏ v ∈ S, (absNorm v.asIdeal - 1) := by
  classical
  have hI : I ≠ 0 := fun h ↦ (absNorm_ne_zero_iff I).mpr ‹_› (by rw [h, map_zero])
  set e : HeightOneSpectrum R → ℕ := fun v ↦
    (Associates.mk v.asIdeal).count (Associates.mk I).factors
  have he (v : HeightOneSpectrum R) : e v ≠ 0 ↔ v ∈ S := by
    rw [hS, Associates.count_ne_zero_iff_dvd hI v.irreducible]
  have hprod : ∏ v ∈ S, v.asIdeal ^ e v = I := by
    rw [← finprod_eq_finsetProd_of_mulSupport_subset (fun v ↦ v.asIdeal ^ e v) fun v hv ↦
      (he v).mp fun h ↦ hv (by simp [h])]
    exact Ideal.finprod_heightOneSpectrum_factorization hI
  let φ := HeightOneSpectrum.quotientEquivPiOfProdEq I (fun v : S ↦ (v : HeightOneSpectrum R))
    (fun v ↦ e v) Subtype.coe_injective.pairwise_ne
    (by rw [Finset.prod_coe_sort S fun v ↦ v.asIdeal ^ e v]; exact hprod)
  have hU : Nat.card (R ⧸ I)ˣ = ∏ v ∈ S, Nat.card (R ⧸ v.asIdeal ^ e v)ˣ := by
    rw [Nat.card_congr ((Units.mapEquiv φ.toMulEquiv).trans MulEquiv.piUnits).toEquiv,
      Nat.card_pi, Finset.prod_coe_sort S fun v ↦ Nat.card (R ⧸ v.asIdeal ^ e v)ˣ]
  have hN : absNorm I = ∏ v ∈ S, absNorm (v.asIdeal ^ e v) := by
    rw [← map_prod, hprod]
  rw [hU, hN, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v hv ↦ ?_
  have : Finite (R ⧸ v.asIdeal ^ e v) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective (Ideal.le_of_dvd
      (hprod ▸ Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum R ↦ v.asIdeal ^ e v) hv)))
  exact card_units_quotient_pow_mul_absNorm v.asIdeal ((he v).mpr hv)

/-- **Euler's totient for ideals**: if `S` is the set of height-one primes dividing `I` and
`R ⧸ I` is finite, then `#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∈ S} (1 - (N 𝔭)⁻¹)` in any field of
characteristic zero. This is the analogue of `Nat.totient_eq_mul_prod_factors`. -/
theorem card_units_quotient_eq_absNorm_mul_prod {F : Type*} [Field F] [CharZero F]
    (I : Ideal R) [Finite (R ⧸ I)] {S : Finset (HeightOneSpectrum R)}
    (hS : ∀ v, v ∈ S ↔ v.asIdeal ∣ I) :
    (Nat.card (R ⧸ I)ˣ : F) = absNorm I * ∏ v ∈ S, (1 - (absNorm v.asIdeal : F)⁻¹) := by
  have hN (v) (hv : v ∈ S) : absNorm v.asIdeal ≠ 0 := by
    rw [absNorm_ne_zero_iff]
    exact Finite.of_surjective _
      (Ideal.Quotient.factor_surjective (Ideal.le_of_dvd ((hS v).mp hv)))
  have h := congrArg (Nat.cast (R := F)) (card_units_quotient_mul_prod_absNorm I hS)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod, Finset.prod_congr rfl
    fun v hv ↦ Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (hN v hv))] at h
  have hprod : ∏ v ∈ S, (1 - (absNorm v.asIdeal : F)⁻¹) =
      (∏ v ∈ S, ((absNorm v.asIdeal : F) - 1)) / ∏ v ∈ S, (absNorm v.asIdeal : F) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun v hv ↦ ?_
    have : (absNorm v.asIdeal : F) ≠ 0 := Nat.cast_ne_zero.mpr (hN v hv)
    field_simp
  rw [hprod, ← mul_div_assoc, eq_div_iff (Finset.prod_ne_zero_iff.mpr fun v hv ↦
    Nat.cast_ne_zero.mpr (hN v hv)), h, Nat.cast_one]

end Ideal
