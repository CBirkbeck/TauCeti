/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop

/-!
# The degree and the ramified primes of a cyclotomic extension of a number field

Mathlib computes the degree of an `m`-th cyclotomic extension either over `ℚ`
(`IsCyclotomicExtension.Rat.finrank`) or over a base for which the `m`-th cyclotomic polynomial
is already known to be irreducible (`IsCyclotomicExtension.finrank`). Neither is directly usable
over a general number field `K`, where irreducibility of `Φ_m` over `K` is exactly what has to be
established.

This file supplies the arithmetic criterion: if `m` is coprime to the discriminant of `K`, then

`[M : K] = φ m`   for `M / K` an `m`-th cyclotomic extension with `K` a number field.

The degree comes from linear disjointness rather than a direct irreducibility argument. Inside
`M`, the two subfields `ℚ(ζ)` and (the image of) `K` have coprime discriminants, so Mathlib's
`NumberField.linearDisjoint_of_isGalois_isCoprime_discr` makes them linearly disjoint; their
compositum is `M`, so the degree of `M` over `K` equals the degree of `ℚ(ζ)` over `ℚ`, which is
`φ m`. Coprimality of the discriminants is where the hypothesis is spent, via the divisibility
input below.

The ramified primes need no hypothesis at all, and go by another route entirely: the different
ideal of the tower `ℤ → 𝓞 K → 𝓞 M`. Transitivity of the different factors `𝔡(𝓞 M / ℤ)` as
`𝔡(𝓞 M / 𝓞 K)` times the extension of `𝔡(𝓞 K / ℤ)` to `𝓞 M`. Since `M = K(ζ)` with `ζ` a root of
`X ^ m - 1`, the first factor contains `m`; so a prime of `𝓞 M` over a rational prime dividing
neither `m` nor `discr K` divides neither factor, and is therefore unramified.

## Main results

* `IsCyclotomicExtension.Rat.prime_dvd_of_dvd_natAbs_discr`: a prime dividing the discriminant
  of an `m`-th cyclotomic field divides `m`. This is the divisibility input that turns
  coprimality to `m` into coprimality of discriminants.
* `IsCyclotomicExtension.finrank_eq_totient`: the degree identity `[M : K] = φ m`.
* `IsCyclotomicExtension.natCast_mem_differentIdeal`: the level `m` lies in the different ideal
  of `𝓞 M` over `𝓞 K`.
* `IsCyclotomicExtension.prime_dvd_natAbs_discr`: a prime dividing `discr M` divides `discr K`
  or divides `m` — the extension ramifies only below or at the level.

## Implementation notes

The hypothesis `((NumberField.discr K).natAbs).Coprime m` of `finrank_eq_totient` is a statement
about the *base* field. It is the condition an arithmetic caller can actually arrange — e.g. by
choosing `m` to be a prime unramified in `K` — whereas the resulting intersection or
irreducibility conditions would have to be re-derived from it at each use. Some hypothesis of the
kind is unavoidable there: `[M : K] = φ m` fails outright when `K` already contains a primitive
`m`-th root of unity. The ramification statement needs none, and carries none.

`finrank_eq_totient` asks only the base `K` to be a number field: a cyclotomic extension of a
number field is again one, by `IsCyclotomicExtension.numberField`, so demanding `[NumberField M]`
there would be an avoidable hypothesis. `prime_dvd_natAbs_discr` cannot make that economy, because
its statement names `discr M`, which does not elaborate without the instance; it therefore takes
`[NumberField M]`, and a caller holding only `[NumberField K]` supplies it exactly as
`finrank_eq_totient` does internally.

Adapted from the Birkbeck–Brasca Chebotarev density project.
-/

public section

namespace IsCyclotomicExtension

namespace Rat

/-- A prime dividing the discriminant of an `m`-th cyclotomic extension of `ℚ` divides `m`. -/
theorem prime_dvd_of_dvd_natAbs_discr (E : Type*) [Field E] [NumberField E] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} ℚ E] {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ (NumberField.discr E).natAbs) : p ∣ m := by
  refine hp.dvd_of_dvd_pow (n := m.totient) (hpd.trans ?_)
  obtain ⟨c, hc⟩ := Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos m)
  rw [IsCyclotomicExtension.Rat.natAbs_discr (K := E) (n := m), hc,
    Nat.mul_div_cancel_left _ (Finset.prod_pos fun q hq ↦
      pow_pos (Nat.prime_of_mem_primeFactors hq).pos _)]
  exact dvd_mul_left _ _

end Rat

-- **The linear-disjointness setup** behind the degree identity. Inside `M` sit `K₁ = ℚ(ζ)` and
-- `K₂`, the image of `K`; they have coprime discriminants, so they are linearly disjoint, and
-- they generate `M`.
--
-- Stated as an existential rather than as a definition because its only role is to be
-- destructured by `finrank_eq_totient`: nothing downstream needs to name `K₁` or `K₂`, and
-- packaging them as data would expose a choice of primitive root that the consumer does not make.
private theorem exists_adjoin_linearDisjoint (K M : Type*) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M]
    (hcop : ((NumberField.discr K).natAbs).Coprime m) :
    ∃ K₁ K₂ : IntermediateField ℚ M, IsCyclotomicExtension {m} ℚ K₁ ∧ K₁ ⊔ K₂ = ⊤ ∧
      K₁.LinearDisjoint K₂ ∧ Module.finrank K M = Module.finrank K₂ M := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) K M
    (Set.mem_singleton m) (NeZero.ne m)
  set K₁ : IntermediateField ℚ M := IntermediateField.adjoin ℚ {ζ}
  set K₂ : IntermediateField ℚ M := (IsScalarTower.toAlgHom ℚ K M).fieldRange
  have hcyc : IsCyclotomicExtension {m} ℚ K₁ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ)
  have : IsGalois ℚ K₁ := IsCyclotomicExtension.isGalois (S := {m}) (K := ℚ) (L := K₁)
  have hsup : K₁ ⊔ K₂ = ⊤ :=
    TauCeti.IntermediateField.adjoin_sup_fieldRange_eq_top ℚ K M
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ)
  let eK₂ : K ≃+* K₂ := ((IsScalarTower.toAlgHom ℚ K M : K →+* M)).rangeRestrictFieldEquiv
  have hdiscrK₂ : NumberField.discr K₂ = NumberField.discr K :=
    (NumberField.discr_eq_discr_of_ringEquiv (f := eK₂)).symm
  have hcoprime : IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) := by
    rw [hdiscrK₂, Int.isCoprime_iff_gcd_eq_one, Int.gcd]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    rw [Nat.dvd_gcd_iff] at hpdvd
    obtain ⟨hpa, hpb⟩ := hpdvd
    have hpm : p ∣ m := Rat.prime_dvd_of_dvd_natAbs_discr K₁ m hp hpa
    have hpgcd : p ∣ Nat.gcd (NumberField.discr K).natAbs m := Nat.dvd_gcd hpb hpm
    rw [hcop] at hpgcd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpgcd)
  have hld : K₁.LinearDisjoint K₂ :=
    NumberField.linearDisjoint_of_isGalois_isCoprime_discr (L := M) K₁ K₂ hcoprime
  have hrelabel : Module.finrank K M = Module.finrank K₂ M := by
    refine Algebra.finrank_eq_of_equiv_equiv eK₂ (RingEquiv.refl M) ?_
    ext x
    -- `eK₂` is the embedding `K → M` with its range restricted, so coercing back to `M` returns
    -- that embedding: `RingHom.rangeRestrictFieldEquiv_apply_coe`.
    exact RingHom.rangeRestrictFieldEquiv_apply_coe _ x
  exact ⟨K₁, K₂, hcyc, hsup, hld, hrelabel⟩

/-- **The cyclotomic degree over a number field base.** If `M / K` is an `m`-th cyclotomic
extension with `K` a number field and `m` coprime to `discr K`, then `[M : K] = φ m`.

Coprimality to `discr K` stands in for irreducibility of `Φ_m` over `K`, and is the hypothesis
an arithmetic caller can arrange directly. Only the base `K` need be a number field. -/
theorem finrank_eq_totient (K M : Type*) [Field K] [NumberField K] [Field M]
    [Algebra K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M]
    (hcop : ((NumberField.discr K).natAbs).Coprime m) :
    Module.finrank K M = m.totient := by
  -- `M` is a number field rather than assumed one: a cyclotomic extension of a number field is
  -- again a number field.
  have : NumberField M := IsCyclotomicExtension.numberField {m} K M
  obtain ⟨K₁, K₂, hcyc, hsup, hld, hrelabel⟩ := exists_adjoin_linearDisjoint K M m hcop
  have hfinK₁ : Module.finrank ℚ K₁ = m.totient :=
    IsCyclotomicExtension.finrank K₁ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  rw [hrelabel, hld.finrank_right_eq_finrank hsup, hfinK₁]

open NumberField Polynomial in
/-- **The level lies in the different ideal.** For `M / K` an `m`-th cyclotomic extension of
number fields, `m` belongs to the different ideal of `𝓞 M` over `𝓞 K`; equivalently that different
divides `(m)`, so only primes dividing `m` can ramify in `M / K`.

Stated as a membership rather than as a divisibility of `Ideal.span {(m : 𝓞 M)}`: that is the
form Mathlib's `aeval_derivative_mem_differentIdeal` produces, and the form a consumer feeds to
an `Ideal.dvd_iff_le` bound on the different; `Ideal.span_singleton_le_iff_mem` recovers the
divisibility reading where that is the one wanted. -/
theorem natCast_mem_differentIdeal (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M] :
    (m : 𝓞 M) ∈ differentIdeal (𝓞 K) (𝓞 M) := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) K M
    (Set.mem_singleton m) (NeZero.ne m)
  set z : 𝓞 M := hζ.toInteger
  -- `M = K(ζ)` is generated over `K` by a primitive `m`-th root of unity, so the different
  -- contains the element `aeval ζ (derivative (minpoly (𝓞 K) ζ))`.
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 K) K M z
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ)
  have hzpow : z ^ m = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  -- `ζ` is a root of `X ^ m - 1`, so its minimal polynomial divides that.
  obtain ⟨q, hq⟩ : minpoly (𝓞 K) z ∣ (X ^ m - 1 : (𝓞 K)[X]) :=
    minpoly.isIntegrallyClosed_dvd (Algebra.IsIntegral.isIntegral z) (by simp [hzpow])
  -- Differentiating that factorisation at `ζ` makes `m * ζ ^ (m - 1)` a multiple of `hmem`.
  have hder : aeval z (derivative (X ^ m - 1 : (𝓞 K)[X])) =
      aeval z (derivative (minpoly (𝓞 K) z)) * aeval z q := by
    rw [hq, derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero]
  rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, map_mul, map_pow, aeval_C,
    aeval_X] at hder
  -- Multiplying by `ζ` and using `ζ ^ m = 1` turns `m * ζ ^ (m - 1)` into `m` itself.
  have hm : (m : 𝓞 M) = aeval z (derivative (minpoly (𝓞 K) z)) * aeval z q * z := by
    rw [← hder, mul_assoc, ← pow_succ, Nat.sub_add_cancel (NeZero.pos m), hzpow, mul_one,
      map_natCast]
  rw [hm]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hmem)

open NumberField in
/-- **A prime ramifying in a cyclotomic extension either ramifies below or divides the level.**
For `M / K` an `m`-th cyclotomic extension of a number field, a prime dividing `discr M` divides
`discr K` or divides `m`.

Unlike `finrank_eq_totient`, this does carry `[NumberField M]`: the statement names `discr M`,
which is not defined without it. It is not a real restriction — a cyclotomic extension of a
number field is one — but it cannot be left to the proof. A caller holding only `[NumberField K]`
gets the instance from `IsCyclotomicExtension.numberField {m} K M`, which is how
`finrank_eq_totient` obtains it internally. -/
theorem prime_dvd_natAbs_discr (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M] {p : ℕ} (hp : p.Prime)
    (hpM : p ∣ (NumberField.discr M).natAbs) : p ∣ (NumberField.discr K).natAbs ∨ p ∣ m := by
  by_cases hdm : p ∣ m
  · exact Or.inr hdm
  refine Or.inl ?_
  by_contra hdK
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hKZ : ¬ (p : ℤ) ∣ NumberField.discr K := fun h ↦
    hdK (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h))
  -- It suffices to show every prime of `𝓞 M` above `p` is unramified over `ℤ`.
  refine (NumberField.not_dvd_discr_iff_forall_mem M (𝓞 M) hpZ).mpr ?_
    (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpM))
  intro P hP hpP
  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  -- Transitivity splits `𝔡(𝓞 M / ℤ)` into `𝔡(𝓞 M / 𝓞 K)` times the extension of `𝔡(𝓞 K / ℤ)`,
  -- so the prime `P` must divide one of the two factors.
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 M),
    Ideal.dvd_iff_le] at hdvd
  rcases hP.mul_le.mp hdvd with h | h
  · -- `P` contains both `m`, via the different of `𝓞 M / 𝓞 K`, and `p`; they are coprime.
    obtain ⟨a, b, hab⟩ : IsCoprime ((p : ℤ) : 𝓞 M) ((m : ℕ) : 𝓞 M) := by
      simpa using (Nat.isCoprime_iff_coprime.mpr
        (hp.coprime_iff_not_dvd.mpr hdm)).map (algebraMap ℤ (𝓞 M))
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr (hab ▸ P.add_mem (P.mul_mem_left a hpP)
      (P.mul_mem_left b (h (natCast_mem_differentIdeal K M m)))))
  · -- `P ∩ 𝓞 K` lies above `p`, hence is unramified over `ℤ`, hence misses `𝔡(𝓞 K / ℤ)`.
    have hpQ : ((p : ℤ) : 𝓞 K) ∈ P.comap (algebraMap (𝓞 K) (𝓞 M)) := by
      simpa [Ideal.mem_comap] using hpP
    exact not_dvd_differentIdeal_iff.mpr
        ((NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) hpZ).mp hKZ _
          (Ideal.IsPrime.comap _) hpQ)
      (Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mp h))

end IsCyclotomicExtension
