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

The mechanism is linear disjointness rather than a direct irreducibility argument. Inside `M`,
the two subfields `ℚ(ζ)` and (the image of) `K` have coprime discriminants, so Mathlib's
`NumberField.linearDisjoint_of_isGalois_isCoprime_discr` makes them linearly disjoint; their
compositum is `M`, so the degree of `M` over `K` equals the degree of `ℚ(ζ)` over `ℚ`, which is
`φ m`. Coprimality of the discriminants is where the hypothesis is spent, via the divisibility
input below.

The same disjointness carries the discriminant: `|discr M|` is a product of powers of
`|discr ℚ(ζ)|` and `|discr K|`, so a prime ramifying in `M` ramifies in `K` or divides `m`. Both
results therefore share one construction, extracted as a private lemma rather than repeated.

## Main results

* `IsCyclotomicExtension.Rat.prime_dvd_of_dvd_natAbs_discr`: a prime dividing the discriminant
  of an `m`-th cyclotomic field divides `m`. This is the divisibility input that turns
  coprimality to `m` into coprimality of discriminants.
* `IsCyclotomicExtension.finrank_eq_totient`: the degree identity `[M : K] = φ m`.
* `IsCyclotomicExtension.prime_dvd_natAbs_discr`: a prime dividing `discr M` divides `discr K`
  or divides `m` — the extension ramifies only below or at the level.

## Implementation notes

The hypothesis is `((NumberField.discr K).natAbs).Coprime m`, a statement about the *base*
field. It is the condition an arithmetic caller can actually arrange — e.g. by choosing `m` to
be a prime unramified in `K` — whereas the resulting intersection or irreducibility conditions
would have to be re-derived from it at each use.

`finrank_eq_totient` asks only the base `K` to be a number field: `M` is finite over `K` by
`IsCyclotomicExtension.finiteDimensional`, hence a number field on its own, so demanding
`[NumberField M]` there would be an avoidable hypothesis. `prime_dvd_natAbs_discr` cannot make
that economy, because its statement names `discr M`, which does not elaborate without the
instance; it therefore takes `[NumberField M]`, and a caller holding only `[NumberField K]`
supplies it exactly as `finrank_eq_totient` does internally. The degree itself comes from
linear disjointness of `ℚ(ζ)` and the image of `K` inside `M`, whose compositum is `M`.

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

/-- **The linear-disjointness setup**, shared by the degree identity and the ramification
dichotomy below. Inside `M` sit `K₁ = ℚ(ζ)` and `K₂`, the image of `K`; they have coprime
discriminants, so they are linearly disjoint, and they generate `M`.

Private, and stated as an existential rather than as a definition, because its only role is to
be destructured by the two theorems that follow: nothing downstream needs to name `K₁` or `K₂`,
and packaging them as data would expose a choice of primitive root that neither consumer makes. -/
private theorem exists_adjoin_linearDisjoint (K M : Type*) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M]
    (hcop : ((NumberField.discr K).natAbs).Coprime m) :
    ∃ K₁ K₂ : IntermediateField ℚ M, IsCyclotomicExtension {m} ℚ K₁ ∧ K₁ ⊔ K₂ = ⊤ ∧
      K₁.LinearDisjoint K₂ ∧ NumberField.discr K₂ = NumberField.discr K ∧
        IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) ∧
          Module.finrank K M = Module.finrank K₂ M := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) K M
    (Set.mem_singleton m) (NeZero.ne m)
  set K₁ : IntermediateField ℚ M := IntermediateField.adjoin ℚ {ζ}
  set K₂ : IntermediateField ℚ M := (IsScalarTower.toAlgHom ℚ K M).fieldRange
  have : IsCyclotomicExtension {m} ℚ K₁ :=
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
  exact ⟨K₁, K₂, ‹IsCyclotomicExtension {m} ℚ K₁›, hsup, hld, hdiscrK₂, hcoprime, hrelabel⟩

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
  obtain ⟨K₁, K₂, hcyc, hsup, hld, -, -, hrelabel⟩ := exists_adjoin_linearDisjoint K M m hcop
  have hfinK₁ : Module.finrank ℚ K₁ = m.totient :=
    IsCyclotomicExtension.finrank K₁ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  rw [hrelabel, hld.finrank_right_eq_finrank hsup, hfinK₁]

/-- **A prime ramifying in a cyclotomic extension either ramifies below or divides the level.**
For `M / K` an `m`-th cyclotomic extension of a number field with `m` coprime to `discr K`, a
prime dividing `discr M` divides `discr K` or divides `m`.

The two cases are the two factors of `M`: inside `M` the subfields `ℚ(ζ)` and `K` are linearly
disjoint and generate `M`, so `|discr M|` is a product of powers of `|discr ℚ(ζ)|` and
`|discr K|`, and a prime dividing the first divides `m`.

Unlike `finrank_eq_totient`, this does carry `[NumberField M]`: the statement names `discr M`,
which is not defined without it. It is not a real restriction — a cyclotomic extension of a
number field is one — but it cannot be left to the proof. A caller holding only `[NumberField K]`
gets the instance from `IsCyclotomicExtension.numberField {m} K M`, which is how
`finrank_eq_totient` obtains it internally. -/
theorem prime_dvd_natAbs_discr (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M]
    (hcop : ((NumberField.discr K).natAbs).Coprime m) {p : ℕ} (hp : p.Prime)
    (hpM : p ∣ (NumberField.discr M).natAbs) : p ∣ (NumberField.discr K).natAbs ∨ p ∣ m := by
  obtain ⟨K₁, K₂, hcyc, hsup, hld, hdiscrK₂, hcoprime, -⟩ :=
    exists_adjoin_linearDisjoint K M m hcop
  -- `|discr M|` factors along the linearly disjoint pair.
  rw [NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow (L := M) K₁ K₂ hld hsup
    (NumberField.isCoprime_differentIdeal_of_isCoprime_discr M hcoprime)] at hpM
  rcases (Nat.Prime.dvd_mul hp).mp hpM with h | h
  · exact Or.inr (Rat.prime_dvd_of_dvd_natAbs_discr K₁ m hp (hp.dvd_of_dvd_pow h))
  · exact Or.inl (hdiscrK₂ ▸ hp.dvd_of_dvd_pow h)

end IsCyclotomicExtension
