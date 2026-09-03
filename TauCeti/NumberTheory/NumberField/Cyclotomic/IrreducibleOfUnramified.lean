/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Ideal.GoingUp
public import TauCeti.NumberTheory.Cyclotomic.Irreducible
public import TauCeti.NumberTheory.RamificationInertia.Tower

/-!
# Unramifiedness makes the cyclotomic polynomial irreducible over a number field

Let `K` be a number field and `p` a prime that is unramified in `K`. Then the cyclotomic polynomial
`Φ_{p^(k+1)}` is irreducible over `K` for every `k`; in particular `Φ_p` is, so
`[K(ζ_p) : K] = p - 1` and the Galois group of `K(ζ_p) / K` is the full unit group `(ℤ/pℤ)ˣ`, of
order `p - 1`.

The mechanism is ramification, not an intersection of fields. Let `F / K` be a `p^(k+1)`-th
cyclotomic extension and `𝔔` a prime of `𝓞 F` above `p`. Inside `F` the subfield `ℚ(ζ)` is the
`p^(k+1)`-th cyclotomic field over `ℚ`, in which `p` is totally ramified with index
`φ(p^(k+1))`; ramification indices multiply in towers, so `e(𝔔 / p) ≥ φ(p^(k+1))`. On the other
hand `e(𝔔 / p) = e(𝔔 / 𝔮) · e(𝔮 / p)` with `𝔮 = 𝔔 ∩ 𝓞 K`, and `e(𝔮 / p) = 1` because `p` is
unramified in `K`. Hence `e(𝔔 / 𝔮) ≥ φ(p^(k+1))`, while `e(𝔔 / 𝔮) ≤ [F : K]`. So
`[F : K] ≥ φ(p^(k+1))`, which is irreducibility of `Φ_{p^(k+1)}` over `K` by
`IsCyclotomicExtension.irreducible_cyclotomic_of_totient_le_finrank`.

The intersection `L ⊓ K(ζ_p) = ⊥` for an extension `L / K` gives none of this: it constrains `L`,
whereas `[K(ζ_p) : K]` is a proper divisor of `p - 1` exactly when `K ∩ ℚ(ζ_p) ≠ ℚ`. The witness
`K = ℚ(√5)`, `p = 5` is `Polynomial.not_irreducible_cyclotomic_five_of_sq_eq_five`.

## Main results

* `IsCyclotomicExtension.totient_le_finrank_of_unramified`: `φ(p^(k+1)) ≤ [F : K]` when `p` is
  unramified in `K`.
* `IsCyclotomicExtension.irreducible_cyclotomic_prime_pow_of_unramified`: `Φ_{p^(k+1)}` is
  irreducible over `K` when `p` is unramified in `K`.
* `IsCyclotomicExtension.irreducible_cyclotomic_of_unramified`: the prime case, in the shape the
  Chebotarev roadmap pins for its auxiliary prime.
* `IsCyclotomicExtension.card_auxiliaryCyclotomic`: the Galois group of a `q`-th cyclotomic
  extension with `Φ_q` irreducible has exactly `q - 1` elements.

## References

Layer 7.2 of the Chebotarev roadmap (`TauCetiRoadmap/Chebotarev/README.md`), whose stated proof
this file follows. Total ramification of `ℚ(ζ_{p^r})` at `p` is Milne, *Algebraic Number Theory*,
Proposition 6.2, and Sharifi, *Algebraic Number Theory*, Lemma 3.1.13; the ramification bookkeeping
is Sharifi, Remark 2.5.7 and Theorem 2.5.11. The argument mirrors
`TauCeti.Multiquadratic.ramificationIdx_eq_two_of_liesOver_primeDiscriminantPrime`.
-/

public section

open Polynomial
open scoped NumberField

namespace IsCyclotomicExtension

variable {K : Type*} [Field K] [NumberField K]

private theorem totient_le_ramificationIdx_int (p k : ℕ) [Fact p.Prime] {F : Type*} [Field F]
    [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime]
    [𝔔.LiesOver (Ideal.span {(p : ℤ)})] : (p ^ (k + 1)).totient ≤ 𝔔.ramificationIdx ℤ := by
  -- `p` is totally ramified in `ℚ(ζ)`: Milne, Prop. 6.2(c) (`(p) = (π)^e` with `e = φ(p^r)`);
  -- Sharifi, Lemma 3.1.13 ("It is totally ramified").
  have : IsCyclotomicExtension {p ^ (k + 1)} ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  -- Indices multiply in towers: Sharifi, Remark 2.5.7 ("`e_{P/p} = e_{P/𝔓} e_{𝔓/p}`").
  have h := (𝔔.under (𝓞 (IntermediateField.adjoin ℚ {ζ}))).ramificationIdx_below_le (R := ℤ) 𝔔
  rwa [Rat.ramificationIdx_eq_of_prime_pow p k, ← Nat.totient_prime_pow_succ Fact.out] at h

private theorem ramificationIdx_under_eq_one (p : ℕ) {F : Type*} [Field F] [Algebra K F]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
    Algebra.IsUnramifiedAt ℤ 𝔮) (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime] [𝔔.LiesOver (Ideal.span {(p : ℤ)})] :
    (𝔔.under (𝓞 K)).ramificationIdx ℤ = 1 :=
  -- Roadmap README Layer 7.2, "From `q` unramified in `K`": `𝔮 = 𝔔 ∩ 𝓞 K` is unramified over `ℤ`.
  Ideal.ramificationIdx_eq_one_iff.mpr (hur _)

private theorem totient_le_ramificationIdx (p k : ℕ) [Fact p.Prime] {F : Type*} [Field F]
    [NumberField F] [Algebra K F] [IsCyclotomicExtension {p ^ (k + 1)} K F]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
    Algebra.IsUnramifiedAt ℤ 𝔮) (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime] [𝔔.LiesOver (Ideal.span {(p : ℤ)})] :
    (p ^ (k + 1)).totient ≤ 𝔔.ramificationIdx (𝓞 K) := by
  -- First tower `ℤ ⊆ 𝓞 ℚ(ζ) ⊆ 𝓞 F`, through a primitive root: `e(𝔔 / p) ≥ φ(p^(k+1))`.
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (S := {p ^ (k + 1)}) K F
    (Set.mem_singleton _) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  -- Second tower `ℤ ⊆ 𝓞 K ⊆ 𝓞 F`: indices multiply (Sharifi, Remark 2.5.7) and `e(𝔮 / p) = 1`
  -- because `p` is unramified in `K` (roadmap README Layer 7.2), so `e(𝔔 / p) = e(𝔔 / 𝔮)`.
  simpa only [Ideal.ramificationIdx_tower (R := ℤ) (𝔔.under (𝓞 K)) 𝔔,
    ramificationIdx_under_eq_one p hur 𝔔, one_mul] using
    totient_le_ramificationIdx_int p k hζ 𝔔

private theorem ramificationIdx_le_finrank_of_isPrime {F : Type*} [Field F] [NumberField F]
    [Algebra K F] (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime] : 𝔔.ramificationIdx (𝓞 K) ≤ Module.finrank K F :=
  -- The fundamental identity `∑ eᵢ fᵢ = [F : K]` bounds each `eᵢ`, and `[𝓞 F : 𝓞 K] = [F : K]`:
  -- Sharifi, Theorem 2.5.11 ("`∑ eᵢ fᵢ = [L : K]`"); Milne, Theorem 3.34.
  (TauCeti.RamificationInertia.ramificationIdx_le_finrank (𝔔.under (𝓞 K)) 𝔔).trans_eq
    (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 F) F).symm

/-- **The degree of a cyclotomic extension above an unramified prime is at least `φ(p^(k+1))`.**
This is the total ramification of `K(ζ_{p^(k+1)}) / K` above `p` that Layer 7.3 of the Chebotarev
roadmap consumes. Unlike `IsPrimitiveRoot.lcm_totient_le_finrank` it assumes no irreducibility, so
it can feed `irreducible_cyclotomic_of_totient_le_finrank` rather than follow from it.

Source: Sharifi, Theorem 2.5.11 (`∑ eᵢ fᵢ = [L : K]`); Milne, Theorem 3.34; roadmap README
Layer 7.3 ("by 7.2 the extension `K(ζ_q)/K` is totally ramified at every prime above `q`"). -/
theorem totient_le_finrank_of_unramified (p k : ℕ) [Fact p.Prime] (F : Type*) [Field F]
    [Algebra K F] [IsCyclotomicExtension {p ^ (k + 1)} K F]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮) : (p ^ (k + 1)).totient ≤ Module.finrank K F := by
  have : FiniteDimensional K F := finiteDimensional {p ^ (k + 1)} K F
  have : NumberField F := .of_module_finite K F
  -- A prime of `𝓞 F` above `p`: Sharifi, Thm 2.5.11 (`pB = P₁^{e₁} ⋯ P_g^{e_g}` with `g ≥ 1`).
  obtain ⟨𝔔, _, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (Ideal.span {(p : ℤ)})
    (S := 𝓞 F)
  -- `𝔔` has relative ramification index at least `φ(p^(k+1))` over `𝓞 K`, and a ramification
  -- index never exceeds the degree of the extension.
  exact (totient_le_ramificationIdx p k hur 𝔔).trans (ramificationIdx_le_finrank_of_isPrime 𝔔)

variable (K) in
/-- **Unramifiedness gives irreducibility of `Φ_{p^(k+1)}`.** If the prime `p` is unramified in the
number field `K`, then the `p^(k+1)`-th cyclotomic polynomial is irreducible over `K`.

`hur` is definitionally Mathlib's `Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})`, so a proof
of that predicate can be passed directly; the bundled `Algebra.Unramified ℤ (𝓞 K)` is far stronger,
and forces `K = ℚ` by `NumberField.finrank_eq_one_of_unramified`. Unramifiedness is sufficient but
not necessary: irreducibility holds exactly when `K ∩ ℚ(ζ_{p^(k+1)}) = ℚ`. For `k = 0` see
`irreducible_cyclotomic_of_unramified`.

Source: roadmap README Layer 7.2, steps 1–3; Milne, Prop. 6.2 and Sharifi, Lemma 3.1.13 for the
base `ℚ`. -/
theorem irreducible_cyclotomic_prime_pow_of_unramified (p k : ℕ) [Fact p.Prime]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮) : Irreducible (cyclotomic (p ^ (k + 1)) K) :=
  -- `p` unramified in `K` forces the canonical `p^(k+1)`-th cyclotomic extension of `K` to have
  -- degree at least `φ(p^(k+1))`, the full degree of `Φ_{p^(k+1)}`.
  irreducible_cyclotomic_of_totient_le_finrank K (CyclotomicField (p ^ (k + 1)) K) <|
    totient_le_finrank_of_unramified p k _ hur

variable (K) in
/-- **Layer 7.2, the degree input the crossing actually needs.** If the prime `q` is unramified in
the number field `K`, then the `q`-th cyclotomic polynomial is irreducible over `K`, hence
`[K(ζ_q) : K] = q - 1`.

`hur` is definitionally Mathlib's `Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)})`, so a proof
of that predicate can be passed directly. `L ⊓ K(ζ_q) = ⊥` is no substitute: it constrains `L`, not
`K ∩ ℚ(ζ_q)`, which is what irreducibility is equivalent to. See
`Polynomial.not_irreducible_cyclotomic_five_of_sq_eq_five` for the witness.

Source: roadmap `Suggested.lean`, `irreducible_cyclotomic_of_unramified` (pinned statement); the
case `k = 0` of `irreducible_cyclotomic_prime_pow_of_unramified`. -/
theorem irreducible_cyclotomic_of_unramified (q : ℕ) (hq : q.Prime)
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(q : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮) : Irreducible (cyclotomic q K) := by
  -- The case `k = 0` of the prime-power result, where `q ^ (0 + 1)` reduces to `q`.
  have : Fact q.Prime := ⟨hq⟩
  simpa using irreducible_cyclotomic_prime_pow_of_unramified K q 0 hur

omit [NumberField K] in
variable (K) in
/-- **Layer 7.2, the auxiliary Galois group is the full unit group**, in particular cyclic of order
`q - 1`. If `Φ_q` is irreducible over `K`, a `q`-th cyclotomic extension `F / K` has exactly
`q - 1` automorphisms. The name records its role in the Chebotarev crossing, where `F = K(ζ_q)`
for the auxiliary prime `q`.

`hirr` is what `irreducible_cyclotomic_of_unramified` supplies, and keeping it a hypothesis stops a
crossing argument from silently assuming the order. `q - 1` is truncated `ℕ` subtraction, equal to
`q.totient` here because `q` is prime. For the degree rather than the automorphism count use
Mathlib's `IsCyclotomicExtension.finrank`, and for the isomorphism itself `autEquivPow`.

Source: roadmap `Suggested.lean`, `card_auxiliaryCyclotomic` (pinned statement); roadmap README
Layer 7.2, step 3 ("the cyclotomic character `Gal(K(ζ_q)/K) ≃ (ZMod q)ˣ` is an isomorphism onto
the full unit group, in particular cyclic of order `q - 1`"). -/
theorem card_auxiliaryCyclotomic (q : ℕ) [NeZero q] (F : Type*) [Field F] [Algebra K F]
    [IsCyclotomicExtension {q} K F] (hq : q.Prime) (hirr : Irreducible (cyclotomic q K)) :
    Nat.card (F ≃ₐ[K] F) = q - 1 := by
  -- `(ZMod q)ˣ` has `φ(q) = q - 1` elements, as `q` is prime.
  rw [Nat.card_congr (autEquivPow F hirr).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime hq]

end IsCyclotomicExtension

