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

/-- **A prime of `𝓞 F` above `p` exists.** The prime `(p)` of `ℤ` has at least one prime of the
ring of integers of a number field above it.

Source: Sharifi, Theorem 2.5.11 ("write `pB = P₁^{e₁} ⋯ P_g^{e_g}` for some distinct nonzero prime
ideals `Pᵢ` of `B` and positive integers `eᵢ`, for `1 ≤ i ≤ g` and some `g ≥ 1`"). -/
private theorem exists_isPrime_liesOver (F : Type*) [Field F] [NumberField F] (p : ℕ)
    [Fact p.Prime] :
    ∃ 𝔔 : Ideal (𝓞 F), 𝔔.IsPrime ∧ 𝔔.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero Fact.out)
  have : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hp).mpr (Nat.prime_iff_prime_int.mp Fact.out)
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)})
    (⊥ : Ideal (𝓞 F)) (by
      rw [Ideal.comap_bot_of_injective _ (RingHom.injective_int (algebraMap ℤ (𝓞 F)))]
      exact bot_le)
  exact ⟨Q, hQ, ⟨hQp.symm⟩⟩

/-- **Total ramification of the cyclotomic subfield.** For a primitive `p^(k+1)`-th root of unity
`ζ` in a number field `F` and a prime `𝔔` of `𝓞 F` above `p`, the prime of `ℚ(ζ)` below `𝔔` has
ramification index `φ(p^(k+1)) = p^k (p - 1)` over `ℤ`.

Source: Milne, *Algebraic Number Theory*, Prop. 6.2(c) ("`(p) = (π)^e` with `e = φ(p^r)`");
Sharifi, Lemma 3.1.13 ("It is totally ramified"); Mathlib's
`IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime_pow`. -/
private theorem ramificationIdx_under_adjoin_eq (p k : ℕ) [Fact p.Prime] {F : Type*} [Field F]
    [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (𝔔 : Ideal (𝓞 F))
    [𝔔.IsPrime] [𝔔.LiesOver (Ideal.span {(p : ℤ)})] :
    (𝔔.under (𝓞 (IntermediateField.adjoin ℚ {ζ}))).ramificationIdx ℤ = p ^ k * (p - 1) := by
  have : IsCyclotomicExtension {p ^ (k + 1)} ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime_pow p k _ _

/-- **The absolute ramification index of a prime above `p` is at least `φ(p^(k+1))`.** In the tower
`ℤ ⊆ 𝓞 ℚ(ζ) ⊆ 𝓞 F` the ramification index of `𝔔` over `ℤ` is the product of the index of the prime
of `ℚ(ζ)` below it, which is `φ(p^(k+1))`, and a positive relative index.

Source: Sharifi, Remark 2.5.7 ("`e_{P/p} = e_{P/𝔓} e_{𝔓/p}`"); Milne, Prop. 6.2(c). -/
private theorem totient_le_ramificationIdx_int (p k : ℕ) [Fact p.Prime] {F : Type*} [Field F]
    [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (𝔔 : Ideal (𝓞 F))
    [𝔔.IsPrime] [𝔔.LiesOver (Ideal.span {(p : ℤ)})] :
    (p ^ (k + 1)).totient ≤ 𝔔.ramificationIdx ℤ := by
  rw [Ideal.ramificationIdx_tower (R := ℤ) (𝔔.under (𝓞 (IntermediateField.adjoin ℚ {ζ}))) 𝔔,
    ramificationIdx_under_adjoin_eq p k hζ 𝔔, Nat.totient_prime_pow Fact.out (Nat.succ_pos k),
    Nat.succ_sub_one]
  exact Nat.le_mul_of_pos_right _ (Ideal.ramificationIdx_pos 𝔔 _)

/-- **Above an unramified prime, the prime of `K` below `𝔔` has ramification index one.**

Source: Mathlib, `Algebra.IsUnramifiedIn.ramificationIdx_eq_one` ("For a prime `𝔓` of `S` lying
over an unramified prime `𝔭` of `R`, the ramification index `e(𝔓 ∣ 𝔭)` equals `1`"); roadmap README
Layer 7.2, "From `q` unramified in `K`". -/
private theorem ramificationIdx_under_eq_one (p : ℕ) {F : Type*} [Field F] [Algebra K F]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮)
    (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime] [𝔔.LiesOver (Ideal.span {(p : ℤ)})] :
    (𝔔.under (𝓞 K)).ramificationIdx ℤ = 1 := by
  have hunr : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) :=
    fun 𝔮 h𝔮 hlo ↦ by have := h𝔮; have := hlo; exact hur 𝔮
  exact hunr.ramificationIdx_eq_one (Ideal.under_liesOver_of_liesOver (𝓞 K) 𝔔 _)

/-- **The relative ramification index above an unramified prime is at least `φ(p^(k+1))`.**
Ramification indices multiply in the towers `ℤ ⊆ 𝓞 ℚ(ζ) ⊆ 𝓞 F` and `ℤ ⊆ 𝓞 K ⊆ 𝓞 F`; the first
gives `e(𝔔 / p) ≥ φ(p^(k+1))`, the second `e(𝔔 / p) = e(𝔔 / 𝔮)` since `e(𝔮 / p) = 1`.

Source: Sharifi, Remark 2.5.7 ("ramification indices and residue degrees are multiplicative in
extensions"); roadmap README Layer 7.2, "From `q` unramified in `K`". -/
private theorem totient_le_ramificationIdx (p k : ℕ) [Fact p.Prime] {F : Type*} [Field F]
    [NumberField F] [Algebra K F] [IsCyclotomicExtension {p ^ (k + 1)} K F]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮)
    (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime] [𝔔.LiesOver (Ideal.span {(p : ℤ)})] :
    (p ^ (k + 1)).totient ≤ 𝔔.ramificationIdx (𝓞 K) := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {p ^ (k + 1)}) K F
    (Set.mem_singleton _)
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have h := totient_le_ramificationIdx_int p k hζ 𝔔
  rwa [Ideal.ramificationIdx_tower (R := ℤ) (𝔔.under (𝓞 K)) 𝔔, ramificationIdx_under_eq_one p hur 𝔔,
    one_mul] at h

/-- **A relative ramification index is at most the degree of the extension.** The fundamental
identity `∑ eᵢ fᵢ = [F : K]` bounds each `eᵢ`, and `[𝓞 F : 𝓞 K] = [F : K]`.

Source: Sharifi, Theorem 2.5.11 ("`∑ eᵢ fᵢ = [L : K]`"); Milne, Theorem 3.34. -/
private theorem ramificationIdx_le_finrank_of_isPrime {F : Type*} [Field F] [NumberField F]
    [Algebra K F] (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime] :
    𝔔.ramificationIdx (𝓞 K) ≤ Module.finrank K F := by
  calc 𝔔.ramificationIdx (𝓞 K) ≤ Module.finrank (𝓞 K) (𝓞 F) :=
        TauCeti.RamificationInertia.ramificationIdx_le_finrank (𝔔.under (𝓞 K)) 𝔔
    _ = Module.finrank K F := (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 F) F).symm

/-- **The degree of a cyclotomic extension above an unramified prime is at least `φ(p^(k+1))`.**
A prime `𝔔` of `𝓞 F` above `p` has relative ramification index at least `φ(p^(k+1))` over `𝓞 K`,
and a ramification index never exceeds the degree of the extension. This is the total ramification
of `K(ζ_{p^(k+1)}) / K` above `p` that Layer 7.3 of the Chebotarev roadmap consumes.

Source: Sharifi, Theorem 2.5.11 (`∑ eᵢ fᵢ = [L : K]`); Milne, Theorem 3.34; roadmap README
Layer 7.3 ("by 7.2 the extension `K(ζ_q)/K` is totally ramified at every prime above `q`"). -/
theorem totient_le_finrank_of_unramified (p k : ℕ) [Fact p.Prime] (F : Type*) [Field F]
    [Algebra K F] [IsCyclotomicExtension {p ^ (k + 1)} K F]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮) :
    (p ^ (k + 1)).totient ≤ Module.finrank K F := by
  have : FiniteDimensional K F := IsCyclotomicExtension.finiteDimensional {p ^ (k + 1)} K F
  have : NumberField F := NumberField.of_module_finite K F
  obtain ⟨𝔔, h1, h2⟩ := exists_isPrime_liesOver F p
  exact (totient_le_ramificationIdx p k hur 𝔔).trans (ramificationIdx_le_finrank_of_isPrime 𝔔)

variable (K) in
/-- **Unramifiedness gives irreducibility of `Φ_{p^(k+1)}`.** If the prime `p` is unramified in the
number field `K`, then the `p^(k+1)`-th cyclotomic polynomial is irreducible over `K`: the
`p^(k+1)`-th cyclotomic extension has degree at least `φ(p^(k+1))` by
`totient_le_finrank_of_unramified`, and `irreducible_cyclotomic_of_totient_le_finrank` applies.

Source: roadmap README Layer 7.2, steps 1–3; Milne, Prop. 6.2 and Sharifi, Lemma 3.1.13 for the
base `ℚ`. -/
theorem irreducible_cyclotomic_prime_pow_of_unramified (p k : ℕ) [Fact p.Prime]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮) :
    Irreducible (cyclotomic (p ^ (k + 1)) K) := by
  exact irreducible_cyclotomic_of_totient_le_finrank K (CyclotomicField (p ^ (k + 1)) K)
    (totient_le_finrank_of_unramified p k _ hur)

variable (K) in
/-- **Layer 7.2, the degree input the crossing actually needs.** `q` unramified in `K` forces
`K ∩ ℚ(ζ_q) = ℚ`, because `ℚ(ζ_q)/ℚ` is totally ramified at `q` and so every subfield of it other
than `ℚ` is ramified at `q`. That is what makes the `q`-th cyclotomic polynomial irreducible over
`K`, hence `[K(ζ_q) : K] = q - 1`.

`L ⊓ K(ζ_q) = ⊥` implies none of this: it constrains `L`, not `K ∩ ℚ(ζ_q)`. See
`Polynomial.not_irreducible_cyclotomic_five_of_sq_eq_five` for the witness.

Source: roadmap `Suggested.lean`, `irreducible_cyclotomic_of_unramified` (pinned statement); the
case `k = 0` of `irreducible_cyclotomic_prime_pow_of_unramified`. -/
theorem irreducible_cyclotomic_of_unramified (q : ℕ) (hq : q.Prime)
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(q : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮) :
    Irreducible (cyclotomic q K) := by
  have : Fact q.Prime := ⟨hq⟩
  simpa using irreducible_cyclotomic_prime_pow_of_unramified K q 0 hur

omit [NumberField K] in
variable (K) in
/-- **Layer 7.2, the auxiliary Galois group is the full unit group**, in particular cyclic of order
`q - 1`. Consuming Mathlib's `IsCyclotomicExtension.autEquivPow` keeps the irreducibility hypothesis
visible in the type, so a crossing argument cannot silently assume the order. The name records its
role in the Chebotarev crossing, where `F = K(ζ_q)` for the auxiliary prime `q`.

Source: roadmap `Suggested.lean`, `card_auxiliaryCyclotomic` (pinned statement); roadmap README
Layer 7.2, step 3 ("the cyclotomic character `Gal(K(ζ_q)/K) ≃ (ZMod q)ˣ` is an isomorphism onto
the full unit group, in particular cyclic of order `q - 1`"). -/
theorem card_auxiliaryCyclotomic (q : ℕ) [NeZero q] (F : Type*) [Field F] [Algebra K F]
    [IsCyclotomicExtension {q} K F] (hq : q.Prime) (hirr : Irreducible (cyclotomic q K)) :
    Nat.card (F ≃ₐ[K] F) = q - 1 := by
  have : Fact q.Prime := ⟨hq⟩
  rw [Nat.card_congr (IsCyclotomicExtension.autEquivPow F hirr).toEquiv, Nat.card_eq_fintype_card]
  exact ZMod.card_units q

end IsCyclotomicExtension

