/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
public import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
public import TauCeti.NumberTheory.NumberField.ArtinSymbol

/-!
# The cyclotomic character weight

For a finite Galois extension `L / K` of number fields and a character `χ : Gal(L/K) →* ℂˣ`, this
file builds the *canonical ideal weight* `cyclotomicCharacterWeight χ`: the completely
multiplicative function on the ideals of `𝓞 K` whose value at a height-one prime `𝔭` is
`χ (Frob 𝔭)` when `𝔭` is unramified in `L`, and `0` when `𝔭` ramifies.

The weight is **total**, and that is a design constraint rather than a convenience: a weight
specified only away from ramification leaves its values at the bad primes unconstrained, so the
Euler product and the orthogonality identities would not pin it down. Vanishing at the ramified
primes is what makes the ramified Euler factors drop out as `(1 - 0)⁻¹ = 1`.

## Main definitions

* `NumberField.Chebotarev.cyclotomicCharacterPrimeValue`: the value of the weight at a single
  prime, `χ (Frob 𝔭)` at an unramified maximal `𝔭` and `0` otherwise.
* `NumberField.Chebotarev.cyclotomicCharacterWeightFun`: the completely multiplicative function
  on ideals extending that prime value through the prime factorization.
* `NumberField.Chebotarev.cyclotomicCharacterWeight`: the same function packaged as a
  `TauCeti.MultiplicativeIdealWeight K`.

## Main results

* `NumberField.Chebotarev.cyclotomicCharacterWeightFun_mul`: the weight is completely
  multiplicative.
* `NumberField.Chebotarev.cyclotomicCharacterWeightFun_heightOne_eq_zero_iff`: the weight
  vanishes at a height-one prime exactly when that prime ramifies in `L`.
* `NumberField.Chebotarev.badPrimes_cyclotomicCharacterWeight`: the bad primes of the weight are
  exactly the ramified primes.

## Implementation notes

The weight is packaged as a `TauCeti.MultiplicativeIdealWeight K` rather than as a bare function
`Ideal (𝓞 K) → ℂ`. That carrier already supplies the `→*₀` bundling, the `badPrimes` API and the
bridge `toIdealArithmeticFunction` into the ideal Euler product, so the Euler-product identity is
an instantiation of existing supplier machinery rather than a fresh development.

Two deltas against the source, both forced by the target API:

* the source's `frobeniusClass K L 𝔭` is total on ideals, whereas `NumberField.artinSymbol` takes
  the unramifiedness proof as an argument and needs `𝔭.IsMaximal`. The value at a prime is
  therefore produced by a `dite` on the ramification condition, which is exactly the negation of
  membership in `ramifiedPrimes K L` supplied by `mem_ramifiedPrimes_iff`;
* a `→*₀` must send `⊥` to `0`, whereas the raw factorization product sends `⊥` to the empty
  product `1`. The zero ideal is therefore split off explicitly.

## References

Adapted from `galoisCharacterOnIdeal`, `galoisCharacterOnIdeal_mul` and
`norm_galoisCharacterOnIdeal_le_one` in `CebotarevDensity/ZetaProduct.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, following Sharifi,
*Algebraic Number Theory*, Notation 7.1.17. The factorization-product definition and the
`Multiset.map_add`/`Multiset.prod_add` multiplicativity argument are the source's; the
`MultiplicativeIdealWeight` packaging and the `artinSymbol` totalization are the roadmap's.
-/

public section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

open UniqueFactorizationMonoid

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

open scoped Classical in
/-- The value of `cyclotomicCharacterWeight χ` at a single prime: `χ (Frob 𝔭)` at an unramified
maximal `𝔭`, and `0` otherwise. -/
noncomputable def cyclotomicCharacterPrimeValue (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔭 : Ideal (𝓞 K)) : ℂ :=
  -- The unramifiedness clause is spelled out rather than named because it is, character for
  -- character, `artinSymbol`'s `hur` hypothesis: `h.2` is handed to it directly below.
  if h : 𝔭.IsMaximal ∧ ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q then
    have : 𝔭.IsMaximal := h.1
    (χ (artinSymbol (L := L) 𝔭 h.2).out : ℂ)
  else 0

open scoped Classical in
/-- **The canonical ideal weight of a Galois character.** On a prime it is `χ (Frob 𝔭)` at the
unramified primes and `0` at the ramified ones; it is extended to all ideals completely
multiplicatively through the prime factorization, and sends the zero ideal to `0`. -/
noncomputable def cyclotomicCharacterWeightFun (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 : Ideal (𝓞 K)) : ℂ :=
  if 𝔞 = ⊥ then 0
  else ((normalizedFactors 𝔞).map (cyclotomicCharacterPrimeValue (L := L) χ)).prod

/-- The zero ideal has weight `0`. -/
@[simp]
theorem cyclotomicCharacterWeightFun_bot (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    cyclotomicCharacterWeightFun (L := L) χ ⊥ = 0 := by
  simp [cyclotomicCharacterWeightFun]

/-- Away from the zero ideal the weight is the factorization product. -/
theorem cyclotomicCharacterWeightFun_of_ne_bot (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔞 : Ideal (𝓞 K)}
    (h𝔞 : 𝔞 ≠ ⊥) :
    cyclotomicCharacterWeightFun (L := L) χ 𝔞 =
      ((normalizedFactors 𝔞).map (cyclotomicCharacterPrimeValue (L := L) χ)).prod := by
  simp [cyclotomicCharacterWeightFun, h𝔞]

/-- The unit ideal has weight `1`. -/
@[simp]
theorem cyclotomicCharacterWeightFun_top (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    cyclotomicCharacterWeightFun (L := L) χ ⊤ = 1 := by
  rw [cyclotomicCharacterWeightFun_of_ne_bot χ top_ne_bot, ← Ideal.one_eq_top,
    normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]

/-- **Complete multiplicativity.** The weight of a product of ideals is the product of the
weights. -/
theorem cyclotomicCharacterWeightFun_mul (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 𝔟 : Ideal (𝓞 K)) :
    cyclotomicCharacterWeightFun (L := L) χ (𝔞 * 𝔟) =
      cyclotomicCharacterWeightFun (L := L) χ 𝔞 * cyclotomicCharacterWeightFun (L := L) χ 𝔟 := by
  -- Both degenerate cases collapse: `⊥ * 𝔟 = ⊥` and `𝔞 * ⊥ = ⊥`, so each side is `0`.
  rcases eq_or_ne 𝔞 ⊥ with rfl | h𝔞
  · simp
  rcases eq_or_ne 𝔟 ⊥ with rfl | h𝔟
  · simp
  -- `Ideal.mul_eq_bot`, not `mul_ne_zero`: the latter produces `𝔞 * 𝔟 ≠ 0`, and although `0` and
  -- `⊥` are definitionally equal for ideals they are not syntactically equal, so `rw` cannot
  -- match it against the `⊥` in the definition.
  have hab : 𝔞 * 𝔟 ≠ ⊥ := fun h ↦ (Ideal.mul_eq_bot.mp h).elim h𝔞 h𝔟
  rw [cyclotomicCharacterWeightFun_of_ne_bot χ hab, cyclotomicCharacterWeightFun_of_ne_bot χ h𝔞,
    cyclotomicCharacterWeightFun_of_ne_bot χ h𝔟, normalizedFactors_mul h𝔞 h𝔟,
    Multiset.map_add, Multiset.prod_add]

/-- On a height-one prime the weight is just the single prime value. -/
theorem cyclotomicCharacterWeightFun_heightOne (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    cyclotomicCharacterWeightFun (L := L) χ 𝔭.asIdeal =
      cyclotomicCharacterPrimeValue (L := L) χ 𝔭.asIdeal := by
  -- The factorization of a prime ideal is the one-element multiset.
  simp only [cyclotomicCharacterWeightFun_of_ne_bot χ 𝔭.ne_bot,
    normalizedFactors_irreducible 𝔭.irreducible, normalize_eq, Multiset.map_singleton,
    Multiset.prod_singleton]

/-- The weight vanishes at a height-one prime exactly when that prime ramifies in `L`. This is
the roadmap's design constraint made precise, and it is what makes the weight *total*: the bad
primes are not left unconstrained, they are pinned to `0`. -/
theorem cyclotomicCharacterWeightFun_heightOne_eq_zero_iff (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    cyclotomicCharacterWeightFun (L := L) χ 𝔭.asIdeal = 0 ↔ 𝔭 ∈ ramifiedPrimes K L := by
  rw [cyclotomicCharacterWeightFun_heightOne, cyclotomicCharacterPrimeValue,
    mem_ramifiedPrimes_iff]
  -- A height-one prime is maximal, so the `dite` condition reduces to unramifiedness.
  split_ifs with h
  · exact iff_of_false (Units.ne_zero _) (not_not_intro h.2)
  · exact iff_of_true rfl fun hc ↦ h ⟨𝔭.isMaximal, hc⟩

/-- **The cyclotomic character weight** of a Galois character `χ`, packaged as a
`MultiplicativeIdealWeight`. -/
noncomputable def cyclotomicCharacterWeight (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    TauCeti.MultiplicativeIdealWeight K where
  toMonoidWithZeroHom :=
    { toFun := cyclotomicCharacterWeightFun (L := L) χ
      map_zero' := cyclotomicCharacterWeightFun_bot χ
      map_one' := by simp
      map_mul' := cyclotomicCharacterWeightFun_mul χ }
  -- The vanishing set is exactly `ramifiedPrimes K L`, which is already a `Finset`.
  finite_setOf_apply_eq_zero := (ramifiedPrimes K L).finite_toSet.subset fun 𝔭 h𝔭 ↦
    (cyclotomicCharacterWeightFun_heightOne_eq_zero_iff χ 𝔭).mp h𝔭

/-- Defining equation of `cyclotomicCharacterWeight`; its body is not exposed. -/
@[simp]
theorem cyclotomicCharacterWeight_apply (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 : Ideal (𝓞 K)) :
    cyclotomicCharacterWeight (L := L) χ 𝔞 = cyclotomicCharacterWeightFun (L := L) χ 𝔞 := (rfl)

/-- The bad primes of the cyclotomic character weight are exactly the ramified primes. -/
@[simp]
theorem badPrimes_cyclotomicCharacterWeight (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    (cyclotomicCharacterWeight (L := L) χ).badPrimes = ↑(ramifiedPrimes K L) := by
  ext 𝔭
  -- `badPrimes` is not exposed here, so `mem_badPrimes` opens the membership; `rfl` cannot.
  simpa only [TauCeti.MultiplicativeIdealWeight.mem_badPrimes, cyclotomicCharacterWeight_apply,
    Finset.mem_coe] using cyclotomicCharacterWeightFun_heightOne_eq_zero_iff χ 𝔭

end NumberField.Chebotarev
