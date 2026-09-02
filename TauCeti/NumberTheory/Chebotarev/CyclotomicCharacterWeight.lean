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
* a `→*₀` must send `⊥` to `0`, whereas the raw factorisation product sends `⊥` to the empty
  product `1`. The zero ideal is therefore split off explicitly.

## References

Adapted from `galoisCharacterOnIdeal`, `galoisCharacterOnIdeal_mul` and
`norm_galoisCharacterOnIdeal_le_one` in `CebotarevDensity/ZetaProduct.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, following Sharifi,
*Algebraic Number Theory*, Notation 7.1.17. The factorisation-product definition and the
`Multiset.map_add`/`Multiset.prod_add` multiplicativity argument are the source's; the
`MultiplicativeIdealWeight` packaging and the `artinSymbol` totalisation are the roadmap's.
-/

public section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

open UniqueFactorizationMonoid

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- The unramifiedness side condition carried by `NumberField.artinSymbol`, as a `Prop` on an
ideal of `𝓞 K`. It is the negation of membership in `ramifiedPrimes K L`. -/
def IsUnramifiedAtIdeal (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (𝔭 : Ideal (𝓞 K)) : Prop :=
  ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q

open Classical in
/-- The value of `cyclotomicCharacterWeight χ` at a single prime: `χ (Frob 𝔭)` at an unramified
maximal `𝔭`, and `0` otherwise. The `dite` is what makes the weight total; `artinSymbol` is only
defined at unramified primes. -/
noncomputable def cyclotomicCharacterPrimeValue (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔭 : Ideal (𝓞 K)) : ℂ :=
  if h : 𝔭.IsMaximal ∧ IsUnramifiedAtIdeal K L 𝔭 then
    haveI : 𝔭.IsMaximal := h.1
    (χ (artinSymbol (L := L) 𝔭 h.2).out : ℂ)
  else 0

open Classical in
/-- **The canonical ideal weight of a Galois character.** On a prime it is `χ (Frob 𝔭)` at the
unramified primes and `0` at the ramified ones; it is extended to all ideals completely
multiplicatively through the prime factorisation, and sends the zero ideal to `0`. -/
noncomputable def cyclotomicCharacterWeightFun (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 : Ideal (𝓞 K)) : ℂ :=
  if 𝔞 = ⊥ then 0 else
    ((normalizedFactors 𝔞).map (cyclotomicCharacterPrimeValue (L := L) χ)).prod

open Classical in
/-- The zero ideal has weight `0`. -/
@[simp]
theorem cyclotomicCharacterWeightFun_bot (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    cyclotomicCharacterWeightFun (L := L) χ ⊥ = 0 := by
  simp [cyclotomicCharacterWeightFun]

open Classical in
/-- Away from the zero ideal the weight is the factorisation product. This is the form every
proof below uses: it discharges the zero-ideal branch once, so the multiplicativity argument
never has to mention it. -/
theorem cyclotomicCharacterWeightFun_of_ne_bot (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔞 : Ideal (𝓞 K)}
    (h𝔞 : 𝔞 ≠ ⊥) :
    cyclotomicCharacterWeightFun (L := L) χ 𝔞 =
      ((normalizedFactors 𝔞).map (cyclotomicCharacterPrimeValue (L := L) χ)).prod := by
  simp [cyclotomicCharacterWeightFun, h𝔞]

/-- The unit ideal has weight `1`: it has no prime factors, so the product is empty. -/
@[simp]
theorem cyclotomicCharacterWeightFun_top (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    cyclotomicCharacterWeightFun (L := L) χ ⊤ = 1 := by
  rw [cyclotomicCharacterWeightFun_of_ne_bot χ top_ne_bot, ← Ideal.one_eq_top,
    normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]

/-- **Complete multiplicativity.** Transcribed from the source: `normalizedFactors` turns a
product of ideals into a sum of multisets, and `Multiset.prod_add` turns that into a product of
values. The zero ideal is handled by the explicit split, since `⊥ * 𝔟 = ⊥`.

The nonvanishing side condition is built through `Ideal.mul_eq_bot` rather than `mul_ne_zero`:
the latter produces `𝔞 * 𝔟 ≠ 0`, and although `0` and `⊥` are definitionally equal for ideals
they are not syntactically equal, so `rw` cannot match it against the `⊥` in the definition. -/
theorem cyclotomicCharacterWeightFun_mul (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 𝔟 : Ideal (𝓞 K)) :
    cyclotomicCharacterWeightFun (L := L) χ (𝔞 * 𝔟) =
      cyclotomicCharacterWeightFun (L := L) χ 𝔞 * cyclotomicCharacterWeightFun (L := L) χ 𝔟 := by
  rcases eq_or_ne 𝔞 ⊥ with rfl | h𝔞
  · simp
  rcases eq_or_ne 𝔟 ⊥ with rfl | h𝔟
  · simp
  have hab : 𝔞 * 𝔟 ≠ ⊥ := fun h ↦ (Ideal.mul_eq_bot.mp h).elim h𝔞 h𝔟
  rw [cyclotomicCharacterWeightFun_of_ne_bot χ hab, cyclotomicCharacterWeightFun_of_ne_bot χ h𝔞,
    cyclotomicCharacterWeightFun_of_ne_bot χ h𝔟, normalizedFactors_mul h𝔞 h𝔟,
    Multiset.map_add, Multiset.prod_add]

open Classical in
/-- On a height-one prime the weight is just the single prime value: the factorisation of a
prime ideal is the one-element multiset. -/
theorem cyclotomicCharacterWeightFun_heightOne (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    cyclotomicCharacterWeightFun (L := L) χ 𝔭.asIdeal =
      cyclotomicCharacterPrimeValue (L := L) χ 𝔭.asIdeal := by
  rw [cyclotomicCharacterWeightFun_of_ne_bot χ 𝔭.ne_bot,
    normalizedFactors_irreducible (Ideal.prime_of_isPrime 𝔭.ne_bot 𝔭.isPrime).irreducible,
    normalize_eq, Multiset.map_singleton, Multiset.prod_singleton]

open Classical in
/-- The weight vanishes at a height-one prime exactly when that prime ramifies in `L`. This is
the roadmap's design constraint made precise, and it is what makes the weight *total*: the bad
primes are not left unconstrained, they are pinned to `0`. -/
theorem cyclotomicCharacterWeightFun_heightOne_eq_zero_iff (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    cyclotomicCharacterWeightFun (L := L) χ 𝔭.asIdeal = 0 ↔ 𝔭 ∈ ramifiedPrimes K L := by
  have hmax : 𝔭.asIdeal.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime 𝔭.ne_bot 𝔭.isPrime
  rw [cyclotomicCharacterWeightFun_heightOne, cyclotomicCharacterPrimeValue,
    mem_ramifiedPrimes_iff]
  split_ifs with h
  · exact ⟨fun hz ↦ absurd hz (Units.ne_zero _), fun hr ↦ absurd h.2 hr⟩
  · exact ⟨fun _ hc ↦ h ⟨hmax, hc⟩, fun _ ↦ rfl⟩

open Classical in
/-- **The cyclotomic character weight** of a Galois character `χ`, packaged as a
`MultiplicativeIdealWeight`.

Using that carrier rather than a bare function is what makes the roadmap's Euler product a
consumer of existing supplier machinery: `toIdealArithmeticFunction` and
`isMultiplicative_toIdealArithmeticFunction` carry it into the ideal Euler product without any
further hypothesis. The finiteness field is discharged by `ramifiedPrimes`, which is already a
`Finset`. -/
noncomputable def cyclotomicCharacterWeight (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    TauCeti.MultiplicativeIdealWeight K where
  toMonoidWithZeroHom :=
    { toFun := cyclotomicCharacterWeightFun (L := L) χ
      map_zero' := cyclotomicCharacterWeightFun_bot χ
      map_one' := by simp
      map_mul' := cyclotomicCharacterWeightFun_mul χ }
  finite_setOf_apply_eq_zero := by
    refine Set.Finite.subset (ramifiedPrimes K L).finite_toSet fun 𝔭 h𝔭 ↦ ?_
    exact (cyclotomicCharacterWeightFun_heightOne_eq_zero_iff χ 𝔭).mp h𝔭

/-- Defining equation of `cyclotomicCharacterWeight`. Stated through the equation lemma rather
than by `rfl`: the definition is sealed by the module system, so it is opaque even to a theorem
in its own file. -/
@[simp]
theorem cyclotomicCharacterWeight_apply (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 : Ideal (𝓞 K)) :
    cyclotomicCharacterWeight (L := L) χ 𝔞 = cyclotomicCharacterWeightFun (L := L) χ 𝔞 := by
  rw [cyclotomicCharacterWeight]
  rfl

/-- The bad primes of the cyclotomic character weight are exactly the ramified primes. -/
theorem badPrimes_cyclotomicCharacterWeight (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    (cyclotomicCharacterWeight (L := L) χ).badPrimes = ↑(ramifiedPrimes K L) := by
  ext 𝔭
  simpa [TauCeti.MultiplicativeIdealWeight.mem_badPrimes] using
    cyclotomicCharacterWeightFun_heightOne_eq_zero_iff χ 𝔭

end NumberField.Chebotarev
