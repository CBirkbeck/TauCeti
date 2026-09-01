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
/-- The unit ideal has weight `1`: it has no prime factors, so the product is empty. -/
@[simp]
theorem cyclotomicCharacterWeightFun_top (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    cyclotomicCharacterWeightFun (L := L) χ ⊤ = 1 := by
  rw [cyclotomicCharacterWeightFun, if_neg (by simp [Ideal.top_ne_bot]), ← Ideal.one_eq_top,
    normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]

open Classical in
/-- The zero ideal has weight `0`. -/
@[simp]
theorem cyclotomicCharacterWeightFun_bot (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    cyclotomicCharacterWeightFun (L := L) χ ⊥ = 0 := by
  rw [cyclotomicCharacterWeightFun, if_pos rfl]

open Classical in
/-- **Complete multiplicativity.** Transcribed from the source: `normalizedFactors` turns a
product of ideals into a sum of multisets, and `Multiset.prod_add` turns that into a product of
values. The zero ideal is handled by the explicit split, since `⊥ * 𝔟 = ⊥`. -/
theorem cyclotomicCharacterWeightFun_mul (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 𝔟 : Ideal (𝓞 K)) :
    cyclotomicCharacterWeightFun (L := L) χ (𝔞 * 𝔟) =
      cyclotomicCharacterWeightFun (L := L) χ 𝔞 * cyclotomicCharacterWeightFun (L := L) χ 𝔟 := by
  rcases eq_or_ne 𝔞 ⊥ with rfl | h𝔞
  · simp
  rcases eq_or_ne 𝔟 ⊥ with rfl | h𝔟
  · simp
  rw [cyclotomicCharacterWeightFun, cyclotomicCharacterWeightFun, cyclotomicCharacterWeightFun,
    if_neg h𝔞, if_neg h𝔟, if_neg (mul_ne_zero h𝔞 h𝔟), normalizedFactors_mul h𝔞 h𝔟,
    Multiset.map_add, Multiset.prod_add]

end NumberField.Chebotarev
