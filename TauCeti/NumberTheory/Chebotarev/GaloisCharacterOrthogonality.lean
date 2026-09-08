/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
public import TauCeti.NumberTheory.Chebotarev.GaloisCharacterWeight

/-!
# Character orthogonality for the ideal weight of a Galois character

For a finite **abelian** Galois extension `L / K` of number fields, summing `(χ σ)⁻¹` against the
ideal weight `MonoidHom.galoisCharacterWeight χ` over all characters `χ : Gal(L/K) →* ℂˣ` selects
one Frobenius fibre: at a height-one prime `𝔭` unramified in `L` the sum is `#Gal(L/K)` when the
Frobenius at `𝔭` is `σ`, and `0` otherwise. At a ramified prime it is `0`, because every summand is.

This is the character-sum half of the Chebotarev roadmap's Layer 4, the other half being the Euler
product; `Suggested.lean` pins the group-level identity behind it at Layer 11.4 as
`sum_character_indicator`. What it buys is a change of index: an indicator of the single condition
`Frob 𝔭 = σ` becomes a sum over the character group, in which each character contributes an ideal
weight that is completely multiplicative.

## Main results

* `MonoidHom.sum_inv_mul_galoisCharacterWeight_apply_of_unramified`: the orthogonality identity at
  an unramified height-one prime, selecting the fibre of a chosen `σ`.
* `MonoidHom.sum_inv_mul_galoisCharacterWeight_apply_of_mem_ramifiedPrimes`: the sum vanishes at a
  ramified prime, for the trivial reason that every summand does.
* `MonoidHom.sum_galoisCharacterWeight_apply_of_unramified`: the case `σ = 1`, where the plain
  character sum of the weight detects a trivial Frobenius.

## Implementation notes

The inverse sits on the tag `σ`, never on the Frobenius argument. This is the orientation
`Suggested.lean` flags: without the inverse the sum is `∑ χ, χ (σ * Frob 𝔭)`, the indicator of
`Frob 𝔭 = σ⁻¹`, which is a different fibre whenever `σ` is not an involution.

Commutativity enters as `[IsMulCommutative (L ≃ₐ[K] L)]`, a `Prop`-class, rather than as a
`CommGroup` instance argument: `L ≃ₐ[K] L` already carries a `Group` instance, and a second
bundled group structure on the same type would be a diamond. Mathlib supplies the bundled form
from the mixin as a `scoped instance` in the `IsMulCommutative` namespace, deliberately kept out of
global synthesis, so the proofs open that scope rather than building a `CommGroup` by hand.

The abelian hypothesis is what `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` requires, and it is
not a restriction in the intended application: Layer 4 reads this over `K(ζ_m) / K`, whose Galois
group is abelian by `IsCyclotomicExtension.Aut.commGroup`.

The sum ranges over the full character group, whose cardinality equals `Nat.card (L ≃ₐ[K] L)` by
Mathlib's duality for finite abelian groups; that equality is what puts `Nat.card (L ≃ₐ[K] L)` on
the right rather than the cardinality of the dual.
-/
@[expose] public section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

open NumberField NumberField.Chebotarev

namespace MonoidHom

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **Orthogonality at a ramified prime.** Every character's weight vanishes there, so any
character sum against it does too. No commutativity is needed. -/
theorem sum_inv_mul_galoisCharacterWeight_apply_of_mem_ramifiedPrimes (σ : L ≃ₐ[K] L)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : 𝔭 ∈ ramifiedPrimes K L) :
    ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
        (((χ σ)⁻¹ : ℂˣ) : ℂ) * galoisCharacterWeight (L := L) χ 𝔭.asIdeal = 0 :=
  Finset.sum_eq_zero fun χ _ ↦ by
    rw [(galoisCharacterWeight_apply_eq_zero_iff χ 𝔭).mpr h𝔭, mul_zero]

open scoped Classical IsMulCommutative in
/-- **Character orthogonality for the Galois character weight.** For `L / K` abelian, `σ` a chosen
element of `Gal(L/K)` and `𝔭` a height-one prime unramified in `L`, summing `(χ σ)⁻¹` against the
weight over every character gives `#Gal(L/K)` when the Frobenius at `𝔭` is `σ`, and `0` otherwise.
This is the identity that selects one Frobenius fibre.

The inverse sits on the tag `σ`, never on the Frobenius argument: dropping it would leave
`∑ χ, χ (σ * Frob 𝔭)`, the indicator of `Frob 𝔭 = σ⁻¹`, which is a different fibre whenever `σ` is
not an involution.

`artinSymbol` returns a conjugacy class and `.out` picks a representative, but the value does not
depend on that choice for any group: a character lands in `ℂˣ`, which is abelian, so it kills
commutators and is constant on conjugacy classes. What commutativity is needed for is the count on
the right — over a nonabelian group the character sum detects the image of the class in the
abelianization, not the condition `Frob 𝔭 = σ`. -/
theorem sum_inv_mul_galoisCharacterWeight_apply_of_unramified [IsMulCommutative (L ≃ₐ[K] L)]
    (σ : L ≃ₐ[K] L) (𝔭 : HeightOneSpectrum (𝓞 K))
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
    ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
          (((χ σ)⁻¹ : ℂˣ) : ℂ) * galoisCharacterWeight (L := L) χ 𝔭.asIdeal =
      if (artinSymbol (L := L) 𝔭.asIdeal hur).out = σ then (Nat.card (L ≃ₐ[K] L) : ℂ) else 0 := by
  have hexp : Monoid.exponent (L ≃ₐ[K] L) ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have : NeZero ((Monoid.exponent (L ≃ₐ[K] L) : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.mpr hexp⟩
  calc ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
          (((χ σ)⁻¹ : ℂˣ) : ℂ) * galoisCharacterWeight (L := L) χ 𝔭.asIdeal
      = ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
          (((χ σ)⁻¹ : ℂˣ) : ℂ) * ((χ (artinSymbol (L := L) 𝔭.asIdeal hur).out : ℂˣ) : ℂ) :=
        Finset.sum_congr rfl fun χ _ ↦ by
          rw [galoisCharacterWeight_apply_of_unramified χ 𝔭 hur]
    _ = _ := CommGroup.sum_inv_mul_monoidHom_apply_eq_ite _ _

open scoped Classical IsMulCommutative in
/-- **The split-completely case.** At an unramified height-one prime the plain character sum of the
weight is `#Gal(L/K)` exactly when the Frobenius is trivial. This is
`sum_inv_mul_galoisCharacterWeight_apply_of_unramified` at `σ = 1`. -/
theorem sum_galoisCharacterWeight_apply_of_unramified [IsMulCommutative (L ≃ₐ[K] L)]
    (𝔭 : HeightOneSpectrum (𝓞 K))
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
    ∑ χ : (L ≃ₐ[K] L) →* ℂˣ, galoisCharacterWeight (L := L) χ 𝔭.asIdeal =
      if (artinSymbol (L := L) 𝔭.asIdeal hur).out = 1 then (Nat.card (L ≃ₐ[K] L) : ℂ) else 0 := by
  simpa using sum_inv_mul_galoisCharacterWeight_apply_of_unramified (L := L) 1 𝔭 hur

end MonoidHom
