/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import TauCeti.RingTheory.RootsOfUnity.IntegrallyClosed

/-!
# The Kummer character of a group of automorphisms

Let `L / F` be a field extension in which `F` is integrally closed (for fields: algebraically
closed in `L`, as the constants of a function field are), `G` a monoid acting on `L` by
`F`-algebra automorphisms, and `α` a unit of `L` whose `n`-th power no element of `G` moves. Then
each `σ ∈ G` moves `α` by an `n`-th root of unity, which lies in `F` because `F` and `L` have the
same `n`-th roots of unity (`TauCeti.rootsOfUnityMulEquiv`), and `σ ↦ σ α / α` is a homomorphism
`G →* rootsOfUnity n F`: the Kummer character of `α`, with values in the constants. It is
multiplicative in `α`, and trivial exactly when `G` fixes `α`.

Mathlib's `autEquivRootsOfUnity` is the Kummer isomorphism of a splitting field of `Xⁿ - a` over a
base containing the `n`-th roots of unity; here the base is the constant field and the acting
monoid is arbitrary.

## Main definitions

* `TauCeti.kummerCharacter`: the character `σ ↦ σ α / α` of `G` with values in `rootsOfUnity n F`.

## Main results

* `TauCeti.algebraMap_kummerCharacter`: its value at `σ`, read in `L`, is `σ α / α`.
* `TauCeti.kummerCharacter_mul`: it is multiplicative in `α`.
* `TauCeti.kummerCharacter_eq_one_iff`: it is trivial exactly when `G` fixes `α`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1, where the Weil
  pairing is this character for the translation action of `E[n]`.
-/

public section

namespace TauCeti

variable {F L G : Type*} [Field F] [Field L] [Algebra F L] [IsIntegrallyClosedIn F L] [Monoid G]
  (ρ : G →* (L ≃ₐ[F] L)) (n : ℕ) [NeZero n]

-- `σ α / α` as an `n`-th root of unity of `L`.
private noncomputable def ratio {α : Lˣ} (hα : ∀ σ, ρ σ ((α : L) ^ n) = (α : L) ^ n) (σ : G) :
    rootsOfUnity n L :=
  rootsOfUnity.mkOfPowEq (ρ σ α / α) <| by
    rw [div_pow, ← map_pow, hα, div_self (pow_ne_zero _ α.ne_zero)]

/-- **The Kummer character of `α`**: `σ ↦ σ α / α`, which lies in the `n`-th roots of unity of `F`
as soon as no element of `G` moves `αⁿ`. -/
noncomputable def kummerCharacter (α : Lˣ) (hα : ∀ σ, ρ σ ((α : L) ^ n) = (α : L) ^ n) :
    G →* rootsOfUnity n F where
  toFun σ := (rootsOfUnityMulEquiv F L n).symm (ratio ρ n hα σ)
  map_one' := by
    rw [MulEquiv.symm_apply_eq, map_one]
    ext
    simp [ratio]
  map_mul' σ τ := by
    rw [MulEquiv.symm_apply_eq, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    ext
    have hτ : ρ τ α = ((ratio ρ n hα τ : Lˣ) : L) * α := by
      simp [ratio, div_mul_cancel₀ _ α.ne_zero]
    -- `ρ σ` fixes the constant `τ α / α`, which is how it commutes past the second factor.
    have hc : ρ σ ((ratio ρ n hα τ : Lˣ) : L) = ((ratio ρ n hα τ : Lˣ) : L) := by
      rw [← MulEquiv.apply_symm_apply (rootsOfUnityMulEquiv F L n) (ratio ρ n hα τ),
        coe_rootsOfUnityMulEquiv, AlgEquiv.commutes]
    simp only [ratio, rootsOfUnity.coe_mkOfPowEq, Subgroup.coe_mul, Units.val_mul, map_mul,
      AlgEquiv.mul_apply]
    rw [hτ, map_mul, hc]
    simp only [ratio, rootsOfUnity.coe_mkOfPowEq]
    field_simp

variable {ρ n}

/-- **The value of the Kummer character**, read in `L`: `χ(σ) = σ α / α`. -/
@[simp]
theorem algebraMap_kummerCharacter {α : Lˣ} (hα : ∀ σ, ρ σ ((α : L) ^ n) = (α : L) ^ n) (σ : G) :
    algebraMap F L (kummerCharacter ρ n α hα σ : Fˣ) = ρ σ α / α := by
  rw [← coe_rootsOfUnityMulEquiv F L n, kummerCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.apply_symm_apply]
  simp [ratio]

/-- **The Kummer character moves `α` by its value**: `σ α = χ(σ) α`. -/
theorem apply_eq_algebraMap_kummerCharacter_mul {α : Lˣ}
    (hα : ∀ σ, ρ σ ((α : L) ^ n) = (α : L) ^ n) (σ : G) :
    ρ σ α = algebraMap F L (kummerCharacter ρ n α hα σ : Fˣ) * α := by
  rw [algebraMap_kummerCharacter, div_mul_cancel₀ _ α.ne_zero]

/-- **The Kummer character is multiplicative in `α`.** -/
theorem kummerCharacter_mul {α β : Lˣ} (hα : ∀ σ, ρ σ ((α : L) ^ n) = (α : L) ^ n)
    (hβ : ∀ σ, ρ σ ((β : L) ^ n) = (β : L) ^ n)
    (hαβ : ∀ σ, ρ σ (((α * β : Lˣ) : L) ^ n) = ((α * β : Lˣ) : L) ^ n) :
    kummerCharacter ρ n (α * β) hαβ = kummerCharacter ρ n α hα * kummerCharacter ρ n β hβ := by
  ext σ
  refine (algebraMap F L).injective ?_
  simp only [MonoidHom.mul_apply, Subgroup.coe_mul, Units.val_mul, map_mul,
    algebraMap_kummerCharacter]
  exact mul_div_mul_comm _ _ _ _

/-- **The Kummer character is trivial exactly when `G` fixes `α`.** -/
theorem kummerCharacter_eq_one_iff {α : Lˣ} (hα : ∀ σ, ρ σ ((α : L) ^ n) = (α : L) ^ n) :
    kummerCharacter ρ n α hα = 1 ↔ ∀ σ, ρ σ α = α := by
  refine ⟨fun h σ ↦ ?_, fun h ↦ MonoidHom.ext fun σ ↦ Subtype.ext <| Units.ext <|
    (algebraMap F L).injective ?_⟩
  · simpa [h] using apply_eq_algebraMap_kummerCharacter_mul hα σ
  · rw [algebraMap_kummerCharacter, h, div_self α.ne_zero]
    simp

end TauCeti

end
