/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.PeterssonInner

/-!
# The Petersson inner product on cusp forms

The sesquilinear API for `CuspForm.pet` and the `Inner ℂ (CuspForm Γ k)` structure it
defines, together with **positive definiteness**: a cusp form with vanishing Petersson
self-pairing is zero.

## Main results

* `CuspForm.inner_def`: `⟪f, g⟫ = pet f g`.
* `CuspForm.pet_conj_symm`, `pet_add_left`, `pet_add_right`, `pet_smul_right`,
  `pet_conj_smul_left`: `pet` is Hermitian-sesquilinear.
* `CuspForm.pet_definite`: `pet f f = 0 → f = 0`, for any arithmetic level `Γ`.

## Implementation notes

Definiteness upgrades `UpperHalfPlane.eq_zero_on_fd_of_peterssonInner_self_eq_zero`
(vanishing on the fundamental domain `𝒟`) to vanishing everywhere via the identity
theorem `UpperHalfPlane.eq_zero_of_frequently`: `f` vanishes on the open set `𝒟ᵒ`, and a
holomorphic function on the connected space `ℍ` vanishing on a nonempty open set is zero.

The scalar lemmas assume `Γ.HasDetOne`, which is what Mathlib's ℂ-scalar multiplication
on `CuspForm Γ k` requires; the additivity and definiteness lemmas assume
`Γ.IsArithmetic`, which the integrability of the Petersson integrand requires.

We do **not** register an `InnerProductSpace ℂ (CuspForm Γ k)` instance: that structure
requires a compatible `Norm`, which `CuspForm Γ k` does not carry.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.4
* Miyake, *Modular forms*, §2.7–2.8
-/

public section

noncomputable section

namespace CuspForm

open UpperHalfPlane ModularGroup MeasureTheory

open scoped ComplexConjugate ComplexInnerProductSpace MatrixGroups

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- The Petersson inner product as an `Inner ℂ` structure on cusp forms. -/
instance : Inner ℂ (CuspForm Γ k) where
  inner := pet

@[simp]
theorem inner_def (f g : CuspForm Γ k) : ⟪f, g⟫ = pet f g := rfl

/-- Hermitian symmetry of the Petersson inner product of cusp forms. -/
theorem pet_conj_symm (f g : CuspForm Γ k) : conj (pet g f) = pet f g := by
  simp only [pet_def]
  exact peterssonInner_conj_symm k ModularGroup.fd f g

section HasDetOne

variable [Γ.HasDetOne]

/-- The Petersson inner product is ℂ-linear in the second argument. -/
theorem pet_smul_right (c : ℂ) (f g : CuspForm Γ k) : pet f (c • g) = c * pet f g := by
  simp only [pet_def, IsGLPos.coe_smul]
  exact peterssonInner_smul_right k ModularGroup.fd c f g

/-- The Petersson inner product is conjugate-linear in the first argument. -/
theorem pet_conj_smul_left (c : ℂ) (f g : CuspForm Γ k) :
    pet (c • f) g = conj c * pet f g := by
  simp only [pet_def, IsGLPos.coe_smul]
  exact peterssonInner_conj_smul_left k ModularGroup.fd c f g

end HasDetOne

section IsArithmetic

variable [Γ.IsArithmetic]

/-- Additivity of the Petersson inner product in the second argument. -/
theorem pet_add_right (f g₁ g₂ : CuspForm Γ k) : pet f (g₁ + g₂) = pet f g₁ + pet f g₂ := by
  simp only [pet_def, coe_add]
  exact peterssonInner_add_right k ModularGroup.fd f g₁ g₂
    (peterssonInner_integrableOn_left k Γ f g₁) (peterssonInner_integrableOn_left k Γ f g₂)

/-- Additivity of the Petersson inner product in the first argument. -/
theorem pet_add_left (f₁ f₂ g : CuspForm Γ k) : pet (f₁ + f₂) g = pet f₁ g + pet f₂ g := by
  rw [← pet_conj_symm, pet_add_right, map_add, pet_conj_symm, pet_conj_symm]

/-- **Positive definiteness** of the Petersson inner product: a cusp form of any
arithmetic level with `pet f f = 0` is zero.

`pet f f = 0` forces `f = 0` on the open fundamental domain `𝒟ᵒ`, and a holomorphic
function on `ℍ` vanishing on a nonempty open set vanishes identically. -/
theorem pet_definite (f : CuspForm Γ k) (hpet : pet f f = 0) : f = 0 := by
  rw [pet_def] at hpet
  have hfdo : ∀ τ ∈ fdo, f τ = 0 := fun τ hτ ↦
    eq_zero_on_fd_of_peterssonInner_self_eq_zero f hpet (fdo_subset_fd hτ)
  set τ₀ : ℍ := ⟨⟨0, 2⟩, by norm_num⟩ with hτ₀_def
  have hτ₀ : τ₀ ∈ fdo := by
    constructor
    · norm_num [hτ₀_def, Complex.normSq_apply]
    · norm_num [hτ₀_def]
  have hev := Filter.eventually_of_mem (isOpen_fdo.mem_nhds hτ₀) hfdo
  have h := UpperHalfPlane.eq_zero_of_frequently (CuspFormClass.holo f)
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  ext τ
  exact congr_fun h τ

end IsArithmetic

end CuspForm
