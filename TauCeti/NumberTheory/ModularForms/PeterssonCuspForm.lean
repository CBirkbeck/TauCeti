/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.PeterssonInner

/-!
# The Petersson inner product on cusp forms

The sesquilinear API for `CuspForm.peterssonInner` and the `Inner ℂ (CuspForm Γ k)` structure it
defines, together with **positive definiteness**: a cusp form with vanishing Petersson
self-pairing is zero.

## Main results

* `CuspForm.inner_def`: `⟪f, g⟫ = peterssonInner f g`.
* `CuspForm.peterssonInner_conj_symm`, `peterssonInner_add_left`, `peterssonInner_add_right`,
  `peterssonInner_smul_right`, `peterssonInner_smul_left`: Hermitian-sesquilinear.
* `CuspForm.peterssonInner_definite`: `peterssonInner f f = 0 → f = 0`, for any arithmetic
  level `Γ`.

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
  inner := peterssonInner

@[simp]
theorem inner_def (f g : CuspForm Γ k) : ⟪f, g⟫ = peterssonInner f g := rfl

/-- Hermitian symmetry of the Petersson inner product of cusp forms. -/
theorem peterssonInner_conj_symm (f g : CuspForm Γ k) :
    conj (peterssonInner g f) = peterssonInner f g := by
  simp only [peterssonInner_def]
  exact UpperHalfPlane.peterssonInner_conj_symm k ModularGroup.fd f g

section HasDetOne

variable [Γ.HasDetOne]

/-- The Petersson inner product is ℂ-linear in the second argument. -/
theorem peterssonInner_smul_right (c : ℂ) (f g : CuspForm Γ k) :
    peterssonInner f (c • g) = c * peterssonInner f g := by
  simp only [peterssonInner_def, IsGLPos.coe_smul]
  exact UpperHalfPlane.peterssonInner_smul_right k ModularGroup.fd c f g

/-- The Petersson inner product is conjugate-linear in the first argument. -/
theorem peterssonInner_smul_left (c : ℂ) (f g : CuspForm Γ k) :
    peterssonInner (c • f) g = conj c * peterssonInner f g := by
  simp only [peterssonInner_def, IsGLPos.coe_smul]
  exact UpperHalfPlane.peterssonInner_smul_left k ModularGroup.fd c f g

end HasDetOne

section IsArithmetic

variable [Γ.IsArithmetic]

/-- Additivity of the Petersson inner product in the second argument. -/
theorem peterssonInner_add_right (f g₁ g₂ : CuspForm Γ k) :
    peterssonInner f (g₁ + g₂) = peterssonInner f g₁ + peterssonInner f g₂ := by
  simp only [peterssonInner_def, coe_add]
  exact UpperHalfPlane.peterssonInner_add_right k ModularGroup.fd f g₁ g₂
    (integrableOn_petersson_fd_left k Γ f g₁) (integrableOn_petersson_fd_left k Γ f g₂)

/-- Additivity of the Petersson inner product in the first argument. -/
theorem peterssonInner_add_left (f₁ f₂ g : CuspForm Γ k) :
    peterssonInner (f₁ + f₂) g = peterssonInner f₁ g + peterssonInner f₂ g := by
  rw [← peterssonInner_conj_symm, peterssonInner_add_right, map_add,
    peterssonInner_conj_symm, peterssonInner_conj_symm]

/-- **Positive definiteness** of the Petersson inner product: a cusp form of any
arithmetic level with `peterssonInner f f = 0` is zero.

`peterssonInner f f = 0` forces `f = 0` on the open fundamental domain `𝒟ᵒ`, and a holomorphic
function on `ℍ` vanishing on a nonempty open set vanishes identically. -/
theorem peterssonInner_definite (f : CuspForm Γ k) (hpet : peterssonInner f f = 0) : f = 0 := by
  rw [peterssonInner_def] at hpet
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
