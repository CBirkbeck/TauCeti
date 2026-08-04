/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Modular.Orbits
public import TauCeti.NumberTheory.ModularForms.Cusps
public import TauCeti.NumberTheory.ModularForms.FiniteZeros

/-!
# The vanishing order on `SL(2, ℤ)`-orbits

The vanishing order of a level-one modular form is constant on `SL(2, ℤ)`-orbits of `ℍ`,
so it descends to the orbit space (`TauCeti.ModularForm.ordOrbit`), and for a nonzero
form only finitely many orbits carry nonzero order — the summation index of the valence
formula. The generic orbit facts it rides live in `TauCeti.NumberTheory.Modular.Orbits`.

## Main declarations

* `TauCeti.ModularForm.ordOrbit`: the order descended to
  `MulAction.orbitRel.Quotient SL(2, ℤ) ℍ`.
* `TauCeti.ModularForm.finite_support_ordOrbit`: finite support on orbits for a nonzero
  form.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane

open scoped ModularForm MatrixGroups Modular

namespace TauCeti

namespace ModularForm

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] (f : F)

/-- The coercion of the `SL(2, ℤ)`-action on `ℍ` to the `GL(2, ℝ)`-action. -/
private lemma smul_eq_coe_smul (g : SL(2, ℤ)) (p : ℍ) :
    g • p = ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) • p := rfl

/-- The vanishing order of a level-one form, descended to `SL(2, ℤ)`-orbits of `ℍ`. -/
def ordOrbit [SlashInvariantFormClass F 𝒮ℒ k] (q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) :
    ℤ :=
  Quotient.liftOn' q (orderOfVanishingAt f) fun _ b ⟨g, hg⟩ ↦ by
    have hg' : g • b = _ := hg
    rw [← hg', smul_eq_coe_smul,
      orderOfVanishingAt_smul f (γ := ((g : SL(2, ℤ)) : GL (Fin 2) ℝ))
        (MonoidHom.mem_range.mpr ⟨g, rfl⟩) (by
          rw [Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
            ← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL]
          exact one_pos) b]

@[simp]
lemma ordOrbit_mk [SlashInvariantFormClass F 𝒮ℒ k] (p : ℍ) :
    ordOrbit f (Quotient.mk'' p) = orderOfVanishingAt f p := by
  unfold ordOrbit
  rfl

/-- For a nonzero level-one form, only finitely many orbits carry nonzero order. -/
lemma finite_support_ordOrbit [ModularFormClass F 𝒮ℒ k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    Set.Finite {q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ | ordOrbit f q ≠ 0} := by
  choose rep hrep_mk hrep_fd using ModularGroup.orbit_exists_fd_rep
  have h_image : rep '' {q | ordOrbit f q ≠ 0} ⊆
      {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt f p ≠ 0} := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨hrep_fd q, by rwa [← ordOrbit_mk f (rep q), hrep_mk q]⟩
  have h_inj : Set.InjOn rep {q | ordOrbit f q ≠ 0} := fun q₁ _ q₂ _ h ↦ by
    rw [← hrep_mk q₁, ← hrep_mk q₂, h]
  exact ((finite_zeros_in_fd hf).subset h_image).of_finite_image h_inj

end ModularForm

end TauCeti

end
