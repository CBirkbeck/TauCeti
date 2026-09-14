/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
public import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.MeasureTheory.Group.FundamentalDomain
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Basic

/-!
# The Hecke coset representatives tile a fundamental domain

`HeckeRing.GL2.heckeSlashSum` sums `f ∣[k] aᵥ` over `v : DecompQuotient Γ₂ Γ₁ δ⁻¹`, with
`aᵥ = rightCosetRep D v = δ τᵥ⁻¹`. Everything there lives in `GL (Fin 2) ℚ`, which does **not**
act on `ℍ`; the slash goes through `φ = Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)`.

This file shows that the real images `φ aᵥ` of those representatives translate a fundamental
domain for `Γ₂` into one for `Γ₁ ∩ δ Γ₂ δ⁻¹`, both read in `GL (Fin 2) ℝ`.

## Main results

* `HeckeRing.GL2.isFundamentalDomain_iUnion_rightCosetRep_smul`: the tiling.

-/

public section

open MeasureTheory ConjAct Matrix UpperHalfPlane DoubleCoset

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ Γ₁ Γ₂)

/-- The change of scalars `GL (Fin 2) ℚ →* GL (Fin 2) ℝ` the rational slash action factors
through. -/
noncomputable abbrev ratToRealGL : GL (Fin 2) ℚ →* GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

theorem ratToRealGL_injective : Function.Injective (ratToRealGL) :=
  Matrix.GeneralLinearGroup.map_injective (algebraMap ℚ ℝ).injective

open scoped Classical in
/-- **The real images of the Hecke coset representatives tile a fundamental domain.**

`heckeSlashSum` sums over `v : DecompQuotient Γ₂ Γ₁ δ⁻¹` with `aᵥ = δ τᵥ⁻¹`, all in
`GL (Fin 2) ℚ`. Their images under `φ` translate a fundamental domain `S` for `φ(Γ₂)` into one
for `φ(Γ₁) ⊓ φ(δ) φ(Γ₂) φ(δ)⁻¹`. -/
theorem isFundamentalDomain_iUnion_rightCosetRep_smul
    [Countable (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)]
    {S : Set ℍ} {μ : Measure ℍ}
    (hS : IsFundamentalDomain (Γ₂.map ratToRealGL : Subgroup (GL (Fin 2) ℝ)) S μ)
    (hδ : Measure.QuasiMeasurePreserving
      (fun x : ℍ ↦ (ratToRealGL (D.out : GL (Fin 2) ℚ))⁻¹ • x) μ μ)
    (hnull : ∀ v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹,
      NullMeasurableSet (ratToRealGL (((v.out : Γ₂) : GL (Fin 2) ℚ))⁻¹ • S) μ) :
    IsFundamentalDomain
      ((Γ₁.map ratToRealGL ⊓
        toConjAct (ratToRealGL (D.out : GL (Fin 2) ℚ)) • Γ₂.map ratToRealGL :
          Subgroup (GL (Fin 2) ℝ)))
      (⋃ v, ratToRealGL (rightCosetRep D v) • S) μ := by
  have hinj := ratToRealGL_injective
  set r : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹ →
      (Γ₂.map ratToRealGL : Subgroup (GL (Fin 2) ℝ)) := fun v ↦
    ⟨ratToRealGL (((v.out : Γ₂) : GL (Fin 2) ℚ))⁻¹,
      ⟨(((v.out : Γ₂) : GL (Fin 2) ℚ))⁻¹, Γ₂.inv_mem v.out.2, rfl⟩⟩ with hr_def
  have hset : ∀ v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹,
      ratToRealGL (D.out : GL (Fin 2) ℚ) * ((r v : GL (Fin 2) ℝ)) =
        ratToRealGL (rightCosetRep D v) := fun v ↦ by
    simp only [r]
    rw [rightCosetRep_def, map_mul, map_inv]
  have hrinv : ∀ v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹,
      (r v)⁻¹ = Subgroup.equivMapOfInjective Γ₂ ratToRealGL hinj v.out := by
    intro v
    apply Subtype.ext
    simp [r, Subgroup.coe_equivMapOfInjective_apply]
  have hbij : Function.Bijective fun v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹ ↦
      (QuotientGroup.mk (r v)⁻¹ :
        (Γ₂.map ratToRealGL : Subgroup (GL (Fin 2) ℝ)) ⧸
          (toConjAct (ratToRealGL (D.out : GL (Fin 2) ℚ))⁻¹ •
            (Γ₁.map ratToRealGL : Subgroup (GL (Fin 2) ℝ))).subgroupOf
              (Γ₂.map ratToRealGL : Subgroup (GL (Fin 2) ℝ))) := by
    have heq : ∀ v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹,
        (QuotientGroup.mk (r v)⁻¹ : _) =
          decompQuotientEquivMapOfInjective ratToRealGL hinj Γ₂ Γ₁
            (D.out : GL (Fin 2) ℚ)⁻¹ v := by
      intro v
      rw [hrinv, ← decompQuotientEquivMapOfInjective_mk]
      exact congrArg _ v.out_eq
    -- `map_inv` is definitional for `Units.map`, so the equiv's target type is already the one
    -- `iUnion_mul_smul_of_transversal` asks for; only the function needs transporting.
    exact funext heq ▸ (decompQuotientEquivMapOfInjective ratToRealGL hinj Γ₂ Γ₁
      (D.out : GL (Fin 2) ℚ)⁻¹).bijective
  have := hS.iUnion_mul_smul_of_transversal (ratToRealGL (D.out : GL (Fin 2) ℚ)) hδ
    (r := r) (fun v ↦ hnull v) hbij
  simpa only [hset] using this

end HeckeRing.GL2
