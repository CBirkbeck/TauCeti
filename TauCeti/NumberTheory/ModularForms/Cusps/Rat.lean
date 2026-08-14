/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Rational matrices carry cusps to cusps

A cusp of `𝒮ℒ` is exactly a rational point of `OnePoint ℝ` (`isCusp_SL2Z_iff`), and a matrix
over `ℚ` carries rational points to rational points. So the cusps of `𝒮ℒ` are stable under the
action of every element of `GL (Fin 2) ℚ`, not merely under `𝒮ℒ` itself — and for an arithmetic
`Γ` the cusps are the same set (`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`), so the statement
is given at that generality.

This is what the Hecke operators need. A rational representative need not lie in `𝒮ℒ` at all,
so `IsCusp.smul_of_mem` does not apply to it, and the general `IsCusp.smul`
only places the image cusp in a *conjugate* subgroup. Going through the rational description
avoids conjugation altogether, and asks nothing of the determinant beyond invertibility.

## Main results

* `IsCusp.smul_map_ratCast`: if `c` is a cusp of an arithmetic `Γ` then so is `g • c`, for any
  `g : GL (Fin 2) ℚ` pushed forward to `ℝ`.

## Provenance

The need for this lemma, and its role as the cusp-stability step under a Hecke representative,
come from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0),
`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, where it is packaged as `glMap_smul_isCusp_Gamma1`.

The **proof is not ported**: that declaration is specific to `Γ₁(N)`, whereas this one is stated
for an arbitrary arithmetic subgroup and reduces to `𝒮ℒ` through mathlib's
`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z` and the rational description of the cusps of
`𝒮ℒ` (`isCusp_SL2Z_iff`), neither of which the source uses.
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

/-- **Rational matrices carry cusps to cusps**, for any arithmetic `Γ`. Its cusps are those of
`𝒮ℒ`, which are the rational points of `OnePoint ℝ`, and `g` has rational entries. -/
lemma IsCusp.smul_map_ratCast {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {c : OnePoint ℝ}
    (hc : IsCusp c Γ) (g : GL (Fin 2) ℚ) :
    IsCusp (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g • c) Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨x, rfl⟩ := hc
  refine ⟨g • x, ?_⟩
  rw [show (algebraMap ℚ ℝ) = (Rat.castHom ℝ) from rfl, ← Rat.coe_castHom, OnePoint.map_smul]

end
