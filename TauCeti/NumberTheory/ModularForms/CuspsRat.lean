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
action of every element of `GL (Fin 2) ℚ`, not merely under `𝒮ℒ` itself.

This is what the Hecke operators need. Their representatives have determinant `p > 1`, so they
lie outside `𝒮ℒ` and `OnePoint.IsCusp.smul_of_mem` does not apply; the general
`OnePoint.IsCusp.smul` only places the image cusp in a *conjugate* subgroup. Going through the
rational description avoids conjugation altogether.

## Main results

* `isCusp_smul_map_ratCast`: if `c` is a cusp of `𝒮ℒ` then so is `g • c`, for any
  `g : GL (Fin 2) ℚ` pushed forward to `ℝ`.
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

/-- **Rational matrices carry cusps of `𝒮ℒ` to cusps of `𝒮ℒ`.** A cusp is a rational point of
`OnePoint ℝ`, and `g` has rational entries. -/
lemma isCusp_smul_map_ratCast {c : OnePoint ℝ} (g : GL (Fin 2) ℚ) (hc : IsCusp c 𝒮ℒ) :
    IsCusp (g.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨x, rfl⟩ := hc
  exact ⟨g • x, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

end
