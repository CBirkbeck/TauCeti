/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Sum

/-!
# The descent of a level-raise

For a prime `p ∣ N` and a cusp form `g` of level `Γ₁(N / p)`, every member of the descent family
`descendMatrix p N` slashes the level-raise `V_p g` (a form of level `Γ₁(N)`) back to `p⁻¹ • g`:
the upper-triangular members `!![1, b; 0, p]` because `(V_p g) ((τ + b) / p) = g (τ + b) = g τ`,
and the extra member because its `Γ₀(N / p)` factor lies in `Γ(N / p)`. So the descent slash
sum of `V_p g` is the scalar multiple `(|family| / p) • g`, with `|family| = p` when `p² ∣ N` and
`p + 1` otherwise. This is the computation behind the coefficient formula of the descent in
Miyake's proof of Lemma 4.6.14.

## Main results

* `TauCeti.coe_levelRaise_slash_upperTriRep`: `(V_p g) ∣[k] !![1, b; 0, p] = p⁻¹ • g`.
* `TauCeti.descendSlash_coe_levelRaise`: `descendSlash k p N (V_p g) = (|family| / p) • g`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/HeckeDescent.lean`
(`V_p_slash_descendCoset`, `V_p_slash_upper_aux`) and
`StrongMultiplicityOne/DescentCharSpace.lean` (`slash_sum_V_p_pointwise_eq_smul_g_low`). The
source's `modularFormLevelRaise` is this repository's `CuspForm.levelRaise`, and its
`descendCosetList` the family `descendMatrix`; the statements are re-proved on those.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.14.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {p N : ℕ} (k : ℤ)

/-- **An upper-triangular member of the family slashes a level-raise back to the form**: for `g`
of level `Γ₁(M)`, `(V_p g) ∣[k] !![1, b; 0, p] = p⁻¹ • g`, because `(V_p g) ((τ + b) / p)` is
`g (τ + b) = g τ`. -/
theorem coe_levelRaise_slash_upperTriRep {M : ℕ} [NeZero p] {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [𝒢.HasDetOne] (hle : 𝒢 ≤ ConjAct.toConjAct (scaleGL p)⁻¹ • (Gamma1 M).map (mapGL ℝ))
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (b : Fin p) :
    ⇑(CuspForm.levelRaise p hle g) ∣[k] (upperTriRep p b : GL (Fin 2) ℚ) = (p : ℂ)⁻¹ • ⇑g := by
  funext τ
  rw [slash_upperTriRep_apply, Pi.smul_apply, smul_eq_mul, CuspForm.levelRaise_apply]
  congr 1
  have hτ : scaleGL p • (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p b) • τ) =
      ((b : ℝ) +ᵥ τ : ℍ) := by
    ext1
    rw [coe_scaleGL_smul, coe_upperTriRep_smul, UpperHalfPlane.coe_vadd]
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    push_cast
    field_simp
    ring
  rw [hτ]
  exact SlashInvariantForm.vAdd_apply_of_mem_strictPeriods g τ
    (by simpa using AddSubgroup.nsmul_mem _ (one_mem_strictPeriods_Gamma1_map M) b.val)

/-- **The descent of a level-raise is a multiple of the form.** For `p ∣ N` prime and `g` of level
`Γ₁(N / p)`, `descendSlash k p N (V_p g) = (|family| / p) • g`: every member of the descent family
slashes `V_p g` to `p⁻¹ • g`. -/
theorem descendSlash_coe_levelRaise (hp : p.Prime) (hpN : p ∣ N)
    (g : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    descendSlash k p N ⇑(CuspForm.levelRaise p
        (Gamma1_map_le_conjAct_scaleGL_of_dvd (dvd_of_eq (Nat.mul_div_cancel' hpN))) g) =
      ((descendMatrixCount p N : ℂ) / p) • ⇑g := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hterm (v : Fin (descendMatrixCount p N)) :
      ⇑(CuspForm.levelRaise p
        (Gamma1_map_le_conjAct_scaleGL_of_dvd (dvd_of_eq (Nat.mul_div_cancel' hpN))) g) ∣[k]
          descendMatrix p N v = (p : ℂ)⁻¹ • ⇑g := by
    rcases lt_or_ge v.val p with hv | hv
    · rw [descendMatrix_of_lt hv, ← ModularForm.rat_slash, coe_levelRaise_slash_upperTriRep]
    · have hpsq : ¬ p ^ 2 ∣ N := fun h ↦ by
        have h1 := descendMatrixCount_of_sq_dvd h
        have h2 := v.isLt
        omega
      have hmem : descendExtraGamma p N ∈ Gamma1 (N / p) :=
        Gamma_le_Gamma1 (N / p)
          (Gamma_mem'.mpr (descendExtraGamma_map_intCast_zmod_div_eq_one hp hpN hpsq))
      rw [descendMatrix_eq_map, descendMatrixRat_of_le hv, map_mul, map_mapGL,
        SlashAction.slash_mul, ← ModularForm.rat_slash, coe_levelRaise_slash_upperTriRep,
        _root_.ModularForm.smul_slash, σ_mapGL_real_eq_refl, ContinuousAlgEquiv.refl_apply,
        SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hmem)]
  rw [descendSlash_def, Finset.sum_congr rfl fun v _ ↦ hterm v, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv]

end TauCeti
