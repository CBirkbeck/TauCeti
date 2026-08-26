/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# Slash invariance along `T`-conjugates, for the level-lowering step

The level-lowering half of the conductor theorem starts from a function `f : ℍ → ℂ` that is
only known to be periodic, `f ∣[k] T = f`, together with a transformation law for `f` under the
conjugates `conjScale l γ` of `Γ₀(N)` matrices. The `T`-factorisation of `Γ₀(N / l)` writes an
arbitrary element of that group as `T ^ i * conjScale l γ c * T ^ j`, so to read the
transformation law off a `Γ₀(N / l)` element one needs the law to survive multiplication by
integer powers of `T` on both sides. That is what this file supplies.

Both results are stated for an arbitrary eigenvalue `z`, matching
`TauCeti.slash_conjScale_eq_smul_of_slash_scaleGL`: the nebentypus specialisation `z = χ d_γ`
is a corollary and is not needed here, so no Dirichlet character appears.

## Main results

* `TauCeti.slash_T_zpow_eq_self_of_slash_T_eq`: periodicity is inherited by every integer power,
  `f ∣[k] T = f → f ∣[k] T ^ j = f`. The powers form a subgroup of the slash stabiliser, so this
  is `zpow_mem` rather than an induction.
* `TauCeti.slash_T_zpow_mul_conjScale_mul_T_zpow_eq_smul`: the eigenvalue law survives the two
  translations, `f ∣[k] (T ^ i * conjScale l γ c * T ^ j) = z • f`. Since `T` has determinant
  one, the automorphism `σ` attached to it is the identity and the eigenvalue does not conjugate.

## References

* The `T`-conjugation block is ported from the AINTLIB `LeanModularForms` project
  (Chris Birkbeck), [`Eigenforms/ConductorTheorem.lean`](https://github.com/CBirkbeck/AINTLIB),
  declarations `slash_T_zpow_eq_self_of_slash_T_eq` (:176) and `conductor_slash_T_conj_eq`
  (:186), Apache-2.0 at commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`.

  Two departures, both toward existing API. The source states the second result for a modular
  form `g` lying in `modFormCharSpace k χ.toUnitHom` with `⇑g = levelRaiseFun l k f`, and
  derives the conjugate law inside the proof from its own `conductor_slash_eq` (:84); `main`
  already has that derivation, in the strictly more general eigenvalue form
  `slash_conjScale_eq_smul_of_slash_scaleGL`, so the character hypotheses are dropped and the
  conjugate law is taken as a hypothesis on an arbitrary scalar `z`. The source's
  `levelRaiseConjOfDvd l γ h` packages the lower-left divisibility as `l ∣ γ 1 0`; this file
  uses `main`'s `conjScale l γ c hc`, which carries the cofactor `c` explicitly.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {k : ℤ}

/-- The matrices whose slash action fixes a given function, as a subgroup of `SL(2, ℤ)`. It is
used only to see that the powers of `T` inherit periodicity. -/
private def slashStabilizer (k : ℤ) (f : ℍ → ℂ) : Subgroup SL(2, ℤ) where
  carrier := {γ | f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = f}
  one_mem' := by
    change f ∣[k] (mapGL ℝ (1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = f
    rw [map_one, SlashAction.slash_one]
  mul_mem' := fun {a b} ha hb ↦ by
    change f ∣[k] (mapGL ℝ (a * b) : GL (Fin 2) ℝ) = f
    rw [map_mul, SlashAction.slash_mul, ha, hb]
  inv_mem' := fun {a} ha ↦ by
    change f ∣[k] (mapGL ℝ a⁻¹ : GL (Fin 2) ℝ) = f
    have h := SlashAction.slash_mul k (mapGL ℝ a) (mapGL ℝ a⁻¹) f
    rw [show (mapGL ℝ a : GL (Fin 2) ℝ) * mapGL ℝ a⁻¹ = 1 by
        rw [← map_mul, mul_inv_cancel, map_one],
      SlashAction.slash_one, ha] at h
    exact h.symm

/-- **Periodicity passes to every integer power of `T`.** If `f ∣[k] T = f` then
`f ∣[k] T ^ j = f` for every `j : ℤ`. -/
lemma slash_T_zpow_eq_self_of_slash_T_eq (k : ℤ) (f : ℍ → ℂ)
    (hf : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) (j : ℤ) :
    f ∣[k] (mapGL ℝ (ModularGroup.T ^ j) : GL (Fin 2) ℝ) = f :=
  zpow_mem (show ModularGroup.T ∈ slashStabilizer k f from hf) j

/-- **The eigenvalue law survives the two translations.** If `f` is periodic and slashing by the
conjugate `conjScale l γ c` multiplies it by `z`, then slashing by `T ^ i * conjScale l γ c *
T ^ j` does too. Together with the `T`-factorisation of `Γ₀(N / l)` this is what transports a
transformation law down a level. -/
lemma slash_T_zpow_mul_conjScale_mul_T_zpow_eq_smul (l : ℕ) (f : ℍ → ℂ)
    (hf : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) (γ : SL(2, ℤ)) {c : ℤ}
    (hc : γ 1 0 = l * c) {z : ℂ}
    (hγ : f ∣[k] (mapGL ℝ (conjScale l γ c hc) : GL (Fin 2) ℝ) = z • f) (i j : ℤ) :
    f ∣[k] (mapGL ℝ (ModularGroup.T ^ i * conjScale l γ c hc * ModularGroup.T ^ j)
      : GL (Fin 2) ℝ) = z • f := by
  have hdet : (0 : ℝ) <
      (Matrix.GeneralLinearGroup.det (mapGL ℝ (ModularGroup.T ^ j))).val := by
    rw [Matrix.SpecialLinearGroup.det_mapGL]; norm_num
  rw [map_mul, map_mul, SlashAction.slash_mul, SlashAction.slash_mul,
    slash_T_zpow_eq_self_of_slash_T_eq k f hf i, hγ, _root_.ModularForm.smul_slash,
    σ_eq_refl_of_det_pos hdet, ContinuousAlgEquiv.refl_apply,
    slash_T_zpow_eq_self_of_slash_T_eq k f hf j]

end TauCeti
