/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# Slash invariance along translates

The level-lowering half of the conductor theorem starts from a function `f : ℍ → ℂ` that is only
known to be periodic, `f ∣[k] T = f`, together with a transformation law for `f` under the
conjugates `conjScale l γ` of `Γ₀(N)` matrices. The `T`-factorisation of `Γ₀(N / l)` writes an
arbitrary element of that group as `T ^ i * conjScale l γ c * T ^ j`, so reading the
transformation law off a `Γ₀(N / l)` element needs the law to survive multiplication by integer
powers of `T` on both sides.

Neither result below sees any of that context: the middle factor is an arbitrary element of
`SL(2, ℤ)`, and the eigenvalue is an arbitrary scalar. That matches
`TauCeti.slash_conjScale_eq_smul_of_slash_scaleGL`, which is likewise stated for an arbitrary
scalar, and it means the conductor application is a specialisation rather than the statement.

## Main results

* `TauCeti.slash_zpow_eq_self_of_slash_eq`: slash invariance passes to every integer power,
  `f ∣[k] γ = f → f ∣[k] γ ^ j = f`. The matrices fixing `f` form a subgroup, so this is
  `zpow_mem` rather than an induction on `j`.
* `TauCeti.slash_T_zpow_mul_mul_T_zpow_eq_smul`: an eigenvalue law survives translation on both
  sides, `f ∣[k] (T ^ i * γ * T ^ j) = z • f`. Only `T` needs to fix `f`; since `T` has
  determinant one, the automorphism `σ` attached to it is the identity, so the eigenvalue does
  not conjugate.

## References

* The `T`-conjugation block is ported from the AINTLIB `LeanModularForms` project
  (Chris Birkbeck), [`Eigenforms/ConductorTheorem.lean`](https://github.com/CBirkbeck/AINTLIB),
  declarations `slash_T_zpow_eq_self_of_slash_T_eq` (:176) and `conductor_slash_T_conj_eq`
  (:186), Apache-2.0 at commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`.

  Three departures, all toward generality. The source states the second result for a modular
  form `g` lying in `modFormCharSpace k χ.toUnitHom` with `⇑g = levelRaiseFun l k f`, and derives
  the conjugate law inside the proof from its own `conductor_slash_eq` (:84); `main` already has
  that derivation, in the more general eigenvalue form
  `slash_conjScale_eq_smul_of_slash_scaleGL`, so the character hypotheses are dropped and the
  conjugate law is taken as a hypothesis on an arbitrary scalar `z`. The source then fixes the
  middle factor to be `levelRaiseConjOfDvd l γ h`; nothing in the argument uses that shape, so it
  is an arbitrary `SL(2, ℤ)` element here. Finally the source's first result is stated for `T`,
  where the subgroup argument gives every element at once.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {k : ℤ}

/-- The matrices whose slash action fixes a given function, as a subgroup of `SL(2, ℤ)`. It
exists so that invariance can be pushed to integer powers by `zpow_mem`. -/
private def slashStabilizer (k : ℤ) (f : ℍ → ℂ) : Subgroup SL(2, ℤ) where
  carrier := {γ | f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = f}
  one_mem' := by simp only [Set.mem_ofPred_eq, map_one, SlashAction.slash_one]
  mul_mem' := fun {a b} ha hb ↦ by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, SlashAction.slash_mul, ha, hb]
  inv_mem' := fun {a} ha ↦ by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have hinv : (mapGL ℝ a : GL (Fin 2) ℝ) * mapGL ℝ a⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have h := SlashAction.slash_mul k (mapGL ℝ a) (mapGL ℝ a⁻¹) f
    rw [hinv, SlashAction.slash_one, ha] at h
    exact h.symm

/-- Membership in `slashStabilizer` unfolds to the slash identity it is defined by. -/
private lemma mem_slashStabilizer {f : ℍ → ℂ} {γ : SL(2, ℤ)} :
    γ ∈ slashStabilizer k f ↔ f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = f := Iff.rfl

/-- **Slash invariance passes to every integer power.** If `f ∣[k] γ = f` then
`f ∣[k] γ ^ j = f` for every `j : ℤ`, because the matrices fixing `f` form a subgroup. -/
lemma slash_zpow_eq_self_of_slash_eq (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ))
    (hf : f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = f) (j : ℤ) :
    f ∣[k] (mapGL ℝ (γ ^ j) : GL (Fin 2) ℝ) = f :=
  mem_slashStabilizer.mp (zpow_mem (mem_slashStabilizer.mpr hf) j)

/-- **An eigenvalue law survives translation on both sides.** If `f` is fixed by `T` and slashing
by `γ` multiplies it by `z`, then slashing by `T ^ i * γ * T ^ j` does too. Applied to the
`T`-factorisation of `Γ₀(N / l)`, with `γ` the conjugate `conjScale l γ' c`, this is what
transports a transformation law down a level. -/
lemma slash_T_zpow_mul_mul_T_zpow_eq_smul (f : ℍ → ℂ)
    (hf : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) (γ : SL(2, ℤ)) {z : ℂ}
    (hγ : f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = z • f) (i j : ℤ) :
    f ∣[k] (mapGL ℝ (ModularGroup.T ^ i * γ * ModularGroup.T ^ j) : GL (Fin 2) ℝ) = z • f := by
  have hdet : (0 : ℝ) <
      (Matrix.GeneralLinearGroup.det (mapGL ℝ (ModularGroup.T ^ j))).val := by
    rw [Matrix.SpecialLinearGroup.det_mapGL]; norm_num
  rw [map_mul, map_mul, SlashAction.slash_mul, SlashAction.slash_mul,
    slash_zpow_eq_self_of_slash_eq k f ModularGroup.T hf i, hγ, _root_.ModularForm.smul_slash,
    σ_eq_refl_of_det_pos hdet, ContinuousAlgEquiv.refl_apply,
    slash_zpow_eq_self_of_slash_eq k f ModularGroup.T hf j]

end TauCeti
