/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# The weight-`k` slash action of `GL(2, ℚ)`

Mathlib defines the slash action of `GL(2, ℝ)` on `ℍ → ℂ` and specialises it to `SL(2, ℤ)`
through `monoidHomSlashAction`. The Hecke operators need the intermediate group: their coset
representatives are *rational* matrices of positive determinant — `Δ₀(N)` lives in `GL(2, ℚ)` —
and they are slashed against functions that are invariant under an integral congruence subgroup.

This file supplies that action, by the same mechanism Mathlib uses for `SL(2, ℤ)`: transport
along the entrywise map `GL(2, ℚ) →* GL(2, ℝ)`. It is a `scoped instance`, so a module that does
not want `f ∣[k] g` to elaborate at rational `g` simply does not open the scope.

`f ∣[k] g = f ∣[k] (g.map (algebraMap ℚ ℝ))` holds definitionally, so every `GL(2, ℝ)` lemma
applies after rewriting with `slash_def`; the point of the instance is that consumers need not
insert the coercion by hand.

## Main results

* `ModularForm.rat_slash_def`: the action is the real one at the mapped matrix.
* `ModularForm.det_ratToReal_pos`: positivity of the determinant survives the embedding.
* `ModularForm.smul_rat_slash_of_det_pos`: scalars pass through the slash of a
  positive-determinant rational matrix, with no `σ` twist.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
-/

public section

open Matrix UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace ModularForm

/-- The entrywise embedding `GL(2, ℚ) →* GL(2, ℝ)`, along which the slash action is
transported. -/
scoped notation "ratToReal" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

/-- The weight-`k` slash action of `GL(2, ℚ)`, induced from `GL(2, ℝ)` along `ℚ ↪ ℝ`. Scoped,
so it is opted into rather than imposed. -/
noncomputable scoped instance ratSlashAction : SlashAction ℤ (GL (Fin 2) ℚ) (ℍ → ℂ) :=
  monoidHomSlashAction ratToReal

/-- The rational slash action is the real one at the mapped matrix. Definitional, but named:
it is how every `GL(2, ℝ)` lemma is brought to bear. -/
lemma rat_slash_def (k : ℤ) (g : GL (Fin 2) ℚ) (f : ℍ → ℂ) :
    f ∣[k] g = f ∣[k] (ratToReal g) := (rfl)

/-- A rational matrix of positive determinant maps to a real one of positive determinant.
Stated with `Matrix.det`, the form `UpperHalfPlane.σ_eq_refl_of_det_pos` consumes. -/
lemma det_ratToReal_pos {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    0 < ((ratToReal g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.GeneralLinearGroup.val_map_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simpa using hg

/-- **Scalars pass through the slash of a positive-determinant rational matrix.** Mathlib's
`ModularForm.smul_slash` carries the twist `σ A c`, which is complex conjugation when the
determinant is negative; on the positive branch `σ` is the identity
(`UpperHalfPlane.σ_eq_refl_of_det_pos`) and the scalar simply commutes.

This is what makes a Hecke operator `ℂ`-linear: it is a sum of slashes by representatives of
positive determinant. -/
lemma smul_rat_slash_of_det_pos (k : ℤ) {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (f : ℍ → ℂ) (c : ℂ) :
    (c • f) ∣[k] g = c • (f ∣[k] g) := by
  rw [rat_slash_def, rat_slash_def, ModularForm.smul_slash,
    σ_eq_refl_of_det_pos (det_ratToReal_pos hg), ContinuousAlgEquiv.refl_apply]

end ModularForm
