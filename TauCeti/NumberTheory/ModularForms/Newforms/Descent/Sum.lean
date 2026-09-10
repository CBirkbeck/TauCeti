/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Action

/-!
# The descent slash sum is `Γ₀(N / p)`-invariant

`Newforms/Descent/Action.lean` shows that, at a prime `p` with `p² ∣ N`, right multiplication by
`γ ∈ Γ₀(N / p)` permutes the family `descendMatrix p N` up to `Γ₀(N)`. This file draws the
consequence that the descent consumes: the sum of the slashes of `f` along the family is
`Γ₀(N / p)`-invariant whenever `f` is `Γ₀(N)`-invariant, with the same scalar.

## Main definitions

* `TauCeti.descendSlash`: `∑ v, f ∣[k] descendMatrix p N v`, the descent slash sum.

## Main results

* `TauCeti.descendSlash_slash_mapGL_of_mem_Gamma0`: for `p² ∣ N` and `γ ∈ Γ₀(N / p)`, if
  `f ∣[k] α = u • f` for every `α ∈ Γ₀(N)` then
  `descendSlash k p N f ∣[k] γ = u • descendSlash k p N f`.

## Scope

Only the `p² ∣ N` case, and only invariance under all of `Γ₀(N)` at once: the factorisation in
`Action.lean` records that the witness lies in `Γ₀(N)` but not its lower-right entry modulo `N`,
so the nebentypus transport that `HeckeSlash/UpperTri/Invariance.lean` derives for the
upper-triangular sum is not available here yet. The behaviour at cusps is likewise not claimed.

Corresponds to the `Γ₀(N / p)`-slash step of `miyake_hecke_descend_char` in the AINTLIB
`LeanModularForms` project (`LeanModularForms/StrongMultiplicityOne/HeckeDescent.lean`,
Chris Birkbeck, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>).
-/

public section

open CongruenceSubgroup HeckeRing.GL2 Matrix Matrix.SpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {p N : ℕ}

/-- **The descent slash sum**: `∑ v, f ∣[k] descendMatrix p N v`, over the whole family. -/
noncomputable def descendSlash (k : ℤ) (p N : ℕ) [NeZero p] (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ v : Fin (descendMatrixCount p N), f ∣[k] descendMatrix p N v

/-- The defining equation of `descendSlash`. Since `descendSlash` is not `@[expose]`, a
downstream module rewrites with this instead of unfolding the body. -/
lemma descendSlash_def (k : ℤ) (p N : ℕ) [NeZero p] (f : ℍ → ℂ) :
    descendSlash k p N f = ∑ v : Fin (descendMatrixCount p N), f ∣[k] descendMatrix p N v :=
  (rfl)

/-- The pointwise form of the defining equation. -/
lemma descendSlash_apply (k : ℤ) (p N : ℕ) [NeZero p] (f : ℍ → ℂ) (τ : ℍ) :
    descendSlash k p N f τ
      = ∑ v : Fin (descendMatrixCount p N), (f ∣[k] descendMatrix p N v) τ := by
  rw [descendSlash_def, Finset.sum_apply]

/-- **The descent slash sum is `Γ₀(N / p)`-invariant at `p² ∣ N`.** Slashing each summand by
`γ` lands on another member of the family, by `exists_mem_Gamma0_descendMatrix_mul`, at the cost
of a `Γ₀(N)` matrix that `f` absorbs as the scalar `u`; the family is then reindexed along the
bijection `descendShift`. -/
theorem descendSlash_slash_mapGL_of_mem_Gamma0 (k : ℤ) [NeZero p] (hpsq : p ^ 2 ∣ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p)) {f : ℍ → ℂ} {u : ℂ}
    (hf : ∀ α ∈ Gamma0 N, f ∣[k] (mapGL ℝ α : GL (Fin 2) ℝ) = u • f) :
    descendSlash k p N f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = u • descendSlash k p N f := by
  rw [descendSlash_def, SlashAction.sum_slash, Finset.smul_sum]
  have key : ∀ v : Fin (descendMatrixCount p N),
      (f ∣[k] descendMatrix p N v) ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ)
        = u • (f ∣[k] descendMatrix p N (descendShift p N hpsq γ v)) := fun v ↦ by
    obtain ⟨α, hα, hmul⟩ := exists_mem_Gamma0_descendMatrix_mul p N hpsq hγ v
    rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul, hf α hα,
      ModularForm.smul_slash_of_det_pos k (descendMatrix_det_pos p N _) f u]
  rw [Finset.sum_congr rfl fun v _ ↦ key v]
  exact Fintype.sum_bijective (descendShift p N hpsq γ)
    (descendShift_bijective hpsq
      (Gamma0_le_Gamma0_of_dvd (Nat.dvd_div_of_mul_dvd (by rwa [← pow_two])) hγ))
    (fun v ↦ u • (f ∣[k] descendMatrix p N (descendShift p N hpsq γ v)))
    (fun v ↦ u • (f ∣[k] descendMatrix p N v)) fun _ ↦ rfl

end TauCeti
