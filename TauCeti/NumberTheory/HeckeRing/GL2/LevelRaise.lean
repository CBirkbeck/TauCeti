/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.RepresentationTheory.ClassicalGroups.Diagonal
public import TauCeti.NumberTheory.ModularForms.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.Analysis.Complex.Periodic

public section

/-!
# Level-raising operator for cusp forms (Miyake §4.6 Lemma 4.6.1)

The level-raising operator `ι_d : S_k(Γ₁(M)) → S_k(Γ₁(d·M))` sends a cusp
form `f` for `Γ₁(M)` to the cusp form `(ι_d f)(τ) = f(d·τ)` for the deeper
level `Γ₁(d·M)`, normalised so that the Fourier coefficient at `q^d`
equals the Fourier coefficient of `f` at `q`. In matrix form:
`ι_d f = d^{1-k} · (f ∣[k] [[d,0],[0,1]])`.

## Main definitions

* `levelRaiseMatrix d` — the matrix `α_d = [[d, 0], [0, 1]]` in `GL(2, ℝ)`.
* `levelRaiseFun d k f` — the level-raising operator at the function level.
* `levelRaiseConjOfDvd d γ hdvd` — the explicit `SL(2, ℤ)` element
  `α_d γ α_d⁻¹` constructed when `d ∣ γ.val 1 0`.
* `levelRaiseConj d M γ hγ` — specialisation of `levelRaiseConjOfDvd` to
  `γ ∈ Γ₁(d·M)` (where the divisibility is automatic).
* `levelRaise M d k` — the bundled `ℂ`-linear level-raising operator
  `S_k(Γ₁(M)) →ₗ[ℂ] S_k(Γ₁(d·M))`.
* `modularFormLevelRaise M d k` — the same operator on modular forms,
  `M_k(Γ₁(M)) →ₗ[ℂ] M_k(Γ₁(d·M))`.

## Main results

* `levelRaiseConj_mem_Gamma1` — the conjugate `α_d γ α_d⁻¹` lies in `Γ₁(M)` for
  `γ ∈ Γ₁(d·M)` (Miyake Lemma 4.6.1), which is what makes `levelRaise` well defined.
* `exists_T_levelRaiseConj_T_factor` — every `γ' ∈ Γ₀(N/l)` factors as
  `T^i · (α_l γ α_l⁻¹) · T^j` with `γ ∈ Γ₀(N)`.
* `qExpansion_modularFormLevelRaise_coeff'`, `qExpansion_one_modularFormLevelRaise_coeff` —
  the `q`-expansion of `ι_d f` is that of `f` reindexed by `d`.

## References

* Miyake, *Modular Forms*, §4.6 (Lemma 4.6.1, p.162).
* Diamond–Shurman, *A First Course in Modular Forms*, §5.7 (DS (5.16)).

Ported from Chris Birkbeck's AINTLIB formalization,
`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/LevelRaise.lean`
(<https://github.com/CBirkbeck/AINTLIB>).
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup CuspForm ModularFormClass
  UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

noncomputable section

namespace HeckeRing.GL2

/-- The level-raising matrix `α_d = [[d, 0], [0, 1]]` in `GL(2, ℝ)`. -/
def levelRaiseMatrix (d : ℕ) [NeZero d] : GL (Fin 2) ℝ :=
  TauCeti.diagGL ![Units.mk0 (d : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne d)), 1]

/-- The level-raising operator at the function level: `(ι_d f)(τ) = f(d·τ)`,
realised as `ι_d f = d^{1-k} · (f ∣[k] α_d)` (the `d^{1-k}` scalar cancels the
`det^{k-1}` factor in the slash action). -/
def levelRaiseFun (d : ℕ) [NeZero d] (k : ℤ) (f : UpperHalfPlane → ℂ) :
    UpperHalfPlane → ℂ :=
  ((d : ℂ) ^ (1 - k)) • (f ∣[k] levelRaiseMatrix d)

/-- The denominator of `levelRaiseMatrix l` at any point is `1` (bottom row
of `α_l` is `(0, 1)`). -/
lemma denom_levelRaiseMatrix (l : ℕ) [NeZero l] (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (levelRaiseMatrix l) (↑τ : ℂ) = 1 := by
  simp [UpperHalfPlane.denom, levelRaiseMatrix]

/-- The determinant of `levelRaiseMatrix l` is positive (it equals `l > 0`). -/
lemma levelRaiseMatrix_det_pos (l : ℕ) [NeZero l] :
    (0 : ℝ) < (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l) : ℝ) := by
  simp [levelRaiseMatrix,
    Nat.cast_pos.mpr (Nat.pos_of_neZero l)]

/-- The real absolute determinant of `levelRaiseMatrix l` is `l`. -/
lemma abs_levelRaiseMatrix_det_val (l : ℕ) [NeZero l] :
    |((Matrix.GeneralLinearGroup.det (levelRaiseMatrix l)) : ℝ)| = (l : ℝ) := by
  rw [abs_of_pos (levelRaiseMatrix_det_pos l)]
  simp [levelRaiseMatrix]

/-- The conjugation factor `σ` for `levelRaiseMatrix l` is the identity
(positive determinant). -/
lemma σ_levelRaiseMatrix (l : ℕ) [NeZero l] :
    UpperHalfPlane.σ (levelRaiseMatrix l) = ContinuousAlgEquiv.refl ℝ ℂ := by
  unfold UpperHalfPlane.σ; rw [if_pos (levelRaiseMatrix_det_pos l)]

/-- If `l ∣ N` then every `γ ∈ Γ₀(N)` has `l` dividing its lower-left entry. -/
lemma dvd_lower_left_of_dvd {l N : ℕ} (h_dvd : l ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) : (l : ℤ) ∣ γ.val 1 0 :=
  (Int.natCast_dvd_natCast.mpr h_dvd).trans
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ))
/-- Construction of `α_d γ α_d⁻¹` as an explicit `SL(2, ℤ)` element when
`d ∣ γ.val 1 0`. The formula `[[a, d*b], [c/d, e]]` is integer by hypothesis. -/
noncomputable def levelRaiseConjOfDvd (d : ℕ) (γ : SL(2, ℤ))
    (hdvd : (d : ℤ) ∣ γ.val 1 0) : SL(2, ℤ) :=
  ⟨!![γ.val 0 0, d * γ.val 0 1; γ.val 1 0 / d, γ.val 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (Matrix.det_fin_two γ.val).symm.trans γ.property -
      γ.val 0 1 * Int.ediv_mul_cancel hdvd⟩

/-- Construction of `α_d γ α_d⁻¹` as an explicit `SL(2, ℤ)` element when
`γ ∈ Γ₁(d*M)`. The formula `[[a, d*b], [c/d, e]]` is integer because `d ∣ c`. -/
noncomputable def levelRaiseConj (d M : ℕ) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma1 (d * M)) : SL(2, ℤ) :=
  levelRaiseConjOfDvd d γ (dvd_lower_left_of_dvd (dvd_mul_right d M) (Gamma1_in_Gamma0 _ hγ))

/-- The conjugated matrix is in `Γ₀(M)` when `γ ∈ Γ₀(d*M)`. The (1,0) entry of
`α_d γ α_d⁻¹` is `c/d`, which is divisible by `M` because `c` is divisible by `d*M`. -/
lemma levelRaiseConjOfDvd_mem_Gamma0 (d M : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 (d * M)) :
    levelRaiseConjOfDvd d γ (dvd_lower_left_of_dvd (dvd_mul_right d M) hγ) ∈ Gamma0 M := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.dvd_div_of_mul_dvd (by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ))

/-- The (1,1) entry of the conjugate equals the (1,1) entry of the original. -/
lemma levelRaiseConjOfDvd_lower_right (d : ℕ) (γ : SL(2, ℤ))
    (hdvd : (d : ℤ) ∣ γ.val 1 0) :
    (levelRaiseConjOfDvd d γ hdvd).val 1 1 = γ.val 1 1 :=
  -- the `(1,1)` slot of the defining matrix literal is literally `γ.val 1 1`
  (rfl)

/-- The matrix conjugation identity (in `GL(2, ℝ)`) for `levelRaiseConjOfDvd`:
`α_d * γ * α_d⁻¹ = (levelRaiseConjOfDvd d γ hdvd : GL₂(ℝ))`, equivalently
`levelRaiseMatrix d * mapGL ℝ γ =
mapGL ℝ (levelRaiseConjOfDvd d γ hdvd) * levelRaiseMatrix d`. -/
lemma levelRaiseMatrix_mul_mapGL (d : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hdvd : (d : ℤ) ∣ γ.val 1 0) :
    mapGL ℝ (levelRaiseConjOfDvd d γ hdvd) * levelRaiseMatrix d =
      levelRaiseMatrix d * mapGL ℝ γ := by
  have hdvd_real : ((d : ℕ) : ℝ) * (((γ.val 1 0 / (d : ℤ)) : ℤ) : ℝ) =
      ((γ.val 1 0 : ℤ) : ℝ) := by
    rw [mul_comm, ← Int.cast_natCast (R := ℝ), ← Int.cast_mul, Int.ediv_mul_cancel hdvd]
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, levelRaiseMatrix,
    Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [levelRaiseConjOfDvd, mul_comm, hdvd_real]

/-- The conjugated matrix is in `Γ₁(M)` (Miyake Lemma 4.6.1, conjugation step).

If `γ ∈ Γ₁(d*M)` then `α_d γ α_d⁻¹ ∈ Γ₁(M)`. -/
lemma levelRaiseConj_mem_Gamma1 (d M : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma1 (d * M)) :
    levelRaiseConj d M γ hγ ∈ Gamma1 M := by
  obtain ⟨ha, he, hc⟩ := (Gamma1_mem _ _).mp hγ
  -- the diagonal slots of the defining matrix literal are copied from `γ` unchanged,
  -- so both are true by `rfl`; only the off-diagonal entries are rescaled
  have h00 : ((levelRaiseConj d M γ hγ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
      γ.val 0 0 := (rfl)
  have h11 : ((levelRaiseConj d M γ hγ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
      γ.val 1 1 := levelRaiseConjOfDvd_lower_right d γ _
  refine (Gamma1_mem _ _).mpr
    ⟨by rw [h00]; simpa using congr_arg (ZMod.castHom (Nat.dvd_mul_left M d) (ZMod M)) ha,
     by rw [h11]; simpa using congr_arg (ZMod.castHom (Nat.dvd_mul_left M d) (ZMod M)) he,
     ?_⟩
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.dvd_div_of_mul_dvd (by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc)


open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open scoped MatrixGroups ModularForm Pointwise

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The conjugation inclusion `(Γ₁(d*M)).map (mapGL ℝ) ≤ α_d⁻¹ ((Γ₁(M)).map (mapGL ℝ)) α_d`.

This is the key inclusion that lets us restrict the translated cusp form. -/
lemma Gamma1_mul_le_conj (M d : ℕ) [NeZero d] :
    (Gamma1 (d * M)).map (mapGL ℝ) ≤
      ConjAct.toConjAct (levelRaiseMatrix d)⁻¹ • (Gamma1 M).map (mapGL ℝ) := by
  intro g hg
  obtain ⟨γ, hγ_mem, rfl⟩ := Subgroup.mem_map.mp hg
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨mapGL ℝ (levelRaiseConj d M γ hγ_mem),
    Subgroup.mem_map.mpr ⟨_, levelRaiseConj_mem_Gamma1 d M γ hγ_mem, rfl⟩, ?_⟩
  rw [ConjAct.toConjAct_smul, inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact levelRaiseMatrix_mul_mapGL d γ
    (dvd_lower_left_of_dvd (dvd_mul_right d M) (Gamma1_in_Gamma0 _ hγ_mem))

/-- The level-raising operator `ι_d : S_k(Γ₁(M)) → S_k(Γ₁(d*M))`, defined as
`(ι_d f)(τ) = f(d·τ)`, equivalently `d^{1-k} · (f ∣[k] [[d,0],[0,1]])`
(DS (5.16); Miyake §4.6 Lemma 4.6.1). -/
def levelRaise (M d : ℕ) [NeZero d] (k : ℤ) :
    CuspForm ((Gamma1 M).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 (d * M)).map (mapGL ℝ)) k where
  toFun f :=
    ((d : ℂ) ^ (1 - k)) •
      (CuspForm.translate f (levelRaiseMatrix d)).ofLe (Gamma1_mul_le_conj M d)
  map_add' f₁ f₂ := by
    ext z
    simp only [FunLike.coe_smul, CuspForm.coe_ofLe, CuspForm.coe_translate_gl,
      FunLike.coe_add, SlashAction.add_slash, Pi.add_apply, Pi.smul_apply, smul_add]
  map_smul' c f := by
    ext z
    simp only [FunLike.coe_smul, CuspForm.coe_ofLe, CuspForm.coe_translate_gl,
      ModularForm.smul_slash, σ_levelRaiseMatrix d, ContinuousAlgEquiv.refl_apply,
      Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- The `ModularForm` analogue of `levelRaise`:
`ι_d : M_k(Γ₁(M)) → M_k(Γ₁(d*M))`, sending `f ↦ d^{1-k} · (f ∣[k] α_d)` where
`α_d = [[d, 0], [0, 1]]`. The pointwise formula `(ι_d f)(τ) = f(d·τ)` is provided
by `modularFormLevelRaise_apply`. -/
def modularFormLevelRaise (M d : ℕ) [NeZero d] (k : ℤ) :
    ModularForm ((Gamma1 M).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 (d * M)).map (mapGL ℝ)) k where
  toFun f :=
    ((d : ℂ) ^ (1 - k)) •
      (ModularForm.translate f (levelRaiseMatrix d)).ofLe
        (Gamma1_mul_le_conj M d)
  map_add' f₁ f₂ := by
    ext z
    simp only [FunLike.coe_smul, ModularForm.coe_ofLe, ModularForm.coe_translate,
      FunLike.coe_add, SlashAction.add_slash, Pi.add_apply, Pi.smul_apply, smul_add]
  map_smul' c f := by
    ext z
    simp only [FunLike.coe_smul, ModularForm.coe_ofLe, ModularForm.coe_translate,
      ModularForm.smul_slash, σ_levelRaiseMatrix d, ContinuousAlgEquiv.refl_apply,
      Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- **Coercion of `modularFormLevelRaise` to `UpperHalfPlane → ℂ`.**

`⇑(modularFormLevelRaise M d k f) = d^{1-k} · (⇑f ∣[k] α_d) = levelRaiseFun d k ⇑f`. -/
@[simp]
lemma coe_modularFormLevelRaise (M d : ℕ) [NeZero d] (k : ℤ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ⇑(modularFormLevelRaise M d k f) = levelRaiseFun d k ⇑f := by
  simp only [modularFormLevelRaise, levelRaiseFun, LinearMap.coe_mk, AddHom.coe_mk,
    FunLike.coe_smul, ModularForm.coe_ofLe, ModularForm.coe_translate]

/-- **Down-conjugation bridge.** For `γ : SL(2, ℤ)` with `l ∣ γ.val 1 0` and
`γ̃ := levelRaiseConjOfDvd l γ hdvd = α_l γ α_l⁻¹`, the slash action by
`mapGL ℝ γ` on `levelRaiseFun l k f` equals the level-raise of the slash
action by `mapGL ℝ γ̃` on `f`. This is the slash-action incarnation of
`levelRaiseMatrix_mul_mapGL`. -/
lemma slash_mapGL_levelRaiseFun (l : ℕ) [NeZero l] (k : ℤ) (γ : SL(2, ℤ))
    (hdvd : (l : ℤ) ∣ γ.val 1 0) (f : UpperHalfPlane → ℂ) :
    levelRaiseFun l k f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) =
      levelRaiseFun l k
        (f ∣[k] (mapGL ℝ (levelRaiseConjOfDvd l γ hdvd) : GL (Fin 2) ℝ)) := by
  have hσγ := σ_mapGL_real_eq_refl γ
  -- `levelRaiseFun` is sealed (`public section`, no `@[expose]`), so `rw`/`simp` cannot
  -- unfold it; `change` states the defeq body directly, which is the only route in
  change ((l : ℂ) ^ (1 - k) • (f ∣[k] levelRaiseMatrix l)) ∣[k]
      (mapGL ℝ γ : GL (Fin 2) ℝ) = _
  rw [ModularForm.smul_slash, hσγ, ContinuousAlgEquiv.refl_apply, ← SlashAction.slash_mul,
    ← levelRaiseMatrix_mul_mapGL l γ hdvd, SlashAction.slash_mul]
  rfl

/-- **Pointwise evaluation of the level-raise operator.** `levelRaiseFun l k f`
evaluates to `f` at the scaled point `α_l • τ`; the `l^{1-k}` prefactor exactly
cancels the `l^{k-1}` factor from the slash action. -/
@[simp]
lemma levelRaiseFun_apply (l : ℕ) [NeZero l] (k : ℤ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    levelRaiseFun l k f τ = f ((levelRaiseMatrix l) • τ) := by
  -- same sealed-body situation as above: `change` supplies the defeq unfolding, then the
  -- coercion is pushed through the pointwise scalar action by `simp`
  change ((l : ℂ) ^ (1 - k)) • ((f ∣[k] levelRaiseMatrix l) τ) = _
  rw [ModularForm.slash_apply, σ_levelRaiseMatrix, ContinuousAlgEquiv.refl_apply,
    abs_levelRaiseMatrix_det_val, denom_levelRaiseMatrix, one_zpow, mul_one,
    smul_eq_mul, Complex.ofReal_natCast, mul_comm (f _), ← mul_assoc,
    ← zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne l))]
  norm_num

/-- The action of `levelRaiseMatrix l = [[l, 0], [0, 1]]` on `ℍ` is the diagonal
scaling `(α_l • τ : ℂ) = l · (↑τ : ℂ)`. -/
lemma coe_levelRaiseMatrix_smul (l : ℕ) [NeZero l] (τ : UpperHalfPlane) :
    ((levelRaiseMatrix l • τ : UpperHalfPlane) : ℂ) = (l : ℂ) * (↑τ : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (levelRaiseMatrix_det_pos l)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, levelRaiseMatrix]

/-- **Pointwise evaluation** of the `ModularForm` level-raising operator:
`(modularFormLevelRaise M d k f) τ = f (α_d • τ)`, where `α_d` acts as
`τ ↦ d · τ` on `ℍ`. -/
@[simp]
lemma modularFormLevelRaise_apply (M d : ℕ) [NeZero d] (k : ℤ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (τ : UpperHalfPlane) :
    modularFormLevelRaise M d k f τ = f ((levelRaiseMatrix d) • τ) := by
  rw [show (modularFormLevelRaise M d k f : UpperHalfPlane → ℂ) = levelRaiseFun d k ⇑f from
    coe_modularFormLevelRaise M d k f]
  exact levelRaiseFun_apply d k (⇑f) τ

/-- **Injectivity of `levelRaiseFun l k`.** If two functions `f₁, f₂ : ℍ → ℂ`
have the same level-raise, they are equal. -/
lemma levelRaiseFun_injective (l : ℕ) [NeZero l] (k : ℤ) :
    Function.Injective (levelRaiseFun (k := k) l) := by
  -- `levelRaiseFun` is sealed, so route through its public evaluation equation: pointwise the
  -- `l^{1-k}` prefactor cancels, leaving precomposition by the (bijective) action of `α_l`
  have h : levelRaiseFun (k := k) l =
      fun f : UpperHalfPlane → ℂ ↦ f ∘ (levelRaiseMatrix l • ·) :=
    funext fun f ↦ funext fun τ ↦ levelRaiseFun_apply l k f τ
  rw [h]
  exact (MulAction.bijective (levelRaiseMatrix l)).surjective.injective_comp_right

/-- **Coercion of the bundled `levelRaise` to its underlying function.**
`⇑(levelRaise M d k g) = levelRaiseFun d k ⇑g` (definitional). -/
@[simp]
lemma coe_levelRaise (M d : ℕ) [NeZero d] (k : ℤ)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (⇑(levelRaise M d k g) : UpperHalfPlane → ℂ) = levelRaiseFun d k ⇑g := by
  simp only [levelRaise, levelRaiseFun, LinearMap.coe_mk, AddHom.coe_mk,
    FunLike.coe_smul, CuspForm.coe_ofLe, CuspForm.coe_translate_gl]

/-- **Associativity of the diagonal scaling action.** Acting by `α_{d'}` after
`α_d` equals acting by `α_{d·d'}`: both send `τ` to the upper-half-plane point with
complex value `(d·d')·τ`. -/
lemma levelRaiseMatrix_smul_levelRaiseMatrix_smul (d d' : ℕ) [NeZero d] [NeZero d']
    (τ : UpperHalfPlane) :
    levelRaiseMatrix d' • (levelRaiseMatrix d • τ) = levelRaiseMatrix (d * d') • τ := by
  apply UpperHalfPlane.ext
  rw [coe_levelRaiseMatrix_smul, coe_levelRaiseMatrix_smul, coe_levelRaiseMatrix_smul]
  push_cast
  ring

/-- **Associativity of `levelRaiseFun` (function level).** Raising by `d'` and then by `d`
equals raising by `d·d'` directly: `(ι_d ∘ ι_{d'}) f = ι_{d·d'} f`. The order of the
diagonal matrices does not matter (they commute), so `d·d'` appears. -/
lemma levelRaiseFun_levelRaiseFun (d d' : ℕ) [NeZero d] [NeZero d'] (k : ℤ)
    (f : UpperHalfPlane → ℂ) :
    levelRaiseFun d k (levelRaiseFun d' k f) = levelRaiseFun (d * d') k f := by
  funext τ
  rw [levelRaiseFun_apply, levelRaiseFun_apply, levelRaiseFun_apply,
    levelRaiseMatrix_smul_levelRaiseMatrix_smul]

/-- **Associativity of the bundled `levelRaise` operator.** Raising a cusp form `h` from
level `M'` to `M = e·M'` and then to `d·M`, equals raising it directly from `M'` to
`(d·e)·M'`.  Both produce a cusp form at level `d·M = (d·e)·M'`, identified via the level
equality `(d·e)·M' = d·M`, which follows from `heq1` by associativity.  This is the
algebraic core that folds two iterated level-raises into a single one
(Diamond–Shurman §5.6 Exercise 5.6.2; Miyake §4.6). -/
lemma levelRaise_levelRaise {M' : ℕ} {e : ℕ} [NeZero e] {M : ℕ}
    {d : ℕ} [NeZero d] {k : ℤ}
    (h : CuspForm ((Gamma1 M').map (mapGL ℝ)) k) (heq1 : e * M' = M) :
    levelRaise M d k (CuspForm.mcast (Γ' := (Gamma1 M).map (mapGL ℝ)) rfl
        (levelRaise M' e k h) (by rw [heq1])) =
      CuspForm.mcast (Γ' := (Gamma1 (d * M)).map (mapGL ℝ)) rfl
        (levelRaise M' (d * e) k h) (by subst heq1; rw [mul_assoc]) := by
  subst heq1
  apply CuspForm.ext
  intro τ
  simp only [CuspForm.mcast_apply, coe_levelRaise]
  -- `CuspForm.mcast` transports along a level equality but keeps the underlying function,
  -- so the two sides are defeq; no rewrite exists to witness that, hence `change`
  change levelRaiseFun d k (⇑((levelRaise M' e k) h)) τ = _
  simp only [coe_levelRaise]
  rw [levelRaiseFun_levelRaiseFun]

private noncomputable def primeProductCoprime (a : ℤ) (l : ℕ) : ℤ :=
  ((l.primeFactors.filter (fun (p : ℕ) ↦ ¬ ((p : ℤ) ∣ a))).prod id : ℕ)

private lemma dvd_primeProductCoprime_of_not_dvd
    {a : ℤ} {l : ℕ} {p : ℕ} (hp : p ∈ l.primeFactors) (hpa : ¬ ((p : ℤ) ∣ a)) :
    (p : ℤ) ∣ primeProductCoprime a l := by
  unfold primeProductCoprime
  exact_mod_cast Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨hp, hpa⟩)

private lemma not_dvd_primeProductCoprime_of_dvd
    {a : ℤ} {l : ℕ} {p : ℕ} (hp_prime : p.Prime) (hpa : (p : ℤ) ∣ a) :
    ¬ ((p : ℤ) ∣ primeProductCoprime a l) := by
  unfold primeProductCoprime
  intro h_dvd
  obtain ⟨q, hq_mem, hq_dvd⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp_prime) id).mp
    (by exact_mod_cast h_dvd)
  obtain ⟨hq_pf, hqa⟩ := Finset.mem_filter.mp hq_mem
  exact hqa ((Nat.prime_dvd_prime_iff_eq hp_prime
    (Nat.prime_of_mem_primeFactors hq_pf)).mp hq_dvd ▸ hpa)

private lemma exists_shift_isCoprime (a c : ℤ) (l : ℕ) [NeZero l]
    (hac : IsCoprime a c) :
    IsCoprime (a - primeProductCoprime a l * c) (l : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd, Int.natAbs_natCast]
  by_contra h_ne_one
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd h_ne_one
  rw [Nat.dvd_gcd_iff] at hp_dvd
  obtain ⟨hp_dvd_x, hp_dvd_l⟩ := hp_dvd
  have hp_dvd_x_int : (p : ℤ) ∣ (a - primeProductCoprime a l * c) := by
    rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
  have hp_isPrime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
  by_cases hpa : (p : ℤ) ∣ a
  · rcases hp_isPrime.dvd_mul.mp (by simpa using dvd_sub hpa hp_dvd_x_int) with h | h
    · exact not_dvd_primeProductCoprime_of_dvd hp_prime hpa h
    · exact hp_isPrime.not_unit (hac.isUnit_of_dvd' hpa h)
  · refine hpa ?_
    simpa using dvd_add hp_dvd_x_int
      ((dvd_primeProductCoprime_of_not_dvd
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd_l, NeZero.ne l⟩) hpa).mul_right c)

private lemma eq_T_zpow_mul_levelRaiseConj_mul_T_zpow
    (l : ℕ) [NeZero l] (a b c d i j k : ℤ) (M γ : SL(2, ℤ))
    (hMval : (M.val : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d])
    (hγval : (γ.val : Matrix (Fin 2) (Fin 2) ℤ) = !![a - i * c, k; (l : ℤ) * c, d - c * j])
    (hk : b - i * d - j * (a - i * c) = (l : ℤ) * k)
    (hdvd : (l : ℤ) ∣ γ.val 1 0) :
    M = ModularGroup.T ^ i * levelRaiseConjOfDvd l γ hdvd * ModularGroup.T ^ j := by
  apply Subtype.ext
  rw [hMval, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.coe_T_zpow, ModularGroup.coe_T_zpow]
  apply Matrix.ext
  intro p q
  fin_cases p <;> fin_cases q <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, levelRaiseConjOfDvd, hγval,
      Int.mul_ediv_cancel_left c (Nat.cast_ne_zero.mpr (NeZero.ne l))];
     try linear_combination hk)

/-- **Lower-level T-factorisation.** Every `γ' ∈ Γ₀(N/l)` can be written as
`T^i · (levelRaiseConjOfDvd l γ ...) · T^j` for explicit integers `i, j`
and an explicit `γ ∈ Γ₀(N)`. -/
lemma exists_T_levelRaiseConj_T_factor (l N : ℕ) [NeZero l] (h_dvd : l ∣ N)
    (γ' : SL(2, ℤ)) (hγ' : γ' ∈ Gamma0 (N / l)) :
    ∃ (i j : ℤ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N),
      γ' = ModularGroup.T ^ i *
            (levelRaiseConjOfDvd l γ (dvd_lower_left_of_dvd h_dvd hγ)) *
            ModularGroup.T ^ j ∧
      γ.val 1 1 = γ'.val 1 1 - γ'.val 1 0 * j := by
  set a := γ'.val 0 0
  set b := γ'.val 0 1
  set c := γ'.val 1 0
  set d := γ'.val 1 1
  have hdet : a * d - b * c = 1 := by
    have hp := γ'.property; rw [Matrix.det_fin_two] at hp; simpa using hp
  set i := primeProductCoprime a l
  set α := a - i * c
  set β := b - i * d
  -- `IsCoprime α l` is the Bézout identity `u·α + v·l = 1`; take `j := u·β`
  obtain ⟨u, v, huv⟩ := exists_shift_isCoprime a c l (γ'.isCoprime_col 0)
  set j := u * β with hj_def
  set k := β * v with hk_def
  have hk : β - j * α = (l : ℤ) * k := by
    simp only [hj_def, hk_def]; linear_combination -β * huv
  refine ⟨i, j, ⟨!![α, k; (l : ℤ) * c, d - c * j], ?det⟩,
    ?gamma0_mem, ?eq, ?diag⟩
  · rw [Matrix.det_fin_two_of]
    -- `Matrix.det_fin_two` leaves the entries as `!![…] i j` applications; `change` reads
    -- them off the literal, which no simp lemma does in one step
    change α * (d - c * j) - k * ((l : ℤ) * c) = 1
    linear_combination hdet + c * hk
  · refine Gamma0_mem.mpr ?_
    -- as above: the goal mentions the `(1,0)` entry of the matrix literal, and `change`
    -- names it rather than routing through `Matrix.cons_val` unfolding
    change (((l : ℤ) * c : ℤ) : ZMod N) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine Int.dvd_mul_of_div_dvd (Int.natCast_dvd_natCast.mpr h_dvd) ?_
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ')
    rwa [Int.natCast_div] at h
  · refine eq_T_zpow_mul_levelRaiseConj_mul_T_zpow l a b c d i j k γ' _
      (Matrix.eta_fin_two γ'.val) rfl ?_ _
    -- restating the goal as the β-scaled Bézout identity; `linear_combination` below needs
    -- this exact shape, which no rewrite produces from the coerced form
    change β - j * α = (l : ℤ) * k
    linear_combination hk
  · rfl

/-- **Sparse reindexing** of a HasSum over `(q^d)^j` as a HasSum over
`q^n` with zero coefficients at non-multiples of `d`.  For
`HasSum (j ↦ a j • (q ^ d) ^ j) S`, we obtain
`HasSum (n ↦ if d ∣ n then a (n / d) • q ^ n else 0) S`. -/
private lemma hasSum_pow_dvd_reindex {d : ℕ} (hd : 0 < d) {a : ℕ → ℂ} {q : ℂ}
    {S : ℂ} (h : HasSum (fun j : ℕ ↦ a j • (q ^ d) ^ j) S) :
    HasSum (fun n : ℕ ↦ if d ∣ n then a (n / d) • q ^ n else 0) S := by
  have hinj : Function.Injective (fun j : ℕ ↦ d * j) :=
    fun _ _ ↦ Nat.mul_left_cancel hd
  have h_zero : ∀ n : ℕ, n ∉ Set.range (fun j : ℕ ↦ d * j) →
      (fun n : ℕ ↦ if d ∣ n then a (n / d) • q ^ n else 0) n = 0 := by
    intro n hn
    refine if_neg fun hdvd ↦ ?_
    obtain ⟨j, rfl⟩ := hdvd
    exact hn ⟨j, rfl⟩
  have h_eq : ((fun n : ℕ ↦ if d ∣ n then a (n / d) • q ^ n else 0) ∘
      (fun j : ℕ ↦ d * j)) = fun j : ℕ ↦ a j • (q ^ d) ^ j := by
    funext j
    simp only [Function.comp_apply]
    rw [if_pos ⟨j, rfl⟩, Nat.mul_div_cancel_left j hd, pow_mul]
  rwa [← hinj.hasSum_iff h_zero, h_eq]

/-- **Period-general q-expansion scaling formula for `modularFormLevelRaise`.**
For an arbitrary positive period `h` that is a strict period of both `Γ₁(N)`
(the source level of `f`) — equivalently of `Γ₁(d · N)`, since both strict-period
groups are `zmultiples 1` — the
level-raised form `modularFormLevelRaise N d k f` has Fourier coefficients
given by `d`-dilation of those of `f`. -/
theorem qExpansion_modularFormLevelRaise_coeff'
    {N : ℕ} [NeZero N] {d : ℕ} [NeZero d] {k : ℤ} {h : ℝ}
    (hh_pos : 0 < h)
    (hh_period_N : h ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (UpperHalfPlane.qExpansion h ⇑(modularFormLevelRaise N d k f)).coeff n =
      if d ∣ n then (UpperHalfPlane.qExpansion h ⇑f).coeff (n / d) else 0 := by
  -- the strict-period groups of `Γ₁(N)` and `Γ₁(d·N)` are both `zmultiples 1`
  have hh_period_dN : h ∈ ((Gamma1 (d * N)).map (mapGL ℝ)).strictPeriods := by
    rw [strictPeriods_Gamma1] at hh_period_N ⊢; exact hh_period_N
  have h_sum_g : ∀ τ : UpperHalfPlane,
      HasSum (fun j : ℕ ↦
        (if d ∣ j then (UpperHalfPlane.qExpansion h ⇑f).coeff (j / d) else 0) •
          Function.Periodic.qParam h (τ : ℂ) ^ j)
        (modularFormLevelRaise N d k f τ) := fun τ ↦ by
    rw [modularFormLevelRaise_apply N d k f τ]
    have hfsum := ModularForm.hasSum_qExpansion f hh_pos hh_period_N
      (levelRaiseMatrix d • τ)
    simp only [← smul_eq_mul] at hfsum
    rw [coe_levelRaiseMatrix_smul d τ, TauCeti.Periodic.qParam_nat_mul_eq_pow h d (τ : ℂ)] at hfsum
    convert hasSum_pow_dvd_reindex (Nat.pos_of_neZero d) hfsum using 1
    funext j
    split_ifs with hdvd
    · rfl
    · simp
  exact (ModularFormClass.qExpansion_coeff_unique (f := modularFormLevelRaise N d k f)
    hh_pos hh_period_dN h_sum_g n).symm

/-- **Period-1 specialisation** of `qExpansion_modularFormLevelRaise_coeff'`:
the canonical Fourier expansion of `modularFormLevelRaise N d k f` is the
`d`-dilation of that of `f`. -/
theorem qExpansion_one_modularFormLevelRaise_coeff
    {N : ℕ} [NeZero N] {d : ℕ} [NeZero d] {k : ℤ}
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) ⇑(modularFormLevelRaise N d k f)).coeff n =
      if d ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f).coeff (n / d) else 0 :=
  qExpansion_modularFormLevelRaise_coeff' one_pos
    (by rw [strictPeriods_Gamma1]; exact ⟨1, by simp⟩) f n

/-- **Injectivity of the bundled cusp-form operator `levelRaise M d k`.** -/
lemma levelRaise_injective (M d : ℕ) [NeZero d] (k : ℤ) :
    Function.Injective (levelRaise M d k) := fun f g hfg ↦ by
  ext τ
  exact congrFun (levelRaiseFun_injective d k (by
    rw [← coe_levelRaise, ← coe_levelRaise, hfg])) τ

/-- **Injectivity of the bundled modular-form operator `modularFormLevelRaise M d k`.** -/
lemma modularFormLevelRaise_injective (M d : ℕ) [NeZero d] (k : ℤ) :
    Function.Injective (modularFormLevelRaise M d k) := fun f g hfg ↦ by
  ext τ
  exact congrFun (levelRaiseFun_injective d k (by
    rw [← coe_modularFormLevelRaise, ← coe_modularFormLevelRaise, hfg])) τ


end HeckeRing.GL2

end
