/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.Cusps
public import TauCeti.NumberTheory.ModularForms.Basic
public import TauCeti.NumberTheory.ModularForms.Fricke.Conjugation

/-!
# The Fricke operator on modular and cusp forms

The Fricke matrix `W = !![0, -1; N, 0]` of `TauCeti/NumberTheory/ModularForms/Fricke/Matrix.lean`
normalizes `Γ₁(N)`, by `frickeConjSL_mem_Gamma1` of
`TauCeti/NumberTheory/ModularForms/Fricke/Conjugation.lean`. Slashing by `W` therefore preserves
weight-`k` invariance under `Γ₁(N)`, and this file packages `f ↦ f ∣[k] W` as the **Fricke
operator** `W_N`, a `ℂ`-linear endomorphism of `M_k(Γ₁(N))` and of `S_k(Γ₁(N))`.

## Main results

* `TauCeti.frickeSlash_invariant`: slashing by `W` preserves `Γ₁(N)`-invariance.

## Main definitions

* `TauCeti.frickeOperator`: the Fricke operator on `M_k(Γ₁(N))`.
* `TauCeti.frickeOperatorCusp`: the Fricke operator on `S_k(Γ₁(N))`.

## The base field

`frickeGL` is parameterized by the field it is read in, so the slash here is by `frickeGL ℝ N`
directly, with no transport from `GL (Fin 2) ℚ`. The one place a rational model is still needed
is `frickeGL_isCusp_smul`: mathlib detects a cusp of `SL₂(ℤ)` by rationality of the point
(`isCusp_SL2Z_iff`), so the image point has to be exhibited as a rational one, and
`map_ratCast_frickeGL` identifies `W` over `ℝ` as the base change of `W` over `ℚ` for that step.

## `ℂ`-linearity

Scalars commute past a slash only on the positive-determinant branch — mathlib's
`ModularForm.smul_slash` otherwise carries the twist `σ A c`, which is complex conjugation.
`det W = N > 0`, so `ModularForm.smul_slash_of_det_pos` of
`TauCeti/NumberTheory/ModularForms/Basic.lean` applies and gives `map_smul'` for both operators.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Fricke.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `340875adfb2`, Apache-2.0, Chris Birkbeck), realizing part of Layer 6 of the ModularForms
roadmap.

AINTLIB slashes by `(frickeGL N : GL (Fin 2) ℚ)` and lets the coercion to `GL (Fin 2) ℝ` do the
work, so its `frickeSlash_invariant` consumes the hand-transported identity
`glMap_frickeGL_mul_mapGL`; here the identity is available over `ℝ` as an instance of
`frickeGL_mul_mapGL`, so no transport lemma appears. For the same reason AINTLIB's
`frickeGL_det_pos` is `val_det_frickeGL_pos` read at `ℝ`.

AINTLIB proves `ℂ`-linearity with its own `smul_slash_pos_det`; the corresponding TauCeti lemma
`ModularForm.smul_slash_of_det_pos` was already on hand, and is more general (any scalar `α`
acting on `ℂ` by an `IsScalarTower`, rather than `ℂ` itself).

The diamond-shift theorem `frickeOperator_diamondOp` of the source (`W ∘ ⟨d⟩ = ⟨d⁻¹⟩ ∘ W`) is
deliberately *not* ported here: it is stated through AINTLIB's `Gamma0MapUnits`, the unit-valued
refinement of mathlib's `CongruenceSubgroup.Gamma0Map`, which TauCeti does not have — the same
definition whose absence already kept `Gamma0MapUnits_frickeConjSL` out of
`Fricke/Conjugation.lean`.
It belongs with that definition and with the character-space transport, not here.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- `W` over `ℝ` is the base change of `W` over `ℚ`: both are `!![0, -1; N, 0]`. -/
private theorem map_ratCast_frickeGL :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (frickeGL ℚ N) = frickeGL ℝ N := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_frickeGL]

/-- The determinant of `W`, read as a matrix over `ℝ`, is positive. This is the form the
positive-determinant slash lemmas consume. -/
private theorem det_coe_frickeGL_real_pos :
    0 < ((frickeGL ℝ N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact val_det_frickeGL_pos

/-- **Slash-invariance of `f ∣[k] W` under `Γ₁(N)`**: if `f` is invariant under the image of
`Γ₁(N)` in `GL (Fin 2) ℝ`, then so is `f ∣[k] W`. This is `frickeConjSL_mem_Gamma1` — that `W`
conjugates `Γ₁(N)` into itself — read through the slash action. -/
public theorem frickeSlash_invariant {f : ℍ → ℂ} (hf : ∀ γ ∈ (Gamma1 N).map (mapGL ℝ), f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ (Gamma1 N).map (mapGL ℝ)) :
    (f ∣[k] frickeGL ℝ N) ∣[k] γ = f ∣[k] frickeGL ℝ N := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  rw [← SlashAction.slash_mul, frickeGL_mul_mapGL ℝ ⟨σ, Gamma1_in_Gamma0 N hσ⟩,
    SlashAction.slash_mul, hf _ (Subgroup.mem_map.mpr ⟨_, frickeConjSL_mem_Gamma1 σ hσ, rfl⟩)]

/-- **Cusp transport for `W`**: a cusp of `Γ₁(N)` is carried by `W` to another cusp of `Γ₁(N)`.
Cusps of `SL₂(ℤ)` are exactly the rational points of `OnePoint ℝ`, and `W` has rational entries,
so it permutes them; the statement descends from `SL₂(ℤ)` to `Γ₁(N)` because the latter has
finite index. -/
private theorem frickeGL_isCusp_smul {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    IsCusp (frickeGL ℝ N • c) ((Gamma1 N).map (mapGL ℝ)) := by
  have hc_SL : IsCusp c ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) :=
    hc.mono (Subgroup.map_mono le_top)
  rw [← MonoidHom.range_eq_map] at hc_SL
  have hsmul_SL : IsCusp (frickeGL ℝ N • c) (mapGL ℝ : SL(2, ℤ) →* _).range := by
    rw [isCusp_SL2Z_iff] at hc_SL ⊢
    obtain ⟨q, rfl⟩ := hc_SL
    refine ⟨frickeGL ℚ N • q, ?_⟩
    rw [← Rat.coe_castHom, OnePoint.map_smul, map_ratCast_frickeGL]
  rw [MonoidHom.range_eq_map] at hsmul_SL
  have : ((Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex
      ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) := ⟨by
    rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
      Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero⟩
  exact hsmul_SL.of_isFiniteRelIndex

/-- Boundedness at the cusps transports along `W`, by `frickeGL_isCusp_smul`. -/
private theorem frickeGL_bdd_at_cusps (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsBoundedAt (⇑f ∣[k] frickeGL ℝ N) k :=
  OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' (frickeGL_isCusp_smul hc))

/-- **The Fricke operator `W_N`** on `M_k(Γ₁(N))`: `f ↦ f ∣[k] W` for `W = !![0, -1; N, 0]`.
Slash-invariance comes from `W` normalizing `Γ₁(N)` (`frickeSlash_invariant`) and boundedness at
the cusps from `frickeGL_isCusp_smul`; it is `ℂ`-linear because `det W = N > 0`. -/
public noncomputable def frickeOperator (k : ℤ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
        { toFun := ⇑f ∣[k] frickeGL ℝ N
          slash_action_eq' _ hγ :=
            frickeSlash_invariant
              (fun _ hδ ↦ SlashInvariantFormClass.slash_action_eq f _ hδ) hγ }
      holo' := (ModularFormClass.holo f).slash k _
      bdd_at_cusps' hc := frickeGL_bdd_at_cusps f hc }
  map_add' f g := by
    ext z
    simp only [FunLike.coe_add, SlashAction.add_slash, _root_.add_apply]
    rfl
  map_smul' c f := by
    ext z
    simp only [FunLike.coe_smul, ModularForm.smul_slash_of_det_pos k det_coe_frickeGL_real_pos,
      RingHom.id_apply, _root_.smul_apply, smul_eq_mul]
    rfl

@[simp]
public theorem frickeOperator_coe (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(frickeOperator (N := N) k f) : ℍ → ℂ) = ⇑f ∣[k] frickeGL ℝ N := (rfl)

/-- **The Fricke operator `W_N` on cusp forms** `S_k(Γ₁(N))`: the cusp-form counterpart of
`frickeOperator`, vanishing at the cusps transporting through `frickeGL_isCusp_smul` exactly as
boundedness does. -/
public noncomputable def frickeOperatorCusp (k : ℤ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
        { toFun := ⇑f ∣[k] frickeGL ℝ N
          slash_action_eq' _ hγ :=
            frickeSlash_invariant
              (fun _ hδ ↦ SlashInvariantFormClass.slash_action_eq f _ hδ) hγ }
      holo' := (CuspFormClass.holo f).slash k _
      zero_at_cusps' hc :=
        OnePoint.IsZeroAt.smul_iff.mp (f.zero_at_cusps' (frickeGL_isCusp_smul hc)) }
  map_add' f g := by
    ext z
    simp only [FunLike.coe_add, SlashAction.add_slash, _root_.add_apply]
    rfl
  map_smul' c f := by
    ext z
    simp only [FunLike.coe_smul, ModularForm.smul_slash_of_det_pos k det_coe_frickeGL_real_pos,
      RingHom.id_apply, _root_.smul_apply, smul_eq_mul]
    rfl

@[simp]
public theorem frickeOperatorCusp_coe (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(frickeOperatorCusp (N := N) k f) : ℍ → ℂ) = ⇑f ∣[k] frickeGL ℝ N := (rfl)

end TauCeti
