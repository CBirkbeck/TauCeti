/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
public import TauCeti.RingTheory.PowerSeries.Support

/-!
# Power series supported on multiples of `d`

A power series is *supported on multiples of `d`* when every coefficient at an index not
divisible by `d` vanishes. This is the coefficient condition behind the Atkin–Lehner
description of the old subspace, of which this file proves the **forward inclusion**: the image
of the level-raising operator `V_d` is contained in the forms whose `q`-expansion is supported on
multiples of `d`. The converse — that every such form is in the image, which is what would make
the description exact — is not proved here and needs hypotheses this file does not carry.

The underlying power-series predicate is not stated here: it is generic material and lives in
`TauCeti/RingTheory/PowerSeries/Support.lean`, from which this file pulls
`supportedOnDvdSubmodule` back along the `q`-expansion.

## Main definitions

* `TauCeti.QExpansionSupportedOnDvd`: the support condition on the period-1 `q`-expansion of a
  cusp form.
* `TauCeti.qSupportedOnDvdSubmodule`: the cusp forms satisfying it, as the pullback of
  `TauCeti.supportedOnDvdSubmodule` along the `q`-expansion.

## Main results

* `CuspForm.isSupportedOnDvd_qExpansion_levelRaise` and its modular-form counterpart: the
  image of the level-raising operator `V_d` is supported on multiples of `d` — the forward half of
  the Atkin-Lehner description of the old subspace.
* `TauCeti.range_levelRaise_le_qSupportedOnDvdSubmodule`: the same statement for the `ℂ`-linear
  map, which is the shape `TauCeti.cuspFormsOld` is assembled from.

The source reaches the same conclusion through a cast between cusp-form spaces at equal levels
(`castCuspFormLinearEquiv`, `castLevelRaise`); that scaffolding is not ported, because this
repository's `CuspForm.levelRaiseₗ` accepts the divisibility hypothesis directly via
`Gamma1_map_le_conjAct_scaleGL_of_dvd` and lands at `Γ₁(N)` with no cast — exactly as
`cuspFormsOld` itself does.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/AtkinLehner.lean`, declarations
`QExpansionSupportedOnDvd`, `qSupportedOnDvdSubmodule`,
`levelRaise_mem_qSupportedOnDvdSubmodule`, `qExpansion_modularFormLevelRaise_isSupportedOnDvd`
and `qExpansion_levelRaise_isSupportedOnDvd`. The last two are renamed here to
`ModularForm.isSupportedOnDvd_qExpansion_levelRaise` and its cusp-form counterpart, and
`range_levelRaise_le_qSupportedOnDvdSubmodule` is the cast-free form of the source's
`range_castLevelRaise_le_qSupportedOnDvdSubmodule`. The underlying power-series predicate
`IsSupportedOnDvd` comes from the same source file but lives in
`TauCeti/RingTheory/PowerSeries/Support.lean` and is attributed there.

`qSupportedOnDvdSubmodule` is not a transcription: the source builds the submodule by hand,
discharging `zero_mem'`, `add_mem'` and `smul_mem'` from the predicate's closure lemmas, whereas
here it is the `comap` of `supportedOnDvdSubmodule` along the `q`-expansion, so that closure is
inherited from the linearity already bundled into `ModularForm.qExpansionLinearMap`.

The source's two forward lemmas are proved here directly from
`TauCeti.ModularForm.qExpansion_levelRaise_coeff` and its cusp-form counterpart, which
already state `aₙ(V_d f) = a_{n/d}(f)` for `d ∣ n` and `0` otherwise. The source has no cusp-form
coefficient lemma and reaches the cusp case by rebuilding the form as a `ModularForm` and
transporting along `qExpansion_ext2`; that detour is unnecessary here and is not ported. The
source's `modularFormLevelRaise`/`levelRaise` name pair is this repository's
`ModularForm.levelRaise`/`CuspForm.levelRaise`, distinguished by namespace rather than by prefix.

The source keeps the predicate and its modular-form consequences in one file, inside its
`HeckeRing.GL2.AtkinLehner` namespace. Here the predicate is a statement about power series
alone, so what the source keeps together is split across two files.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §5.7.
* Atkin–Lehner, *Hecke operators on* `Γ₀(m)`, Math. Ann. **185** (1970).
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Function
open scoped Manifold MatrixGroups ModularForm Pointwise

namespace TauCeti

section QExpansion

variable {M d : ℕ} [NeZero M] [NeZero d] {k : ℤ}

/-- A cusp form is **`q`-supported on multiples of `d`** when its period-1 `q`-expansion is. -/
def QExpansionSupportedOnDvd (d : ℕ) (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) : Prop :=
  IsSupportedOnDvd d (qExpansion 1 f)

omit [NeZero M] [NeZero d] in
/-- `QExpansionSupportedOnDvd` restated as an `Iff`, so it rewrites onto the power-series
predicate rather than being unfolded by defeq. -/
theorem qExpansionSupportedOnDvd_iff {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} :
    QExpansionSupportedOnDvd d f ↔ IsSupportedOnDvd d (qExpansion 1 f) := (Iff.rfl)

/-- `1` is a strict period of `Γ₁(M)` viewed in `GL (Fin 2) ℝ`, which is what makes the period-1
`q`-expansion additive and `ℂ`-homogeneous on this space. -/
private theorem one_mem_strictPeriods_Gamma1_map (M : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 M).map (mapGL ℝ)).strictPeriods := by
  simp [CongruenceSubgroup.strictPeriods_Gamma1]

/-- **Level-raising lands in the supported subspace, for modular forms.** The image `V_d g` has
`q`-expansion supported on multiples of `d`, because `aₙ(V_d g)` vanishes unless `d ∣ n`. -/
theorem _root_.ModularForm.isSupportedOnDvd_qExpansion_levelRaise (M : ℕ)
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    IsSupportedOnDvd d
      (qExpansion 1 (ModularForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL M d) g)) :=
  isSupportedOnDvd_iff.mpr fun n hn ↦ by
    simp [ModularForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map M)
      (one_mem_strictPeriods_Gamma1_map (d * M)) (Gamma1_map_le_conjAct_scaleGL M d) g n, hn]

/-- **Level-raising lands in the supported subspace, for cusp forms** — the forward half of the
Atkin-Lehner correspondence. -/
theorem _root_.CuspForm.isSupportedOnDvd_qExpansion_levelRaise (M : ℕ)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    IsSupportedOnDvd d
      (qExpansion 1 (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL M d) g)) :=
  isSupportedOnDvd_iff.mpr fun n hn ↦ by
    simp [CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map M)
      (one_mem_strictPeriods_Gamma1_map (d * M)) (Gamma1_map_le_conjAct_scaleGL M d) g n, hn]

/-- The submodule of cusp forms of level `Γ₁(M)` whose period-1 `q`-expansion is supported on
multiples of `d`, as the pullback of `supportedOnDvdSubmodule` along the `q`-expansion. Taking it
as a `comap` is what supplies closure under the module operations: that is the linearity already
bundled into `ModularForm.qExpansionLinearMap`, which holds because `1` is a strict period. -/
noncomputable def qSupportedOnDvdSubmodule (M : ℕ) (k : ℤ) (d : ℕ) :
    Submodule ℂ (CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :=
  (supportedOnDvdSubmodule ℂ d).comap
    ((ModularForm.qExpansionLinearMap one_pos (one_mem_strictPeriods_Gamma1_map M) k).comp
      CuspForm.toModularFormₗ)

omit [NeZero M] [NeZero d] in
/-- Membership in `qSupportedOnDvdSubmodule` is the `q`-support condition. -/
@[simp]
theorem mem_qSupportedOnDvdSubmodule {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} :
    f ∈ qSupportedOnDvdSubmodule M k d ↔ QExpansionSupportedOnDvd d f := by
  -- The `comap` is taken along the inclusion into `ModularForm`, which changes nothing
  -- pointwise, so the two `q`-expansions are the same function.
  have hcoe : ⇑(CuspForm.toModularFormₗ f) = ⇑f := funext fun _ ↦ rfl
  simp [qSupportedOnDvdSubmodule, QExpansionSupportedOnDvd,
    ModularForm.qExpansionLinearMap_apply, hcoe]

omit [NeZero M] [NeZero d] in
/-- Membership in `qSupportedOnDvdSubmodule`, spelled out on coefficients. -/
theorem mem_qSupportedOnDvdSubmodule_iff {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} :
    f ∈ qSupportedOnDvdSubmodule M k d ↔
      ∀ n : ℕ, ¬ d ∣ n → (qExpansion 1 f).coeff n = 0 :=
  mem_qSupportedOnDvdSubmodule.trans isSupportedOnDvd_iff

/-- **Level-raising into a divisible level lands in the supported submodule.** For `d * M ∣ N`,
the operator `V_d` carries `S_k(Γ₁(M))` into the cusp forms whose `q`-expansion is supported on
multiples of `d` — the forward half of the Atkin–Lehner description of the old subspace. -/
theorem levelRaise_mem_qSupportedOnDvdSubmodule {N : ℕ} (M : ℕ)
    (h : d * M ∣ N) (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g ∈
      qSupportedOnDvdSubmodule N k d :=
  mem_qSupportedOnDvdSubmodule.mpr <| isSupportedOnDvd_iff.mpr fun n hn ↦ by
    simp [CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map M)
      (one_mem_strictPeriods_Gamma1_map N) (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g n, hn]

/-- **The range of `V_d` lies in the supported submodule.** Stated for the `ℂ`-linear map, which is
the shape `TauCeti.cuspFormsOld` is assembled from, so the old subspace is contained in the
supported submodule divisor by divisor. -/
theorem range_levelRaise_le_qSupportedOnDvdSubmodule {N : ℕ} (M : ℕ) (h : d * M ∣ N) :
    LinearMap.range (CuspForm.levelRaiseₗ (k := k) d (Gamma1_map_le_conjAct_scaleGL_of_dvd h)) ≤
      qSupportedOnDvdSubmodule N k d := by
  rintro _ ⟨g, rfl⟩
  simpa using levelRaise_mem_qSupportedOnDvdSubmodule M h g


end QExpansion

end TauCeti
