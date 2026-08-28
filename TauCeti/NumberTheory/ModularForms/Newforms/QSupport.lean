/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# Power series supported on multiples of `d`

A power series is *supported on multiples of `d`* when every coefficient at an index not
divisible by `d` vanishes. This is the coefficient condition behind the Atkin–Lehner
description of the old subspace: the image of the level-raising operator `V_d` consists
exactly of forms whose `q`-expansion is supported on multiples of `d`.

The predicate is stated for a power series over an arbitrary semiring rather than for a
`q`-expansion, so that the closure lemmas below are available before any modular input is
introduced.

## Main definitions

* `TauCeti.IsSupportedOnDvd`: the support condition on a power series.
* `TauCeti.QExpansionSupportedOnDvd`: the same condition on the period-1 `q`-expansion of a
  cusp form.

## Main results

* `TauCeti.IsSupportedOnDvd.add`, `.smul`, `.neg`, `.sub`: the condition is preserved by the
  module operations, which is what makes the forms satisfying it a submodule.
* `TauCeti.CuspForm.isSupportedOnDvd_qExpansion_levelRaise` and its modular-form counterpart: the
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
`IsSupportedOnDvd` and its namespace `zero`, `add`, `smul`, `neg`, `sub`, `one`, together with
`QExpansionSupportedOnDvd`, `qExpansion_modularFormLevelRaise_isSupportedOnDvd`,
`qExpansion_levelRaise_isSupportedOnDvd`, renamed here to
`ModularForm.isSupportedOnDvd_qExpansion_levelRaise` and its cusp-form counterpart.

The source's two forward lemmas are proved here directly from
`TauCeti.ModularForm.qExpansion_levelRaise_coeff` and its cusp-form counterpart, which
already state `aₙ(V_d f) = a_{n/d}(f)` for `d ∣ n` and `0` otherwise. The source has no cusp-form
coefficient lemma and reaches the cusp case by rebuilding the form as a `ModularForm` and
transporting along `qExpansion_ext2`; that detour is unnecessary here and is not ported. The
source's `modularFormLevelRaise`/`levelRaise` name pair is this repository's
`ModularForm.levelRaise`/`CuspForm.levelRaise`, distinguished by namespace rather than by prefix.

The source states the predicate inside its `HeckeRing.GL2.AtkinLehner` namespace; here it is a
statement about power series alone and is placed accordingly, since nothing in it mentions a
modular form.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §5.7.
* Atkin–Lehner, *Hecke operators on* `Γ₀(m)`, Math. Ann. **185** (1970).
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Function
open scoped Manifold MatrixGroups ModularForm Pointwise

namespace TauCeti

/-- A power series is **supported on multiples of `d`** when its coefficient at every index
not divisible by `d` vanishes. -/
def IsSupportedOnDvd {R : Type*} [Semiring R] (d : ℕ) (P : PowerSeries R) : Prop :=
  ∀ n : ℕ, ¬ d ∣ n → P.coeff n = 0

/-- `IsSupportedOnDvd` restated as an `Iff`, so the defining condition is available to `rw`
without unfolding the definition. -/
theorem isSupportedOnDvd_iff {R : Type*} [Semiring R] {d : ℕ} {P : PowerSeries R} :
    IsSupportedOnDvd d P ↔ ∀ n : ℕ, ¬ d ∣ n → P.coeff n = 0 := (Iff.rfl)

namespace IsSupportedOnDvd

variable {R S : Type*} {d : ℕ} {P Q : PowerSeries R}

/-- The elimination form: a supported series has vanishing coefficients away from the
multiples of `d`. -/
theorem coeff_of_not_dvd [Semiring R] (hP : IsSupportedOnDvd d P) {n : ℕ} (hn : ¬ d ∣ n) :
    P.coeff n = 0 := hP n hn

@[simp]
theorem zero [Semiring R] (d : ℕ) : IsSupportedOnDvd d (0 : PowerSeries R) := fun _ _ ↦ by simp

theorem add [Semiring R] (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P + Q) := fun n hn ↦ by
  rw [map_add, hP n hn, hQ n hn, zero_add]

theorem smul [Semiring R] [Semiring S] [Module S R] (c : S) (hP : IsSupportedOnDvd d P) :
    IsSupportedOnDvd d (c • P) := fun n hn ↦ by
  simp [hP n hn]

theorem neg [Ring R] (hP : IsSupportedOnDvd d P) : IsSupportedOnDvd d (-P) := fun n hn ↦ by
  rw [map_neg, hP n hn, neg_zero]

theorem sub [Ring R] (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P - Q) := sub_eq_add_neg P Q ▸ hP.add hQ.neg

/-- The constant power series `1` is supported on multiples of any `d`: its only nonzero
coefficient sits at `0`, which every `d` divides. -/
theorem one [Semiring R] (d : ℕ) : IsSupportedOnDvd d (1 : PowerSeries R) := fun n hn ↦ by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd (dvd_zero d) hn
  · simp [PowerSeries.coeff_one, hpos.ne']

end IsSupportedOnDvd

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
theorem ModularForm.isSupportedOnDvd_qExpansion_levelRaise (M : ℕ)
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    IsSupportedOnDvd d
      (qExpansion 1 (ModularForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL M d) g)) :=
  fun n hn ↦ by
    simp [ModularForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map M)
      (one_mem_strictPeriods_Gamma1_map (d * M)) (Gamma1_map_le_conjAct_scaleGL M d) g n, hn]

/-- **Level-raising lands in the supported subspace, for cusp forms** — the forward half of the
Atkin-Lehner correspondence. -/
theorem CuspForm.isSupportedOnDvd_qExpansion_levelRaise (M : ℕ)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    IsSupportedOnDvd d
      (qExpansion 1 (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL M d) g)) :=
  fun n hn ↦ by
    simp [CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map M)
      (one_mem_strictPeriods_Gamma1_map (d * M)) (Gamma1_map_le_conjAct_scaleGL M d) g n, hn]

/-- The submodule of cusp forms of level `Γ₁(M)` whose period-1 `q`-expansion is supported on
multiples of `d`. Closure under the module operations is the additivity and homogeneity of the
`q`-expansion, which hold because `1` is a strict period. -/
noncomputable def qSupportedOnDvdSubmodule (M : ℕ) (k : ℤ) (d : ℕ) :
    Submodule ℂ (CuspForm ((Gamma1 M).map (mapGL ℝ)) k) where
  carrier := {f | QExpansionSupportedOnDvd d f}
  zero_mem' n _ := by simp [qExpansion_zero]
  add_mem' {f g} hf hg := by
    simpa [QExpansionSupportedOnDvd,
      ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1_map M) f g] using hf.add hg
  smul_mem' c f hf := by
    simpa [QExpansionSupportedOnDvd,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map M) c f] using hf.smul c

omit [NeZero M] [NeZero d] in
/-- Membership in `qSupportedOnDvdSubmodule` is the `q`-support condition, by definition. -/
@[simp]
theorem mem_qSupportedOnDvdSubmodule {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} :
    f ∈ qSupportedOnDvdSubmodule M k d ↔ QExpansionSupportedOnDvd d f := (Iff.rfl)

omit [NeZero M] [NeZero d] in
/-- Membership in `qSupportedOnDvdSubmodule`, spelled out on coefficients. -/
theorem mem_qSupportedOnDvdSubmodule_iff {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} :
    f ∈ qSupportedOnDvdSubmodule M k d ↔
      ∀ n : ℕ, ¬ d ∣ n → (qExpansion 1 f).coeff n = 0 := (Iff.rfl)

/-- **Level-raising into a divisible level lands in the supported submodule.** For `d * M ∣ N`,
the operator `V_d` carries `S_k(Γ₁(M))` into the cusp forms whose `q`-expansion is supported on
multiples of `d` — the forward half of the Atkin–Lehner description of the old subspace. -/
theorem levelRaise_mem_qSupportedOnDvdSubmodule {N : ℕ} (M : ℕ)
    (h : d * M ∣ N) (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g ∈
      qSupportedOnDvdSubmodule N k d := fun n hn ↦ by
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
