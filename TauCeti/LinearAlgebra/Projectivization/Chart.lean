/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# The projective line is the affine line plus one point

`ℙ K (Fin 2 → K)` is the projective line over a field `K`. This file exhibits it as
`Option K`: the point `[1 : x]` for each `x : K`, together with `[0 : 1]` at infinity.

Mathlib has the projective space, the linear-group action on it, and its cardinality, but not
this chart. Without it a concrete index set — `Fin (q + 1)`, say — cannot be identified with the
projective line, and the action cannot be transported to it.

## Main definitions

* `TauCeti.Projectivization.affineChart`: the map `Option K → ℙ K (Fin 2 → K)`.
* `TauCeti.Projectivization.affineChartEquiv`: it is an equivalence.

## Main results

* `TauCeti.Projectivization.affineChart_injective` and
  `TauCeti.Projectivization.affineChart_surjective`.
* `TauCeti.Projectivization.smul_affineChartEquiv_bijective`: transporting the action of a
  `SL(2, K)` matrix along the chart gives a bijection of `Option K`. This is the point of the
  chart: on the projective line the action is a group action, so bijectivity is free, and the
  chart carries that to whatever concrete index set is at hand.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace TauCeti

namespace Projectivization

variable {K : Type*} [Field K]

-- `![1, x]` is nonzero because its first entry is `1`
private theorem cons_one_ne_zero (x : K) : ![(1 : K), x] ≠ 0 := by
  intro h
  have := congr_fun h 0
  simp at this

-- `![0, 1]` is nonzero because its second entry is `1`
private theorem cons_zero_one_ne_zero : ![(0 : K), 1] ≠ 0 := by
  intro h
  have := congr_fun h 1
  simp at this

/-- **The affine chart of the projective line**: `x ↦ [1 : x]`, with `∞ ↦ [0 : 1]`. -/
def affineChart (K : Type*) [Field K] : Option K → ℙ K (Fin 2 → K)
  | some x => _root_.Projectivization.mk K ![1, x] (cons_one_ne_zero x)
  | none => _root_.Projectivization.mk K ![0, 1] cons_zero_one_ne_zero

/-- **The chart is injective.** Two chart points agree only if the scaling relating their
representatives is `1`, which pins the second coordinate; and no finite point is the point at
infinity, since a scaling cannot send `1` to `0`. -/
theorem affineChart_injective : Function.Injective (affineChart K) := by
  rintro (_ | x) (_ | y) h <;> simp only [affineChart] at h
  · rfl
  · rw [_root_.Projectivization.mk_eq_mk_iff] at h
    obtain ⟨a, ha⟩ := h
    have h0 := congr_fun ha 0
    simp [Units.smul_def] at h0
  · rw [_root_.Projectivization.mk_eq_mk_iff] at h
    obtain ⟨a, ha⟩ := h
    have h1 := congr_fun ha 0
    simp at h1
  · rw [_root_.Projectivization.mk_eq_mk_iff] at h
    obtain ⟨a, ha⟩ := h
    have h0 : (a : K) = 1 := by simpa [Units.smul_def] using congr_fun ha 0
    have h1 : (a : K) * y = x := by simpa [Units.smul_def] using congr_fun ha 1
    rw [h0, one_mul] at h1
    exact congrArg some h1.symm

/-- **The chart is surjective.** Scale a representative so that its first coordinate is `1`; when
that coordinate vanishes the second cannot, and the point is the one at infinity. -/
theorem affineChart_surjective : Function.Surjective (affineChart K) := by
  refine _root_.Projectivization.ind fun v hv ↦ ?_
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simpa using ‹_›
    refine ⟨none, ?_⟩
    simp only [affineChart]
    rw [_root_.Projectivization.mk_eq_mk_iff]
    refine ⟨(Units.mk0 (v 1) h1)⁻¹, ?_⟩
    funext i
    fin_cases i <;> simp [Units.smul_def, h0, inv_mul_cancel₀ h1]
  · refine ⟨some (v 1 / v 0), ?_⟩
    simp only [affineChart]
    rw [_root_.Projectivization.mk_eq_mk_iff]
    refine ⟨(Units.mk0 (v 0) h0)⁻¹, ?_⟩
    funext i
    fin_cases i <;> simp [Units.smul_def, h0, div_eq_inv_mul]

/-- **The projective line is the affine line plus one point.** -/
noncomputable def affineChartEquiv (K : Type*) [Field K] : Option K ≃ ℙ K (Fin 2 → K) :=
  Equiv.ofBijective (affineChart K) ⟨affineChart_injective, affineChart_surjective⟩

/-- **A matrix acts bijectively on the chart.** Transported along `affineChartEquiv`, the action
of `g : SL(2, K)` on `ℙ K (Fin 2 → K)` becomes a bijection of `Option K` — bijectivity comes from
the action being a group action, with no case analysis on the chart. -/
theorem smul_affineChartEquiv_bijective (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    Function.Bijective
      (fun x : Option K => (affineChartEquiv K).symm (g • (affineChartEquiv K) x)) :=
  ((affineChartEquiv K).symm.bijective.comp (MulAction.toPerm g).bijective).comp
    (affineChartEquiv K).bijective

end Projectivization

end TauCeti
