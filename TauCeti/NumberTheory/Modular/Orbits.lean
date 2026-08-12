/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Modular

import TauCeti.Analysis.Complex.UpperHalfPlane.Rho

/-!
# Orbits of the modular group on the upper half-plane

Every `SL(2, ℤ)`-orbit of `ℍ` has a representative in the standard fundamental domain, and
translation by one preserves orbits. On the *open* domain the representative is moreover unique,
so the orbit map is injective there. These are the orbit-space inputs of the valence formula: the
first says a sum over orbits can be read off representatives, the last says doing so counts each
orbit once.

On the closed domain `𝒟` the representative is not unique: `z ↦ z + 1` identifies the two
vertical edges and `z ↦ -1/z` folds the unit arc onto itself, fixing `i` and swapping `ρ` with
`ρ + 1`. Mathlib's classification `ModularGroup.cases_of_mem_fd_smul_mem_fd` pins these
identifications down, and here it yields the closed-domain complements: the elliptic orbits of
`i` and `ρ` meet `𝒟` exactly at `i` and at `{ρ, ρ + 1}`, and the orbit map is injective on the
part of `𝒟` left of the identifications — `𝒟` without the right vertical edge and the right
half-arc.

## Main declarations

* `TauCeti.ModularGroup.exists_rep_mem_fd`: every orbit meets `𝒟`.
* `TauCeti.ModularGroup.orbit_mk_int_vadd`: integer translation preserves the orbit.
* `TauCeti.ModularGroup.orbit_mk_injOn_fdo`: the orbit map is injective on `𝒟ᵒ`.
* `TauCeti.ModularGroup.orbit_mk_eq_I_iff`: a point of `𝒟` lies in the orbit of `i` exactly
  when it is `i`.
* `TauCeti.ModularGroup.orbit_mk_eq_ρ_iff`: a point of `𝒟` lies in the orbit of `ρ` exactly
  when it is `ρ` or `ρ + 1`.
* `TauCeti.ModularGroup.orbit_mk_injOn_fd_left`: the orbit map is injective on `𝒟` minus the
  right vertical edge and the right half-arc.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the elliptic-orbit and
  closed-domain classification development (`ForMathlib/Orbits.lean`), commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0. Mathlib's classification
  `ModularGroup.cases_of_mem_fd_smul_mem_fd` replaces its denominator analysis here.
-/

public section

open UpperHalfPlane

open scoped MatrixGroups Modular

namespace TauCeti

namespace ModularGroup

/-- Every `SL(2, ℤ)`-orbit of `ℍ` has a representative in the standard fundamental
domain. -/
lemma exists_rep_mem_fd (q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) :
    ∃ p : ℍ, Quotient.mk'' p = q ∧ p ∈ 𝒟 := by
  induction q using Quotient.inductionOn' with
  | h z =>
    obtain ⟨g, hg⟩ := _root_.ModularGroup.exists_smul_mem_fd z
    exact ⟨g • z, Quotient.sound' ⟨g, rfl⟩, hg⟩

/-- Translation by any integer preserves the `SL(2, ℤ)`-orbit. -/
@[simp]
lemma orbit_mk_int_vadd (n : ℤ) (z : ℍ) :
    (Quotient.mk'' ((n : ℝ) +ᵥ z) : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) =
      Quotient.mk'' z :=
  Quotient.sound' ⟨_root_.ModularGroup.T ^ n, UpperHalfPlane.modular_T_zpow_smul z n⟩


/-- Distinct points of the **open** fundamental domain lie in distinct `SL(2, ℤ)`-orbits: the
orbit map is injective there. This is the Second Fundamental Domain Lemma
(`ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo`) restated as injectivity, which is the form the
orbit-indexed valence formula needs. It fails on the closed domain `𝒟`, whose boundary is
identified with itself by `T` and `S`. -/
lemma orbit_mk_injOn_fdo :
    Set.InjOn (fun p : ℍ ↦ (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ)) 𝒟ᵒ := by
  intro p hp q hq hpq
  obtain ⟨g, hg⟩ := Quotient.exact' hpq
  have hg' : g • q = p := hg
  have hgq : g • q ∈ 𝒟ᵒ := by rw [hg']; exact hp
  exact hg'.symm.trans (_root_.ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo hq hgq).symm

/-! ### The boundary identifications of the closed fundamental domain

The values of the corner points and of the finitely many group elements that can move a point of
`𝒟` inside `𝒟` (classified by `ModularGroup.cases_of_mem_fd_smul_mem_fd`). -/

private lemma re_I : (I : ℍ).re = 0 := by
  rw [← coe_re, coe_I, Complex.I_re]

private lemma re_ρ : (ρ : ℍ).re = -(1 / 2) := by
  rw [← coe_re]
  norm_num [UpperHalfPlane.ρ]

private lemma re_vadd_ρ : ((1 : ℝ) +ᵥ ρ : ℍ).re = 1 / 2 := by
  rw [vadd_re, re_ρ]
  norm_num

private lemma I_ne_ρ : (I : ℍ) ≠ ρ :=
  ne_of_apply_ne UpperHalfPlane.re (by norm_num [re_I, re_ρ])

private lemma I_ne_vadd_ρ : (I : ℍ) ≠ (1 : ℝ) +ᵥ ρ :=
  ne_of_apply_ne UpperHalfPlane.re (by norm_num [re_I, re_ρ])

private lemma ρ_ne_vadd_ρ : (ρ : ℍ) ≠ (1 : ℝ) +ᵥ ρ :=
  ne_of_apply_ne UpperHalfPlane.re (by norm_num [re_ρ])

private lemma S_smul_I : _root_.ModularGroup.S • (I : ℍ) = I :=
  _root_.ModularGroup.stabilizer_I.mpr (by simp)

private lemma S_smul_ρ : _root_.ModularGroup.S • (ρ : ℍ) = (1 : ℝ) +ᵥ ρ := by
  rw [modular_S_smul, UpperHalfPlane.ext_iff, coe_mk, coe_vadd, Complex.ofReal_one, inv_neg,
    ← one_div, ← neg_div, neg_one_div_ρ, add_comm]

private lemma S_smul_vadd_ρ : _root_.ModularGroup.S • ((1 : ℝ) +ᵥ ρ : ℍ) = ρ := by
  rw [modular_S_smul, UpperHalfPlane.ext_iff, coe_mk, coe_vadd, Complex.ofReal_one, inv_neg,
    ← one_div, ← neg_div, add_comm, neg_one_div_ρ_add_one]

private lemma ST_smul_ρ : (_root_.ModularGroup.S * _root_.ModularGroup.T) • (ρ : ℍ) = ρ :=
  _root_.ModularGroup.stabilizer_ρ.mpr (by simp)

private lemma TST_smul_ρ :
    (_root_.ModularGroup.T * _root_.ModularGroup.S * _root_.ModularGroup.T) • (ρ : ℍ) =
      (1 : ℝ) +ᵥ ρ := by
  rw [mul_smul, modular_T_smul, mul_smul, S_smul_vadd_ρ, modular_T_smul]

private lemma T_inv_S_smul_ρ : (_root_.ModularGroup.T⁻¹ * _root_.ModularGroup.S) • (ρ : ℍ) = ρ :=
  _root_.ModularGroup.stabilizer_ρ.mpr (by simp)

/-- The inversion `S` keeps unit-circle points on the unit circle. -/
lemma norm_coe_S_smul {p : ℍ} (hp : ‖(p : ℂ)‖ = 1) :
    ‖((_root_.ModularGroup.S • p : ℍ) : ℂ)‖ = 1 := by
  rw [modular_S_smul, coe_mk, norm_inv, norm_neg, hp, inv_one]

/-- The inversion `S` negates the real part of a unit-circle point. -/
lemma re_S_smul {p : ℍ} (hp : ‖(p : ℂ)‖ = 1) :
    (_root_.ModularGroup.S • p).re = -p.re := by
  rw [← coe_re, modular_S_smul, coe_mk, Complex.inv_re, Complex.neg_re, Complex.normSq_neg,
    Complex.normSq_eq_norm_sq, hp, one_pow, div_one, coe_re]

/-- A point of the closed fundamental domain lying in the `SL(2, ℤ)`-orbit of `i` is `i`
itself: the boundary identifications of `𝒟` fix `i`. -/
lemma orbit_mk_eq_I_iff {p : ℍ} (hp : p ∈ 𝒟) :
    (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' I ↔ p = I := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  obtain ⟨g, rfl⟩ : ∃ g : SL(2, ℤ), g • (I : ℍ) = p := Quotient.exact' h
  rcases _root_.ModularGroup.cases_of_mem_fd_smul_mem_fd _root_.ModularGroup.I_mem_fd hp with
    (rfl | rfl) | ⟨-, hre⟩ | ⟨-, hre⟩ | ⟨rfl | rfl, -⟩ | ⟨-, hI⟩ | ⟨-, hI⟩ | ⟨-, hI⟩ |
    ⟨-, hI⟩ | ⟨-, hI⟩ | ⟨-, hI⟩
  · exact one_smul _ _
  · exact (_root_.ModularGroup.SL_neg_smul _ _).trans (one_smul _ _)
  · norm_num [re_I] at hre
  · norm_num [re_I] at hre
  · exact S_smul_I
  · exact (_root_.ModularGroup.SL_neg_smul _ _).trans S_smul_I
  · exact absurd hI I_ne_vadd_ρ
  · exact absurd hI I_ne_vadd_ρ
  · exact absurd hI I_ne_vadd_ρ
  · exact absurd hI I_ne_ρ
  · exact absurd hI I_ne_ρ
  · exact absurd hI I_ne_ρ

/-- A point of the closed fundamental domain lying in the `SL(2, ℤ)`-orbit of `ρ` is `ρ` or
its translate `ρ + 1`: the two corners the boundary identifications of `𝒟` exchange. -/
lemma orbit_mk_eq_ρ_iff {p : ℍ} (hp : p ∈ 𝒟) :
    (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' ρ ↔
      p = ρ ∨ p = (1 : ℝ) +ᵥ ρ := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ : ∃ g : SL(2, ℤ), g • (ρ : ℍ) = p := Quotient.exact' h
    rcases _root_.ModularGroup.cases_of_mem_fd_smul_mem_fd _root_.ModularGroup.ρ_mem_fd hp with
      (rfl | rfl) | ⟨rfl | rfl, -⟩ | ⟨-, hre⟩ | ⟨rfl | rfl, -⟩ | ⟨-, hρ⟩ | ⟨-, hρ⟩ | ⟨-, hρ⟩ |
      ⟨rfl | rfl, -⟩ | ⟨rfl | rfl, -⟩ | ⟨rfl | rfl, -⟩
    · exact .inl (one_smul _ _)
    · exact .inl ((_root_.ModularGroup.SL_neg_smul _ _).trans (one_smul _ _))
    · exact .inr (modular_T_smul _)
    · exact .inr ((_root_.ModularGroup.SL_neg_smul _ _).trans (modular_T_smul _))
    · norm_num [re_ρ] at hre
    · exact .inr S_smul_ρ
    · exact .inr ((_root_.ModularGroup.SL_neg_smul _ _).trans S_smul_ρ)
    · exact absurd hρ ρ_ne_vadd_ρ
    · exact absurd hρ ρ_ne_vadd_ρ
    · exact absurd hρ ρ_ne_vadd_ρ
    · exact .inl ST_smul_ρ
    · exact .inl ((_root_.ModularGroup.SL_neg_smul _ _).trans ST_smul_ρ)
    · exact .inr TST_smul_ρ
    · exact .inr ((_root_.ModularGroup.SL_neg_smul _ _).trans TST_smul_ρ)
    · exact .inl T_inv_S_smul_ρ
    · exact .inl ((_root_.ModularGroup.SL_neg_smul _ _).trans T_inv_S_smul_ρ)
  · rintro (rfl | rfl)
    · rfl
    · simpa using orbit_mk_int_vadd 1 ρ

/-- The orbit map is injective on the part of `𝒟` left of the boundary identifications: the
points with `re < 1/2` which, if on the unit circle, have `re < 0`. `T` moves the right
vertical edge onto the left one and `S` the right half-arc onto the left one, and this set
meets what remains of each orbit at most once. -/
lemma orbit_mk_injOn_fd_left :
    Set.InjOn (fun p : ℍ ↦ (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ))
      {p : ℍ | p ∈ 𝒟 ∧ p.re < 1 / 2 ∧ (‖(p : ℂ)‖ = 1 → p.re < 0)} := by
  rintro p₁ ⟨hp₁fd, hp₁re, hp₁arc⟩ p₂ ⟨hp₂fd, hp₂re, hp₂arc⟩ h
  obtain ⟨g, rfl⟩ : ∃ g : SL(2, ℤ), g • p₂ = p₁ := Quotient.exact' h
  rcases _root_.ModularGroup.cases_of_mem_fd_smul_mem_fd hp₂fd hp₁fd with
    (rfl | rfl) | ⟨rfl | rfl, hre⟩ | ⟨-, hre⟩ | ⟨rfl | rfl, hnorm⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨rfl | rfl, rfl⟩ | ⟨rfl | rfl, rfl⟩ | ⟨rfl | rfl, rfl⟩
  all_goals try simp only [_root_.ModularGroup.SL_neg_smul] at hp₁re hp₁arc ⊢
  · exact one_smul _ _
  · exact one_smul _ _
  · rw [_root_.ModularGroup.re_T_smul, hre] at hp₁re
    norm_num at hp₁re
  · rw [_root_.ModularGroup.re_T_smul, hre] at hp₁re
    norm_num at hp₁re
  · exact absurd hre hp₂re.ne
  · have h1 := hp₁arc (norm_coe_S_smul hnorm)
    rw [re_S_smul hnorm] at h1
    linarith [hp₂arc hnorm]
  · have h1 := hp₁arc (norm_coe_S_smul hnorm)
    rw [re_S_smul hnorm] at h1
    linarith [hp₂arc hnorm]
  · norm_num [re_ρ] at hp₂re
  · norm_num [re_ρ] at hp₂re
  · norm_num [re_ρ] at hp₂re
  · exact ST_smul_ρ
  · exact ST_smul_ρ
  · rw [TST_smul_ρ, re_vadd_ρ] at hp₁re
    norm_num at hp₁re
  · rw [TST_smul_ρ, re_vadd_ρ] at hp₁re
    norm_num at hp₁re
  · exact T_inv_S_smul_ρ
  · exact T_inv_S_smul_ρ

end ModularGroup

end TauCeti

end
