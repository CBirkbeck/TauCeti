/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Finset.Lattice.Fold

import Mathlib.Analysis.Real.Sqrt

/-!
# The singular sets on the boundary contour

The two finite sets of complex points at which a level-one form's zeros meet the boundary
contour, closed under the identifications the contour pairings use: the arc singular set —
the unit-norm points of a finite set `S ⊆ ℍ` together with their images under the inversion
`z ↦ -1/z` and the corners `ρ`, `ρ + 1` — and the vertical singular set — the `re = ±1/2`,
norm-above-one points of `S` together with their translates onto the opposite vertical
line. Their calculus: the corners belong to the arc set, the arc set consists of unit-norm
points and is inversion-closed, the vertical set lies on the two vertical lines and is
translation-paired, all points have positive imaginary part, and a single height bound
dominates every vertical point.

## Main declarations

* `TauCeti.ModularForm.arcSingularSet` and `TauCeti.ModularForm.verticalSingularSet`.
* `TauCeti.ModularForm.neg_one_div_mem_arcSingularSet` (inversion closure).
* `TauCeti.ModularForm.sub_one_mem_verticalSingularSet` and
  `TauCeti.ModularForm.add_one_mem_verticalSingularSet` (translation pairing).
* `TauCeti.ModularForm.exists_height_bound` (a height above `√3/2` and `1` dominating `S`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Helpers.lean`) this file ports onto the
  current Mathlib pin.
-/

public section

open Complex Set UpperHalfPlane

namespace TauCeti

namespace ModularForm

/-- The arc singular set of a finite `S ⊆ ℍ`: its unit-norm members, their images under the
inversion `z ↦ -1/z`, and the corners `ρ` and `ρ + 1`. -/
noncomputable def arcSingularSet (S : Finset ℍ) : Finset ℂ :=
  (S.filter fun p : ℍ ↦ ‖(p : ℂ)‖ = 1).image ((↑·) : ℍ → ℂ) ∪
    (S.filter fun p : ℍ ↦ ‖(p : ℂ)‖ = 1).image (fun p : ℍ ↦ -1 / (p : ℂ)) ∪
    {(ρ : ℂ), (ρ : ℂ) + 1}

/-- The vertical singular set of a finite `S ⊆ ℍ`: its `re = ±1/2`, norm-above-one members
together with their translates onto the opposite vertical line. -/
noncomputable def verticalSingularSet (S : Finset ℍ) : Finset ℂ :=
  (S.filter fun p : ℍ ↦ (p : ℂ).re = 1 / 2 ∧ 1 < ‖(p : ℂ)‖).image ((↑·) : ℍ → ℂ) ∪
    (S.filter fun p : ℍ ↦ (p : ℂ).re = 1 / 2 ∧ 1 < ‖(p : ℂ)‖).image
      (fun p : ℍ ↦ (p : ℂ) - 1) ∪
    (S.filter fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖).image ((↑·) : ℍ → ℂ) ∪
    (S.filter fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖).image
      (fun p : ℍ ↦ (p : ℂ) + 1)

/-- The real part of the corner `ρ`. -/
private lemma rho_re : (ρ : ℂ).re = -(1 / 2) := by
  norm_num [ρ]

/-- The imaginary part of the corner `ρ`. -/
private lemma rho_im : (ρ : ℂ).im = Real.sqrt 3 / 2 := by
  simp [ρ]

/-- The square norm of the corner `ρ` is `1`. -/
private lemma normSq_rho : normSq (ρ : ℂ) = 1 := by
  rw [normSq_apply, rho_re, rho_im]
  nlinarith [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- The corner `ρ` has norm `1`. -/
private lemma norm_rho : ‖(ρ : ℂ)‖ = 1 := by
  have h2 : ‖(ρ : ℂ)‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, normSq_rho]
  nlinarith [norm_nonneg ((ρ : ℂ))]

private lemma rho_ne_zero : (ρ : ℂ) ≠ 0 := by
  intro h0
  have := normSq_rho
  rw [h0] at this
  simp at this

/-- The inversion carries `ρ` to `ρ + 1`. -/
private lemma neg_one_div_rho : -1 / (ρ : ℂ) = (ρ : ℂ) + 1 := by
  rw [div_eq_iff rho_ne_zero]
  apply Complex.ext <;>
    simp only [neg_re, neg_im, one_re, one_im, mul_re, mul_im, add_re, add_im,
      rho_re, rho_im] <;>
    nlinarith [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private lemma rho_add_one_ne_zero : (ρ : ℂ) + 1 ≠ 0 := by
  intro h0
  have him : ((ρ : ℂ) + 1).im = Real.sqrt 3 / 2 := by rw [add_im, one_im, add_zero, rho_im]
  rw [h0, zero_im] at him
  have := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)
  linarith

/-- The inversion carries `ρ + 1` to `ρ`. -/
private lemma neg_one_div_rho_add_one : -1 / ((ρ : ℂ) + 1) = (ρ : ℂ) := by
  have h := neg_one_div_rho
  rw [div_eq_iff rho_ne_zero] at h
  rw [div_eq_iff rho_add_one_ne_zero]
  linear_combination h

/-- The corner `ρ` belongs to the arc singular set. -/
theorem rho_mem_arcSingularSet (S : Finset ℍ) : (ρ : ℂ) ∈ arcSingularSet S := by
  simp [arcSingularSet]

/-- The corner `ρ + 1` belongs to the arc singular set. -/
theorem rho_add_one_mem_arcSingularSet (S : Finset ℍ) :
    (ρ : ℂ) + 1 ∈ arcSingularSet S := by
  simp [arcSingularSet]

/-- Every point of the arc singular set has norm `1`. -/
theorem norm_eq_one_of_mem_arcSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ arcSingularSet S) : ‖s‖ = 1 := by
  simp only [arcSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with (⟨p, ⟨-, hp_norm⟩, rfl⟩ | ⟨p, ⟨-, hp_norm⟩, rfl⟩) | rfl | rfl
  · exact hp_norm
  · rw [norm_div, norm_neg, norm_one, hp_norm, div_one]
  · exact norm_rho
  · rw [← neg_one_div_rho, norm_div, norm_neg, norm_one, norm_rho, div_one]

/-- The arc singular set is closed under the inversion `z ↦ -1/z`. -/
theorem neg_one_div_mem_arcSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ arcSingularSet S) : -1 / s ∈ arcSingularSet S := by
  simp only [arcSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton] at hs ⊢
  rcases hs with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | rfl | rfl
  · exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
  · refine Or.inl (Or.inl ⟨p, hp, ?_⟩)
    have hne : (p : ℂ) ≠ 0 := by
      intro h0
      rw [h0] at hp
      simpa using hp.2
    field_simp
  · exact Or.inr (Or.inr neg_one_div_rho)
  · exact Or.inr (Or.inl neg_one_div_rho_add_one)

/-- Every point of the vertical singular set lies on one of the two vertical lines. -/
theorem re_eq_of_mem_verticalSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ verticalSingularSet S) : s.re = 1 / 2 ∨ s.re = -(1 / 2) := by
  simp only [verticalSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs
  rcases hs with ((⟨p, ⟨-, hp_re, -⟩, rfl⟩ | ⟨p, ⟨-, hp_re, -⟩, rfl⟩) |
    ⟨p, ⟨-, hp_re, -⟩, rfl⟩) | ⟨p, ⟨-, hp_re, -⟩, rfl⟩
  · exact Or.inl hp_re
  · right
    rw [sub_re, one_re, hp_re]
    norm_num
  · exact Or.inr hp_re
  · left
    rw [add_re, one_re, hp_re]
    norm_num

/-- A right-line point of the vertical singular set has its left translate in the set. -/
theorem sub_one_mem_verticalSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ verticalSingularSet S) (hre : s.re = 1 / 2) :
    s - 1 ∈ verticalSingularSet S := by
  simp only [verticalSingularSet, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hs ⊢
  rcases hs with ((⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
  · exact Or.inl (Or.inl (Or.inr ⟨p, hp, rfl⟩))
  · rw [sub_re, one_re, hp.2.1] at hre
    norm_num at hre
  · rw [hp.2.1] at hre
    norm_num at hre
  · refine Or.inl (Or.inr ⟨p, hp, ?_⟩)
    ring

/-- A left-line point of the vertical singular set has its right translate in the set. -/
theorem add_one_mem_verticalSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ verticalSingularSet S) (hre : s.re = -(1 / 2)) :
    s + 1 ∈ verticalSingularSet S := by
  simp only [verticalSingularSet, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hs ⊢
  rcases hs with ((⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
  · rw [hp.2.1] at hre
    norm_num at hre
  · refine Or.inl (Or.inl (Or.inl ⟨p, hp, ?_⟩))
    ring
  · exact Or.inr ⟨p, hp, rfl⟩
  · rw [add_re, one_re, hp.2.1] at hre
    norm_num at hre

/-- Some height above `√3/2` and `1` dominates the imaginary parts of a finite `S ⊆ ℍ`. -/
theorem exists_height_bound (S : Finset ℍ) :
    ∃ H : ℝ, Real.sqrt 3 / 2 < H ∧ 1 < H ∧ ∀ p ∈ S, (p : ℂ).im < H := by
  have hsqrt3 : Real.sqrt 3 / 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  rcases S.eq_empty_or_nonempty with rfl | h_ne
  · exact ⟨2, hsqrt3, by norm_num, by simp⟩
  refine ⟨max 2 (S.sup' h_ne (fun p : ℍ ↦ (p : ℂ).im) + 1),
    lt_of_lt_of_le hsqrt3 (le_max_left _ _),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun p hp ↦ ?_⟩
  calc (p : ℂ).im ≤ S.sup' h_ne (fun p : ℍ ↦ (p : ℂ).im) :=
        Finset.le_sup' (fun p : ℍ ↦ (p : ℂ).im) hp
    _ < S.sup' h_ne (fun p : ℍ ↦ (p : ℂ).im) + 1 := by linarith
    _ ≤ max 2 (S.sup' h_ne (fun p : ℍ ↦ (p : ℂ).im) + 1) := le_max_right _ _

/-- A height bound on `S` bounds the vertical singular set. -/
theorem im_lt_of_mem_verticalSingularSet {S : Finset ℍ} {s : ℂ} {H : ℝ}
    (hs : s ∈ verticalSingularSet S) (h_bound : ∀ p ∈ S, (p : ℂ).im < H) : s.im < H := by
  simp only [verticalSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs
  rcases hs with ((⟨p, ⟨hp_mem, -⟩, rfl⟩ | ⟨p, ⟨hp_mem, -⟩, rfl⟩) |
    ⟨p, ⟨hp_mem, -⟩, rfl⟩) | ⟨p, ⟨hp_mem, -⟩, rfl⟩ <;>
    first | exact h_bound p hp_mem | simpa using h_bound p hp_mem

/-- Every point of the arc singular set lies in the open upper half-plane. -/
theorem im_pos_of_mem_arcSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ arcSingularSet S) : 0 < s.im := by
  simp only [arcSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with (⟨p, ⟨-, hp_norm⟩, rfl⟩ | ⟨p, ⟨-, hp_norm⟩, rfl⟩) | rfl | rfl
  · exact p.2
  · have hne : (p : ℂ) ≠ 0 := by
      intro h0
      rw [h0] at hp_norm
      simp at hp_norm
    have : (-1 / (p : ℂ)).im = (p : ℂ).im / normSq (p : ℂ) := by
      rw [div_im]
      simp [normSq_apply]
      ring
    rw [this]
    exact div_pos p.2 (normSq_pos.mpr hne)
  · simpa using (ρ : ℍ).2
  · rw [add_im, one_im, add_zero]
    simpa using (ρ : ℍ).2

/-- Every point of the vertical singular set lies in the open upper half-plane. -/
theorem im_pos_of_mem_verticalSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ verticalSingularSet S) : 0 < s.im := by
  simp only [verticalSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs
  rcases hs with ((⟨p, -, rfl⟩ | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩ <;>
    simpa using p.2

end ModularForm

end TauCeti

end
