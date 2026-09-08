/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Normed.Module.FilledHull

/-!
# Points of large norm in an open half-space

`TauCeti.not_isBounded_halfSpace_lt` says an open half-space `{y | φ y < u}` is unbounded.
`TauCeti.exists_lt_and_lt_norm` restates that in the form its consumers want: for every radius
there is a point of the half-space outside that radius. `TauCeti.exists_lt_and_lt_norm'` is the
other side, `u < φ y`, obtained from `-φ`.

Specialising to `Complex.reCLM` and `Complex.imCLM` gives the four open half-planes of `ℂ`. This
is what a winding-number vanishing argument needs: to transport a winding number through an
unbounded connected region one must exhibit, for each radius, a point of the region beyond it.

## Main results

* `TauCeti.exists_lt_and_lt_norm`, `TauCeti.exists_lt_and_lt_norm'` — the two directions for a
  nonzero continuous functional on a real normed space.
* `TauCeti.exists_im_lt_and_lt_norm`, `TauCeti.exists_lt_im_and_lt_norm`,
  `TauCeti.exists_re_lt_and_lt_norm`, `TauCeti.exists_lt_re_and_lt_norm` — the four half-planes.
-/

public section

open Bornology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An open half-space contains points of arbitrarily large norm. -/
theorem exists_lt_and_lt_norm {φ : E →L[ℝ] ℝ} (hφ : φ ≠ 0) (u R : ℝ) :
    ∃ y : E, φ y < u ∧ R < ‖y‖ := by
  by_contra h
  push Not at h
  exact not_isBounded_halfSpace_lt hφ u
    (isBounded_iff_forall_norm_le.mpr ⟨R, fun y hy => h y hy⟩)

/-- The half-space on the other side of the functional, via `-φ`. -/
theorem exists_lt_and_lt_norm' {φ : E →L[ℝ] ℝ} (hφ : φ ≠ 0) (u R : ℝ) :
    ∃ y : E, u < φ y ∧ R < ‖y‖ := by
  obtain ⟨y, hy, hn⟩ := exists_lt_and_lt_norm (φ := -φ) (neg_ne_zero.mpr hφ) (-u) R
  exact ⟨y, by simpa using hy, hn⟩

private lemma imCLM_ne_zero : (Complex.imCLM : ℂ →L[ℝ] ℝ) ≠ 0 := by
  intro h
  simpa using congrArg (fun ψ => ψ Complex.I) h

private lemma reCLM_ne_zero : (Complex.reCLM : ℂ →L[ℝ] ℝ) ≠ 0 := by
  intro h
  simpa using congrArg (fun ψ => ψ 1) h

/-- The open lower half-plane `{z | z.im < c}` contains points of arbitrarily large norm. -/
theorem exists_im_lt_and_lt_norm (c R : ℝ) : ∃ z : ℂ, z.im < c ∧ R < ‖z‖ :=
  exists_lt_and_lt_norm imCLM_ne_zero c R

/-- The open upper half-plane `{z | c < z.im}` contains points of arbitrarily large norm. -/
theorem exists_lt_im_and_lt_norm (c R : ℝ) : ∃ z : ℂ, c < z.im ∧ R < ‖z‖ :=
  exists_lt_and_lt_norm' imCLM_ne_zero c R

/-- The open left half-plane `{z | z.re < c}` contains points of arbitrarily large norm. -/
theorem exists_re_lt_and_lt_norm (c R : ℝ) : ∃ z : ℂ, z.re < c ∧ R < ‖z‖ :=
  exists_lt_and_lt_norm reCLM_ne_zero c R

/-- The open right half-plane `{z | c < z.re}` contains points of arbitrarily large norm. -/
theorem exists_lt_re_and_lt_norm (c R : ℝ) : ∃ z : ℂ, c < z.re ∧ R < ‖z‖ :=
  exists_lt_and_lt_norm' reCLM_ne_zero c R

end TauCeti
