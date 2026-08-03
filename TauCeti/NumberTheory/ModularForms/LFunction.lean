/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# L-functions of modular forms

For a weight-`k` modular form `f` with `q`-expansion `f(τ) = Σ_{n≥0} aₙ qⁿ`, the
**L-function** is the Dirichlet series `L(s, f) = Σ_{n ≥ 1} aₙ · n^{-s}`, built on
Mathlib's `LSeries` infrastructure applied to the coefficient sequence of
`UpperHalfPlane.qExpansion` at the strict width of the level at `∞`.

## Main definitions

* `ModularForms.lCoeff f`: the coefficient sequence `n ↦ aₙ(f)`, as `ℕ → ℂ`.
* `ModularForms.lSeries f`: the L-function `s ↦ LSeries (lCoeff f) s`.
* `ModularForms.imAxis f`: `f` along the positive imaginary axis (`0` off it) — the
  function whose Mellin transform is the completed L-function.

## Main results

Hecke's convergence bounds, from Mathlib's `q`-expansion coefficient growth:

* `ModularForms.abscissaOfAbsConv_lCoeff_le`: for a modular form of weight `k ≥ 0`,
  the abscissa of absolute convergence is at most `k + 1` (from `aₙ = O(nᵏ)`).
* `ModularForms.abscissaOfAbsConv_lCoeff_le_cuspForm`: for a cusp form, at most
  `k/2 + 1` (from Hecke's `aₙ = O(n^{k/2})`).
* `ModularForms.lSeriesSummable_of_modularForm` / `lSeriesSummable_of_cuspForm`:
  absolute convergence on the corresponding half-planes.

The non-cuspidal abscissa bound `k + 1` is weaker than Diamond–Shurman Prop. 5.9.1
(which gives convergence for `Re s > k` via `aₙ = O(n^{k-1})`); tightening it is a
separate milestone of the roadmap's Layer 7.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/LFunction.lean`), with the abscissa bounds — advertised
but not present there — supplied from Mathlib's `ModularFormClass.qExpansion_isBigO` and
`CuspFormClass.qExpansion_isBigO`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.9
* [Miy] Miyake, *Modular Forms*, Thm 4.5.16
-/

public section

noncomputable section

open Filter LSeries UpperHalfPlane

namespace ModularForms

variable {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)}
variable {F : Type*} [FunLike F ℍ ℂ]

/-- The coefficient sequence `n ↦ aₙ(f)` of the `q`-expansion of `f` at the strict width
at `∞` of its level, viewed as `ℕ → ℂ` — the natural input to Mathlib's `LSeries`. -/
def lCoeff [ModularFormClass F Γ k] (f : F) : ℕ → ℂ :=
  fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n

lemma lCoeff_apply [ModularFormClass F Γ k] (f : F) (n : ℕ) :
    lCoeff f n = (qExpansion Γ.strictWidthInfty f).coeff n := (rfl)

/-- The **L-function** of a modular form: the Dirichlet series
`L(s, f) = Σ_{n ≥ 1} aₙ(f) · n^{-s}` of its `q`-expansion coefficients. -/
def lSeries [ModularFormClass F Γ k] (f : F) (s : ℂ) : ℂ :=
  LSeries (lCoeff f) s

lemma lSeries_apply [ModularFormClass F Γ k] (f : F) (s : ℂ) :
    lSeries f s = LSeries (lCoeff f) s := (rfl)

/-- The point `i·t` lies in the upper half-plane when `0 < t`. -/
lemma im_I_mul_pos {t : ℝ} (ht : 0 < t) : 0 < (Complex.I * (t : ℂ)).im := by
  rw [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im]
  simpa using ht

/-- **A modular form along the positive imaginary axis**: `t > 0` maps to `f(i·t)`, and
`t ≤ 0` to `0`. The Mellin transform of this function is the completed L-function. -/
def imAxis [ModularFormClass F Γ k] (f : F) (t : ℝ) : ℂ :=
  if h : 0 < t then f ⟨Complex.I * (t : ℂ), im_I_mul_pos h⟩ else 0

lemma imAxis_apply_of_pos [ModularFormClass F Γ k] (f : F) {t : ℝ} (ht : 0 < t) :
    imAxis f t = f ⟨Complex.I * (t : ℂ), im_I_mul_pos ht⟩ := by
  rw [imAxis, dif_pos ht]

variable [Γ.IsArithmetic]

/-- **Hecke's abscissa bound for modular forms**: for weight `k ≥ 0`, the L-series of a
modular form converges absolutely for `Re s > k + 1` (from `aₙ = O(nᵏ)`). -/
theorem abscissaOfAbsConv_lCoeff_le (hk : 0 ≤ k) [ModularFormClass F Γ k] (f : F) :
    abscissaOfAbsConv (lCoeff f) ≤ ((k : ℝ) : EReal) + 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_isBigO_rpow ?_
  have h := ModularFormClass.qExpansion_isBigO hk f
  refine h.congr' EventuallyEq.rfl (Eventually.of_forall fun n ↦ ?_)
  simp only [Real.rpow_intCast]

/-- **Hecke's abscissa bound for cusp forms**: the L-series of a cusp form converges
absolutely for `Re s > k/2 + 1` (from Hecke's `aₙ = O(n^{k/2})`). -/
theorem abscissaOfAbsConv_lCoeff_le_cuspForm [CuspFormClass F Γ k] (f : F) :
    abscissaOfAbsConv (lCoeff f) ≤ (((k : ℝ) / 2 : ℝ) : EReal) + 1 :=
  LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (CuspFormClass.qExpansion_isBigO f)

/-- The L-series of a weight-`k ≥ 0` modular form is summable for `Re s > k + 1`. -/
theorem lSeriesSummable_of_modularForm (hk : 0 ≤ k) [ModularFormClass F Γ k] (f : F)
    {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    LSeriesSummable (lCoeff f) s := by
  refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
  exact lt_of_le_of_lt (abscissaOfAbsConv_lCoeff_le hk f) (by exact_mod_cast hs)

/-- The L-series of a weight-`k` cusp form is summable for `Re s > k/2 + 1`. -/
theorem lSeriesSummable_of_cuspForm [CuspFormClass F Γ k] (f : F)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeriesSummable (lCoeff f) s := by
  refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
  exact lt_of_le_of_lt (abscissaOfAbsConv_lCoeff_le_cuspForm f) (by exact_mod_cast hs)

end ModularForms
