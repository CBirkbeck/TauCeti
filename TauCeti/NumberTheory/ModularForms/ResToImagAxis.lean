/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Restriction of a function on the upper half-plane to the imaginary axis

The Mellin transform computing the completed L-function of a modular form integrates the
form along the positive imaginary axis: Mathlib's `ModularForm.Λ_eq_mellin` reads
`Λ f = mellin (fun t ↦ f (ofComplex (I * t)))`. This file names that restriction,
`resToImagAxis F t = F (i t)` for `t > 0` (and `0` otherwise, since `i t ∈ ℍ` fails for
`t ≤ 0`), and develops the properties of it that the L-function estimates consume.

The three predicates `RealOnImagAxis`, `PosOnImagAxis` and `EventuallyPosOnImagAxis` record
that the restriction is real-valued, real and positive, or real and eventually positive along
`atTop`. Each is closed under the pointwise algebraic operations, and the closure lemmas are
tagged `@[fun_prop]`, so `fun_prop` discharges these side conditions for a concrete
expression built from constants by `+`, `*`, `•` and `^`.

## Main definitions

* `UpperHalfPlane.resToImagAxis`: the restriction `t ↦ F (i t)`, extended by `0` on `t ≤ 0`.
* `UpperHalfPlane.RealOnImagAxis`, `PosOnImagAxis`, `EventuallyPosOnImagAxis`: the restriction
  is real-valued, positive, or eventually positive along `atTop`.

## Main results

* `UpperHalfPlane.resToImagAxis_of_pos`: the characteristic equation of the restriction, which
  every proof below rewrites with.
* `UpperHalfPlane.differentiableAt_resToImagAxis`: the restriction is real-differentiable at
  every `t > 0` when `F` is differentiable as a map of manifolds.
* `UpperHalfPlane.resToImagAxis_slash_S`: the restriction of `F ∣[k] S` at `t` is
  `i ^ (-k) t ^ (-k)` times the restriction of `F` at `1 / t` — the involution `t ↦ 1 / t`
  underlying the functional equation.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/ResToImagAxis.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), with the
`Function.resToImagAxis` dot-notation alias dropped in favour of the single definition, the
repeated unfolding replaced by `resToImagAxis_of_pos`, and eventual positivity phrased with
the `atTop` filter.
-/

public section

open Complex Filter Topology ModularGroup

open scoped Manifold ModularForm MatrixGroups

namespace UpperHalfPlane

/-- The restriction of `F : ℍ → ℂ` to the positive imaginary axis, `t ↦ F (i t)`. Since
`i t` lies in `ℍ` only for `t > 0`, the restriction is extended by `0` on `t ≤ 0`. -/
noncomputable def resToImagAxis (F : ℍ → ℂ) : ℝ → ℂ :=
  fun t ↦ if ht : 0 < t then F ⟨Complex.I * t, by simpa using ht⟩ else 0

/-- The characteristic equation of `resToImagAxis` on its domain of interest. -/
@[simp]
theorem resToImagAxis_of_pos (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    resToImagAxis F t = F ⟨Complex.I * t, by simpa using ht⟩ := dif_pos ht

/-- Off the positive axis the restriction is `0` by convention. -/
theorem resToImagAxis_of_nonpos (F : ℍ → ℂ) {t : ℝ} (ht : t ≤ 0) :
    resToImagAxis F t = 0 := dif_neg (not_lt.mpr ht)

/-- `F` is real-valued on the positive imaginary axis. -/
@[fun_prop]
def RealOnImagAxis (F : ℍ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → (resToImagAxis F t).im = 0

/-- `F` is real and strictly positive on the positive imaginary axis. -/
@[fun_prop]
def PosOnImagAxis (F : ℍ → ℂ) : Prop :=
  RealOnImagAxis F ∧ ∀ t : ℝ, 0 < t → 0 < (resToImagAxis F t).re

/-- `F` is real on the positive imaginary axis and strictly positive far out along it. -/
@[fun_prop]
def EventuallyPosOnImagAxis (F : ℍ → ℂ) : Prop :=
  RealOnImagAxis F ∧ ∀ᶠ t : ℝ in atTop, 0 < (resToImagAxis F t).re

/-! ### Differentiability and the behaviour under `S` -/

/-- The restriction is real-differentiable at every `t > 0` whenever `F` is differentiable as
a map of manifolds: the restriction is the composite of `F` with `t ↦ i t`. -/
@[fun_prop]
theorem differentiableAt_resToImagAxis (F : ℍ → ℂ) (hF : MDiff F) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (resToImagAxis F) t := by
  have hmdiff := hF ⟨Complex.I * t, by simpa using ht⟩
  rw [mdifferentiableAt_iff] at hmdiff
  have h_diff : DifferentiableAt ℝ (fun t : ℝ ↦ F (ofComplex (Complex.I * t))) t := by
    convert hmdiff.restrictScalars ℝ |>.comp t
      (DifferentiableAt.const_mul ofRealCLM.differentiableAt _) using 1
    all_goals try rfl
  refine h_diff.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with s hs
  rw [resToImagAxis_of_pos F hs, ofComplex_apply_of_im_pos (by simp [hs])]

/-- **The `S`-involution on the imaginary axis**: slashing by `S` turns `t` into `1 / t`,
`(F ∣[k] S) (i t) = i ^ (-k) t ^ (-k) F (i / t)`. This is the reflection underlying the
functional equation of the L-function. -/
theorem resToImagAxis_slash_S (F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    resToImagAxis (F ∣[k] S) t =
      Complex.I ^ (-k) * (t : ℂ) ^ (-k) * resToImagAxis F (1 / t) := by
  have ht' : (0 : ℝ) < 1 / t := by positivity
  have h : mk _ (⟨Complex.I * t, by simpa using ht⟩ : ℍ).im_inv_neg_coe_pos =
      (⟨Complex.I * (1 / t : ℝ), by simpa using ht'⟩ : ℍ) :=
    UpperHalfPlane.ext (by
      push_cast
      field_simp
      rw [Complex.I_sq]
      ring)
  rw [resToImagAxis_of_pos _ ht, SlashInvariantForm.slash_S_apply, h,
    resToImagAxis_of_pos F ht']
  simp only [mul_zpow]
  ring

/-! ### Real-valuedness is preserved by the algebraic operations -/

namespace RealOnImagAxis

/-- A real constant is real-valued on the imaginary axis. -/
@[fun_prop]
theorem const (c : ℝ) : RealOnImagAxis (fun _ ↦ (c : ℂ)) := fun t ht ↦ by
  rw [resToImagAxis_of_pos _ ht]
  simp

/-- The zero function is real-valued on the imaginary axis. -/
@[fun_prop]
theorem zero : RealOnImagAxis (fun _ ↦ 0) := by simpa using const 0

/-- The constant function `1` is real-valued on the imaginary axis. -/
@[fun_prop]
theorem one : RealOnImagAxis (fun _ ↦ 1) := by simpa using const 1

/-- Negation preserves real-valuedness on the imaginary axis. -/
@[fun_prop]
theorem neg {F : ℍ → ℂ} (hF : RealOnImagAxis F) : RealOnImagAxis (-F) := fun t ht ↦ by
  have hf := hF t ht
  rw [resToImagAxis_of_pos _ ht] at hf ⊢
  simp [hf]

/-- Addition preserves real-valuedness on the imaginary axis. -/
@[fun_prop]
theorem add {F G : ℍ → ℂ} (hF : RealOnImagAxis F) (hG : RealOnImagAxis G) :
    RealOnImagAxis (F + G) := fun t ht ↦ by
  have hf := hF t ht
  have hg := hG t ht
  rw [resToImagAxis_of_pos _ ht] at hf hg ⊢
  simp [hf, hg]

/-- Subtraction preserves real-valuedness on the imaginary axis. -/
@[fun_prop]
theorem sub {F G : ℍ → ℂ} (hF : RealOnImagAxis F) (hG : RealOnImagAxis G) :
    RealOnImagAxis (F - G) := by simpa [sub_eq_add_neg] using hF.add hG.neg

/-- Multiplication preserves real-valuedness on the imaginary axis. -/
@[fun_prop]
theorem mul {F G : ℍ → ℂ} (hF : RealOnImagAxis F) (hG : RealOnImagAxis G) :
    RealOnImagAxis (F * G) := fun t ht ↦ by
  have hf := hF t ht
  have hg := hG t ht
  rw [resToImagAxis_of_pos _ ht] at hf hg ⊢
  simp [Complex.mul_im, hf, hg]

/-- Real scalar multiplication preserves real-valuedness on the imaginary axis. -/
@[fun_prop]
theorem smul {F : ℍ → ℂ} {c : ℝ} (hF : RealOnImagAxis F) : RealOnImagAxis (c • F) :=
  fun t ht ↦ by
  have hf := hF t ht
  rw [resToImagAxis_of_pos _ ht] at hf ⊢
  simp [Complex.real_smul, Complex.mul_im, hf]

/-- Natural powers preserve real-valuedness on the imaginary axis. -/
@[fun_prop]
theorem pow {F : ℍ → ℂ} (hF : RealOnImagAxis F) (n : ℕ) : RealOnImagAxis (F ^ n) := by
  induction n with
  | zero => simpa [Pi.one_def] using one
  | succ n hn => simpa [pow_succ] using hn.mul hF

end RealOnImagAxis

/-! ### Positivity is preserved by the algebraic operations -/

namespace PosOnImagAxis

/-- A positive real constant is positive on the imaginary axis. -/
theorem const {c : ℝ} (hc : 0 < c) : PosOnImagAxis (fun _ ↦ (c : ℂ)) :=
  ⟨RealOnImagAxis.const c, fun t ht ↦ by rw [resToImagAxis_of_pos _ ht]; simpa using hc⟩

/-- The constant function `1` is positive on the imaginary axis. -/
@[fun_prop]
theorem one : PosOnImagAxis (fun _ ↦ 1) := by simpa using const one_pos

/-- Addition preserves positivity on the imaginary axis. -/
@[fun_prop]
theorem add {F G : ℍ → ℂ} (hF : PosOnImagAxis F) (hG : PosOnImagAxis G) :
    PosOnImagAxis (F + G) :=
  ⟨hF.1.add hG.1, fun t ht ↦ by
    have hf := hF.2 t ht
    have hg := hG.2 t ht
    rw [resToImagAxis_of_pos _ ht] at hf hg ⊢
    simpa using add_pos hf hg⟩

/-- Multiplication preserves positivity on the imaginary axis: the two restrictions are real
there, so the real part of the product is the product of the real parts. -/
@[fun_prop]
theorem mul {F G : ℍ → ℂ} (hF : PosOnImagAxis F) (hG : PosOnImagAxis G) :
    PosOnImagAxis (F * G) :=
  ⟨hF.1.mul hG.1, fun t ht ↦ by
    have hfi := hF.1 t ht
    have hgi := hG.1 t ht
    have hfr := hF.2 t ht
    have hgr := hG.2 t ht
    rw [resToImagAxis_of_pos _ ht] at hfi hgi hfr hgr ⊢
    simpa [Complex.mul_re, hfi, hgi] using mul_pos hfr hgr⟩

/-- Positive scalar multiplication preserves positivity on the imaginary axis. -/
@[fun_prop]
theorem smul {F : ℍ → ℂ} {c : ℝ} (hF : PosOnImagAxis F) (hc : 0 < c) :
    PosOnImagAxis (c • F) :=
  ⟨hF.1.smul, fun t ht ↦ by
    have hf := hF.2 t ht
    rw [resToImagAxis_of_pos _ ht] at hf ⊢
    simpa [Complex.real_smul, Complex.mul_re] using mul_pos hc hf⟩

/-- Natural powers preserve positivity on the imaginary axis. -/
@[fun_prop]
theorem pow {F : ℍ → ℂ} (hF : PosOnImagAxis F) (n : ℕ) : PosOnImagAxis (F ^ n) := by
  induction n with
  | zero => simpa [Pi.one_def] using one
  | succ n hn => simpa [pow_succ] using hn.mul hF

end PosOnImagAxis

/-! ### Eventual positivity is preserved by the algebraic operations -/

namespace EventuallyPosOnImagAxis

/-- Positivity everywhere implies positivity far out. -/
@[fun_prop]
theorem of_pos {F : ℍ → ℂ} (hF : PosOnImagAxis F) : EventuallyPosOnImagAxis F :=
  ⟨hF.1, by filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht using hF.2 t ht⟩

/-- The constant function `1` is eventually positive on the imaginary axis. -/
@[fun_prop]
theorem one : EventuallyPosOnImagAxis (fun _ ↦ 1) := of_pos PosOnImagAxis.one

/-- A positive real constant is eventually positive on the imaginary axis. -/
theorem const {c : ℝ} (hc : 0 < c) : EventuallyPosOnImagAxis (fun _ ↦ (c : ℂ)) :=
  of_pos (PosOnImagAxis.const hc)

/-- Addition preserves eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem add {F G : ℍ → ℂ} (hF : EventuallyPosOnImagAxis F) (hG : EventuallyPosOnImagAxis G) :
    EventuallyPosOnImagAxis (F + G) :=
  ⟨hF.1.add hG.1, by
    filter_upwards [hF.2, hG.2, eventually_gt_atTop (0 : ℝ)] with t hf hg ht
    rw [resToImagAxis_of_pos _ ht] at hf hg ⊢
    simpa using add_pos hf hg⟩

/-- Multiplication preserves eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem mul {F G : ℍ → ℂ} (hF : EventuallyPosOnImagAxis F) (hG : EventuallyPosOnImagAxis G) :
    EventuallyPosOnImagAxis (F * G) :=
  ⟨hF.1.mul hG.1, by
    filter_upwards [hF.2, hG.2, eventually_gt_atTop (0 : ℝ)] with t hf hg ht
    have hfi := hF.1 t ht
    have hgi := hG.1 t ht
    rw [resToImagAxis_of_pos _ ht] at hfi hgi hf hg ⊢
    simpa [Complex.mul_re, hfi, hgi] using mul_pos hf hg⟩

/-- Positive scalar multiplication preserves eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem smul {F : ℍ → ℂ} {c : ℝ} (hF : EventuallyPosOnImagAxis F) (hc : 0 < c) :
    EventuallyPosOnImagAxis (c • F) :=
  ⟨hF.1.smul, by
    filter_upwards [hF.2, eventually_gt_atTop (0 : ℝ)] with t hf ht
    rw [resToImagAxis_of_pos _ ht] at hf ⊢
    simpa [Complex.real_smul, Complex.mul_re] using mul_pos hc hf⟩

/-- Natural powers preserve eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem pow {F : ℍ → ℂ} (hF : EventuallyPosOnImagAxis F) (n : ℕ) :
    EventuallyPosOnImagAxis (F ^ n) := by
  induction n with
  | zero => simpa [Pi.one_def] using one
  | succ n hn => simpa [pow_succ] using hn.mul hF

end EventuallyPosOnImagAxis

end UpperHalfPlane
