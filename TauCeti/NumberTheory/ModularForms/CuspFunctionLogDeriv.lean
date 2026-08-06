/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
# The logarithmic derivative through the `q`-parameter

A width-`h` periodic holomorphic function on the upper half-plane factors through its
cusp function along `𝕢 h`, so its logarithmic derivative at `z` is the logarithmic
derivative of the cusp function at `𝕢 h z` times the derivative `2πi/h · 𝕢 h z` of the
`q`-parameter. This is the chain rule that turns the ceiling contour integral of the
valence formula into a `q`-circle integral of the cusp function.

## Main declarations

* `TauCeti.hasDerivAt_qParam`: the `q`-parameter differentiates to `2πi/h` times itself.
* `TauCeti.UpperHalfPlane.logDeriv_comp_ofComplex_eq_cuspFunction`: the chain rule for
  the logarithmic derivative through `𝕢 h`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Seg5CuspIntegral.lean`) this file ports
  onto the current Mathlib pin.
-/

public section

open Complex Filter Function UpperHalfPlane

open scoped Real Manifold

namespace TauCeti

/-- The `q`-parameter differentiates to `2πi/h` times itself. For `h = 0` the parameter
is the constant `1` and the claimed derivative is the junk value `0`, so the statement is
unconditional. -/
theorem hasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (Periodic.qParam h) (2 * π * Complex.I / h * Periodic.qParam h z) z := by
  have hlin : HasDerivAt (fun w : ℂ ↦ 2 * ↑π * Complex.I * w / h)
      (2 * ↑π * Complex.I / h) z := by
    have h1 := (hasDerivAt_id z).const_mul (2 * (π : ℂ) * Complex.I / h)
    have h2 : (fun w : ℂ ↦ 2 * ↑π * Complex.I / ↑h * w) =
        fun w : ℂ ↦ 2 * ↑π * Complex.I * w / ↑h := by
      funext w
      ring
    simpa [h2, mul_one] using h1
  have hfun : Periodic.qParam h = fun w : ℂ ↦ Complex.exp (2 * ↑π * Complex.I * w / h) :=
    rfl
  have hval : Periodic.qParam h z = Complex.exp (2 * ↑π * Complex.I * z / h) := rfl
  rw [hval, hfun]
  have hcexp := hlin.cexp
  rwa [mul_comm (Complex.exp (2 * ↑π * Complex.I * z / ↑h))
    (2 * ↑π * Complex.I / ↑h)] at hcexp

namespace UpperHalfPlane

/-- The chain rule for the logarithmic derivative through the `q`-parameter: at a point
of the open upper half-plane, the logarithmic derivative of the extension of a width-`h`
periodic holomorphic bounded function is the logarithmic derivative of its cusp function
at `𝕢 h z`, times the derivative `2πi/h · 𝕢 h z` of the `q`-parameter. -/
theorem logDeriv_comp_ofComplex_eq_cuspFunction {f : ℍ → ℂ} {h : ℝ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f)
    (hfbdd : UpperHalfPlane.IsBoundedAtImInfty f) {z : ℂ} (hz : 0 < z.im) :
    logDeriv (f ∘ ofComplex) z =
      logDeriv (cuspFunction h f) (Periodic.qParam h z) *
        (2 * π * Complex.I / h * Periodic.qParam h z) := by
  have heq : (f ∘ ofComplex) =ᶠ[nhds z]
      fun w ↦ cuspFunction h f (Periodic.qParam h w) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
    have := eq_cuspFunction (h := h) (f := f) ⟨w, hw⟩ hh.ne' hfper
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    exact (this.symm.trans (by rw [UpperHalfPlane.coe_mk]))
  have hq1 : ‖Periodic.qParam h z‖ < 1 := Periodic.norm_qParam_lt_one hh hz
  have hcusp : DifferentiableAt ℂ (cuspFunction h f) (Periodic.qParam h z) :=
    differentiableAt_cuspFunction hh hfper hfhol hfbdd hq1
  have hqd := hasDerivAt_qParam h z
  calc logDeriv (f ∘ ofComplex) z
      = logDeriv (fun w ↦ cuspFunction h f (Periodic.qParam h w)) z := by
        simp only [logDeriv_apply]
        rw [heq.eq_of_nhds, heq.deriv.eq_of_nhds]
    _ = logDeriv (cuspFunction h f) (Periodic.qParam h z) * deriv (Periodic.qParam h) z :=
        logDeriv_comp hcusp hqd.differentiableAt
    _ = _ := by rw [hqd.deriv]

end UpperHalfPlane

end TauCeti

end
