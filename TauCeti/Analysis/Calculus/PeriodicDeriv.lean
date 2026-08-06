/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.LogDeriv

import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Periodicity of the derivative and the logarithmic derivative

Differentiation commutes with translation of the domain, so the derivative of a periodic
function is periodic with the same period, and hence so is its logarithmic derivative.
Both statements are unconditional: `deriv` (and with it `logDeriv`) takes its junk value
at non-differentiable points, and the translation identity holds there too.

## Main declarations

* `TauCeti.Function.Periodic.deriv`: the derivative of a periodic function is periodic.
* `TauCeti.Function.Periodic.logDeriv`: the logarithmic derivative of a periodic function
  is periodic.
-/

public section

namespace TauCeti

namespace Function

namespace Periodic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {c : 𝕜}

/-- The derivative of a periodic function is periodic. -/
theorem deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F}
    (hf : _root_.Function.Periodic f c) :
    _root_.Function.Periodic (_root_.deriv f) c := fun x ↦ by
  rw [← deriv_comp_add_const]
  exact congrFun (congrArg _root_.deriv (funext hf)) x

/-- The logarithmic derivative of a periodic function is periodic. -/
theorem logDeriv {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
    {f : 𝕜 → 𝕜'} (hf : _root_.Function.Periodic f c) :
    _root_.Function.Periodic (_root_.logDeriv f) c :=
  fun x ↦ by rw [logDeriv_apply, logDeriv_apply, deriv hf x, hf x]

end Periodic

end Function

end TauCeti

end
