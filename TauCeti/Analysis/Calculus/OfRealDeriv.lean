/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.RealDeriv

/-!
# The derivative of the real-to-complex inclusion

The inclusion `ℝ → ℂ` is `ℝ`-differentiable with constant derivative `1`. Mathlib records the
derivative of a real function *composed* with the inclusion (`HasDerivAt.ofReal_comp`) but not the
derivative of the inclusion itself, which is what appears whenever a curve `γ : ℝ → ℂ` is a
straight real segment and its index integrand `γ̇ / (γ - z₀)` has to be evaluated.

## Main results

* `Complex.deriv_ofReal` — `deriv (fun s : ℝ => (s : ℂ)) = fun _ => 1`.
-/

public section

namespace Complex

/-- The derivative of the real-to-complex inclusion is constantly `1`. -/
@[simp]
theorem deriv_ofReal : deriv (fun s : ℝ => (s : ℂ)) = fun _ => 1 := by
  funext t
  simpa using ((hasDerivAt_id t).ofReal_comp).deriv

end Complex

end
