/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.BranchLogRoot
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic

/-!
# A holomorphic logarithm of an ideal `L`-series

`TauCeti.MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm` gives nonvanishing one
point at a time, and the exponential form of the Euler product determines a logarithm only modulo
`2πi ℤ`.  Neither is a branch: a branch is a single holomorphic function on a region, and choosing
one needs the region to be simply connected as well as zero-free.

This file makes that choice.  On a simply connected open set where the ideal-indexed series
converges absolutely at every point, the `L`-series has a holomorphic logarithm, and the derivative
of that logarithm is the logarithmic derivative of the `L`-series — the same function for every
choice of branch, since two branches differ by a locally constant multiple of `2πi`.

## Main results

* `TauCeti.MultiplicativeIdealWeight.exists_differentiableOn_exp_eq_LSeries`: the branch, together
  with the identification of its derivative.
-/

public section

namespace TauCeti

open Complex IsDedekindDomain Set

open scoped NumberField

namespace MultiplicativeIdealWeight

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)

/-- **A holomorphic logarithm of the `L`-series on a simply connected zero-free region.**  Let `U`
be a simply connected open set on which the `L`-series of the norm coefficients is holomorphic and
at every point of which the ideal-indexed series converges absolutely.  Then there is a holomorphic
`L` on `U` with `exp ∘ L` the `L`-series, and `deriv L` is its logarithmic derivative.

Absolute convergence enters only through the Euler product, which is what makes the `L`-series
zero-free on `U`; simple connectedness is what turns pointwise nonvanishing into a single branch. -/
theorem exists_differentiableOn_exp_eq_LSeries {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (LSeries (normCoeff K χ.toIdealArithmeticFunction)) U)
    (hconv : ∀ s ∈ U, Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧
      EqOn (Complex.exp ∘ L) (LSeries (normCoeff K χ.toIdealArithmeticFunction)) U ∧
      ∀ s ∈ U, deriv L s = logDeriv (LSeries (normCoeff K χ.toIdealArithmeticFunction)) s := by
  have h₀ : 0 ∉ LSeries (normCoeff K χ.toIdealArithmeticFunction) '' U := by
    rintro ⟨s, hs, hs0⟩
    exact χ.LSeries_ne_zero_of_summable_idealTerm (hconv s hs) hs0
  obtain ⟨L, hL, hLeq⟩ := exists_differentiableOn_eqOn_exp_comp hUc hUo hdiff h₀
  exact ⟨L, hL, hLeq, fun s hs ↦ deriv_eq_logDeriv_of_eqOn_exp_comp hUo hL hLeq hs⟩

end MultiplicativeIdealWeight

end TauCeti
