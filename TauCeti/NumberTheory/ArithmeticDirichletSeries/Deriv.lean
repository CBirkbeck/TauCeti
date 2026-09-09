/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup

/-!
# Derivatives of ideal-indexed Dirichlet series

Mathlib's `LSeries.hasDerivAt_term` differentiates the term `f n / n ^ s` of an `ℕ`-indexed
Dirichlet series, producing the same term weighted by `-log n`.  This file records the
ideal-indexed counterpart: `idealTerm K f s I` is `f I / N(I) ^ s`, and differentiating it in `s`
weights it by `-log N(I)`.

## Main results

* `TauCeti.hasDerivAt_idealTerm`: the derivative in `s` of an ideal term is the term itself,
  weighted by `-log N(I)`.
-/

public section

namespace TauCeti

open Complex

open scoped nonZeroDivisors NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **The derivative of an ideal term.**  Differentiating `f I / N(I) ^ s` in `s` returns the same
term weighted by `-log N(I)`.

This is the ideal-indexed counterpart of Mathlib's `LSeries.hasDerivAt_term`.  The logarithm is the
complex one, of a positive real argument: `N(I) ≥ 1` for a nonzero ideal, so it agrees with
`Real.log N(I)` and is real and nonnegative. -/
theorem hasDerivAt_idealTerm (f : IdealArithmeticFunction K) (I : (Ideal (𝓞 K))⁰) (s : ℂ) :
    HasDerivAt (fun z ↦ idealTerm K f z I)
      (-(Complex.log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) * idealTerm K f s I)) s := by
  have hne : ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors I).ne'
  have hfun : (fun z : ℂ ↦ idealTerm K f z I)
      = fun z : ℂ ↦ f I * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-z)) := by
    funext z
    rw [idealTerm_def, cpow_neg, div_eq_mul_inv]
  rw [hfun]
  have hbase := (hasDerivAt_neg' s).const_cpow
    (c := ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ))) (Or.inl hne)
  have heq : -(Complex.log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) * idealTerm K f s I)
      = f I * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)
          * Complex.log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) * -1) := by
    rw [idealTerm_def, cpow_neg, div_eq_mul_inv]
    ring
  rw [heq]
  exact hbase.const_mul (f I)

end TauCeti
