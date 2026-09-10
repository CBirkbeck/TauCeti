/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Deriv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup

/-!
# Derivatives of ideal-indexed Dirichlet series

Mathlib's `LSeries.hasDerivAt_term` differentiates the term `f n / n ^ s` of an `ℕ`-indexed
Dirichlet series, producing the same term weighted by `-log n`.  This file records the
ideal-indexed counterpart: `idealTerm K f s I` is `f I / N(I) ^ s`, and differentiating it in `s`
weights it by `-log N(I)`.

No new calculus is done here.  An ideal term is an `L`-series term of a constant coefficient at
the index `N(I)`, so the statement is a specialization rather than a parallel development.

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

This is Mathlib's `LSeries.hasDerivAt_term` at the constant coefficient `fun _ ↦ f I` and the
index `N(I)`: an ideal term *is* an `L`-series term, once the ideal is replaced by its norm.  The
logarithm is the complex one, of a positive real argument: `N(I) ≥ 1` for a nonzero ideal, so it
agrees with `Real.log N(I)` and is real and nonnegative. -/
theorem hasDerivAt_idealTerm (f : IdealArithmeticFunction K) (I : (Ideal (𝓞 K))⁰) (s : ℂ) :
    HasDerivAt (fun z ↦ idealTerm K f z I)
      (-(Complex.log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) * idealTerm K f s I)) s := by
  have hn : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 :=
    (Ideal.absNorm_pos_of_nonZeroDivisors I).ne'
  -- An ideal term is the `L`-series term of the constant coefficient `f I` at `N(I)`.
  have h := LSeries.hasDerivAt_term (fun _ ↦ f I) (Ideal.absNorm (I : Ideal (𝓞 K))) s
  simp only [LSeries.term_of_ne_zero hn, LSeries.logMul] at h
  simpa [idealTerm_def, mul_div_assoc] using h

end TauCeti
