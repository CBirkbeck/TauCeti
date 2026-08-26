/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Valuation.Basic

import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Monic

/-!
# Valuations of roots of monic polynomials

Elementary estimates for a valuation `ν` on a commutative ring: a product of two `ν`-integral
elements that is a `ν`-unit has `ν`-unit factors, and for a monic polynomial `p` with
`ν`-integral coefficients the leading term dominates at any `t` with `1 < ν t`, so that
`ν (p.eval t) = ν t ^ p.natDegree`. Consequently a root of such a `p` is `ν`-integral — the
concrete form of the fact that valuation rings are integrally closed.

## Main results

* `Valuation.eq_one_of_mul_eq_one`: if `ν a ≤ 1`, `ν b ≤ 1` and `ν (a * b) = 1`, then `ν a = 1`.
* `Valuation.map_eval_eq_of_one_lt`: `ν (p.eval t) = ν t ^ p.natDegree` for monic `p` with
  `ν`-integral coefficients and `1 < ν t`.
* `Valuation.le_one_of_root_monic`: a root of a monic polynomial of positive degree with
  `ν`-integral coefficients is `ν`-integral.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (Mordell–Weil): the `2`-descent has to see that
a root of the Weierstrass cubic is integral at every prime where the cubic's coefficients are, which
is `le_one_of_root_monic`. Nothing here mentions a curve, so it is stated for a bare valuation. The
companion estimate, for a polynomial *expression* in an element that is already integral, is
`TauCeti.RingTheory.Valuation.Polynomial`.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `Valuation`. The source is written against Lean
`v4.32.0`; this is a forward port.
-/

public section

namespace Valuation

open Polynomial

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (ν : Valuation L Γ)
  {t a b : L}

lemma map_natCast_le_one {R : Type*} [Ring R] (ν : Valuation R Γ) (n : ℕ) :
    ν (n : R) ≤ 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ]
    exact (ν.map_add _ _).trans (max_le ih ν.map_one.le)

/-- If a product of two integral elements is a unit, then each factor is a unit. -/
lemma eq_one_of_mul_eq_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hab : ν (a * b) = 1) :
    ν a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = ν a * ν b := by rw [← map_mul, hab]
    _ ≤ ν a * 1 := by gcongr
    _ = ν a := mul_one _

/-- If `p` is monic with coefficients that are integral for the valuation `ν` and `1 < ν t`,
then the value of `p` at `t` is dominated by the leading term: `ν (p.eval t) = ν t ^ p.natDegree`.
In particular, `p.eval t ≠ 0`. -/
lemma map_eval_eq_of_one_lt {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (ht : 1 < ν t) :
    ν (p.eval t) = ν t ^ p.natDegree := by
  set n := p.natDegree with hn
  have h0 : ν t ≠ 0 := (zero_lt_one.trans ht).ne'
  have heval : p.eval t = (∑ i ∈ Finset.range n, p.coeff i * t ^ i) + t ^ n := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul]
  have hlt : ν (∑ i ∈ Finset.range n, p.coeff i * t ^ i) < ν (t ^ n) := by
    rw [map_pow]
    refine ν.map_sum_lt (pow_ne_zero n h0) fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    calc ν (p.coeff i * t ^ i) ≤ 1 * ν t ^ i := by
          rw [map_mul, map_pow]; gcongr; exact hcoeff i hi
      _ = ν t ^ i := one_mul _
      _ < ν t ^ n := pow_lt_pow_right₀ ht hi
  rw [heval, ν.map_add_eq_of_lt_right hlt, map_pow]

/-- A root of a monic polynomial of positive degree with coefficients that are integral for the
valuation `ν` is itself integral. (This is a concrete form of the fact that valuation rings are
integrally closed.) -/
lemma le_one_of_root_monic {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (hdeg : p.natDegree ≠ 0)
    (heq : p.eval t = 0) :
    ν t ≤ 1 := by
  by_contra! hlt
  have h := ν.map_eval_eq_of_one_lt hp hcoeff hlt
  rw [heq, map_zero] at h
  exact (zero_lt_one.trans hlt).ne' (pow_eq_zero_iff hdeg |>.mp h.symm)

end Valuation

end
