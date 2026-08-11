/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.CharZero

/-!
# Polynomials over a ring of characteristic zero

Adjoining a variable preserves characteristic zero: the coefficients embed in the polynomial ring,
so a natural number that vanishes there already vanished in the coefficient ring.

Mathlib records this for `MvPolynomial` (`MvPolynomial.instCharZero`, in
`Mathlib/RingTheory/MvPolynomial/Basic.lean`) but not for univariate `Polynomial`. The gap is
visible as soon as the two are mixed: `CharZero ((MvPolynomial σ ℤ)[X][X])` fails to synthesise
even though every coefficient ring in sight has characteristic zero. This file supplies the
missing instance, which is what makes `two_ne_zero` and friends available over iterated polynomial
rings without a bespoke lemma at each level.
-/

public section

namespace Polynomial

/-- Adjoining a variable preserves characteristic zero, the coefficient embedding `Polynomial.C`
being injective. -/
instance instCharZero {R : Type*} [Semiring R] [CharZero R] : CharZero R[X] :=
  (RingHom.charZero_iff C_injective).1 inferInstance

end Polynomial
