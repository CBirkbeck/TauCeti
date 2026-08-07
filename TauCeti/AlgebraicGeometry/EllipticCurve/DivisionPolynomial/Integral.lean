/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Integrality from the division-polynomial description of the `x`-coordinate

The `x`-coordinate of `n • P` is `Φₙ(x) / ΨSqₙ(x)`, where `x` is the `x`-coordinate of `P`. So if
`n • P` has `x`-coordinate `x'`, the two are tied by

`x' * ΨSqₙ(x) = Φₙ(x)`,

which says exactly that `x` is a root of `Φₙ − x' · ΨSqₙ`. This file proves that this polynomial is
**monic** whenever `(n : R) ≠ 0` — `Φₙ` is monic of degree `n²` while `ΨSqₙ` has degree `n² - 1`, so
subtracting a constant multiple of the latter cannot disturb the leading term — and draws the
consequence: when `R` is integrally closed in the ambient algebra, an `x'` coming from `R` forces
`x` to come from `R` as well. In words,
*if a multiple of a point is integral then the point already was*, which is the descent step that
lets the Nagell–Lutz argument reduce an arbitrary torsion point to one of prime order.

The geometric input — that the `x`-coordinates really are related that way — is not proved here: it
is the point-level `[n]`-multiplication formula, which is mathlib-track material (mathlib
[#13782](https://github.com/leanprover-community/mathlib4/pull/13782) and its successors). It enters
below as the hypothesis `hid`, so the algebraic half is available independently and the two can be
composed once the `[n]`-formula lands.

## Main results

* `TauCeti.WeierstrassCurve.monic_Φ_sub_C_mul_ΨSq`: `Φₙ − C c * ΨSqₙ` is monic when `(n : R) ≠ 0`.
* `TauCeti.WeierstrassCurve.aeval_Φ_sub_C_mul_ΨSq_eq_zero`: the coordinate identity says exactly
  that `x` is a root of that polynomial.
* `TauCeti.WeierstrassCurve.isInteger_of_mul_eval_ΨSq_eq_eval_Φ`: in any `R`-algebra in which `R`
  is integrally closed, if `x' * ΨSqₙ(x) = Φₙ(x)` with `x'` coming from `R`, then so does `x`.

The last needs only `IsIntegrallyClosedIn R A` — no fraction field, no domain, no unique
factorization: it is an integral-root statement, not a rational-root one. Nontriviality of `R` is
not assumed either; it follows from `(n : R) ≠ 0`.

This advances the Nagell–Lutz integrality milestone of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item "The torsion subgroup and Nagell–Lutz",
whose stated route is "division polynomials".

## Provenance

Ported from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), pinned by
that roadmap at `dev/modular-curves @ 9fec8eba7652`:
`LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean`, declarations `monic_Φ_sub_smul_ΨSq` and the
integral-root half of `x_isInteger_of_nsmul_x_isInteger`.
-/

public section

open Polynomial

namespace TauCeti

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [NoZeroDivisors R] (W : _root_.WeierstrassCurve R)

/-- `Φₙ − C c * ΨSqₙ` is monic, for any `c : R`, whenever `(n : R) ≠ 0`.

`Φₙ` is monic of degree `n²` (`leadingCoeff_Φ`, `natDegree_Φ`) and `ΨSqₙ` has degree `n² - 1`
(`natDegree_ΨSq`, which is where `(n : R) ≠ 0` is used), so the subtracted term has strictly
smaller degree and the leading coefficient survives. Nontriviality of `R` is not assumed: it
follows from `(n : R) ≠ 0`. -/
theorem monic_Φ_sub_C_mul_ΨSq {n : ℤ} (hn : (n : R) ≠ 0) (c : R) :
    (W.Φ n - C c * W.ΨSq n).Monic := by
  have : Nontrivial R := nontrivial_of_ne _ _ hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine Polynomial.Monic.sub_of_left (W.leadingCoeff_Φ n) (degree_lt_degree ?_)
  calc (C c * W.ΨSq n).natDegree
    _ ≤ (W.ΨSq n).natDegree := natDegree_C_mul_le _ _
    _ = n.natAbs ^ 2 - 1 := W.natDegree_ΨSq hn
    _ < n.natAbs ^ 2 := Nat.pred_lt (pow_ne_zero 2 (Int.natAbs_ne_zero.mpr hn0))
    _ = (W.Φ n).natDegree := (W.natDegree_Φ n).symm

section Root

variable {A : Type*} [CommRing A] [Algebra R A]

omit [NoZeroDivisors R] in
/-- The coordinate identity `c * ΨSqₙ(x) = Φₙ(x)` says exactly that `x` is a root of the
polynomial `Φₙ − C c * ΨSqₙ` over `R`.

Kept separate from the integrality theorem so that the passage between `W.baseChange A` and the
`R`-coefficient polynomials lives in one place. -/
theorem aeval_Φ_sub_C_mul_ΨSq_eq_zero {n : ℤ} {x : A} {c : R}
    (hid : algebraMap R A c * ((W.baseChange A).ΨSq n).eval x = ((W.baseChange A).Φ n).eval x) :
    aeval x (W.Φ n - C c * W.ΨSq n) = 0 := by
  simp only [_root_.WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_Φ,
    _root_.WeierstrassCurve.map_ΨSq, aeval_def, eval₂_eq_eval_map, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, eval_sub, eval_mul, eval_C] at hid ⊢
  linear_combination -hid

/-- **An integral multiple forces an integral point, on `x`-coordinates.**

If `x' * ΨSqₙ(x) = Φₙ(x)` — the relation between the `x`-coordinates of `P` and `n • P` — and `x'`
comes from `R`, then so does `x`: it is a root of the monic `Φₙ − C c * ΨSqₙ`, and `R` is
integrally closed in `A`.

Stated for an arbitrary `R`-algebra `A` in which `R` is integrally closed; the fraction field of an
integrally closed domain is the case the Nagell–Lutz argument uses. -/
theorem isInteger_of_mul_eval_ΨSq_eq_eval_Φ [IsIntegrallyClosedIn R A] {n : ℤ} (hn : (n : R) ≠ 0)
    {x x' : A} (hx' : IsLocalization.IsInteger R x')
    (hid : x' * ((W.baseChange A).ΨSq n).eval x = ((W.baseChange A).Φ n).eval x) :
    IsLocalization.IsInteger R x := by
  obtain ⟨c, hc⟩ := hx'
  exact RingHom.mem_rangeS.mpr (IsIntegrallyClosedIn.isIntegral_iff.mp
    ⟨_, monic_Φ_sub_C_mul_ΨSq W hn c, aeval_Φ_sub_C_mul_ΨSq_eq_zero W (hc ▸ hid)⟩)

end Root

end WeierstrassCurve

end TauCeti
