/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# An integral-root criterion for the division polynomials `Φₙ` and `ΨSqₙ`

This file is pure polynomial algebra about Mathlib's division polynomials. Its content is that
`Φₙ − C c * ΨSqₙ` is **monic** whenever `(n : R) ≠ 0` — `Φₙ` is monic of degree `n²` while `ΨSqₙ`
has degree `n² - 1`, so subtracting a constant multiple of the latter cannot disturb the leading
term — together with the integral-root consequence: a solution of `c * ΨSqₙ(x) = Φₙ(x)` is a root of
that monic polynomial, so it is integral over `R`, and lies in `R` when `R` is integrally closed in
the ambient algebra.

⚠ **No point of a curve occurs in any statement here, and nothing about `n • P` is proved.** The
motivation is that the `x`-coordinate of `n • P` is `Φₙ(x)/ΨSqₙ(x)`, so the coordinates of `P` and
`n • P` would satisfy exactly the hypothesis `c * ΨSqₙ(x) = Φₙ(x)`; feeding that in would give "an
integral multiple forces an integral point", the descent step of Nagell–Lutz. But that link is the
point-level `[n]`-multiplication formula — mathlib-track material (mathlib
[#13782](https://github.com/leanprover-community/mathlib4/pull/13782) and its successors) — which is
**not available and not proved here**. Until it lands, this file is the algebraic half alone, and
the descent step is not a theorem of this repository.

## Main results

* `TauCeti.WeierstrassCurve.monic_Φ_sub_C_mul_ΨSq`: `Φₙ − C c * ΨSqₙ` is monic when `(n : R) ≠ 0`.
* `TauCeti.WeierstrassCurve.aeval_Φ_sub_C_mul_ΨSq_eq_zero`: the coordinate identity says exactly
  that `x` is a root of that polynomial.
* `TauCeti.WeierstrassCurve.isInteger_of_mul_eval_ΨSq_eq_eval_Φ`: in any `R`-algebra in which `R`
  is integrally closed, if `x' * ΨSqₙ(x) = Φₙ(x)` with `x'` coming from `R`, then so does `x` — a
  statement about two elements satisfying that identity, not about a point and its multiple.

The last needs only `IsIntegrallyClosedIn R A` — no fraction field, no domain, no unique
factorization: it is an integral-root statement, not a rational-root one. Nontriviality of `R` is
not assumed either; it follows from `(n : R) ≠ 0`.

This supplies an ingredient for the Nagell–Lutz integrality milestone of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item "The torsion subgroup and Nagell–Lutz",
whose stated route is "division polynomials". It does not by itself establish any part of that
milestone's statement.

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

/-- **An integral-root criterion for `Φₙ` and `ΨSqₙ`.**

If `x' * ΨSqₙ(x) = Φₙ(x)` and `x'` comes from `R`, then so does `x`: it is a root of the monic
`Φₙ − C c * ΨSqₙ`, and `R` is integrally closed in `A`.

That identity is the relation the `x`-coordinates of `P` and `n • P` would satisfy, which is why
this is the algebraic half of the Nagell–Lutz descent step — but that reading is motivation only:
no point, and no multiple, occurs in this statement. -/
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
