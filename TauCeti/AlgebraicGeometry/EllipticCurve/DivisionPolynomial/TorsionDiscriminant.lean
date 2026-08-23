/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Discriminant
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.NagellLutz

/-!
# The discriminant companion of Nagell–Lutz

For a torsion point with integral coordinates, either `ψ₂` vanishes there or its square divides
`4Δ`. Writing `κ = ψ₂(x₀, y₀) = 2y₀ + a₁x₀ + a₃`, that is the classical `y = 0 ∨ y² ∣ Δ` disjunct
in the form a long Weierstrass model supports.

The arithmetic is already in `Discriminant.lean`, which proves — for any commutative ring, any `x`
and **any** divisor `d` — that `d ∣ Ψ₂Sq(x)` and `d ∣ 4·Ψ₃(x)` together give `d ∣ 4Δ`, by an
explicit Bézout certificate in the `b`-invariants. What this file adds is the torsion input that
discharges the second premise, which that file deliberately left open: *"its hypothesis
`κ² ∣ 4·Ψ₃(x)` is supplied by point-level `[n]`-multiplication material that is not yet in this
repository"*. It is now, so the premise can be met.

The route is doubling. `κ ≠ 0` forces `2 • P ≠ 0`, so `2 • P` has an affine representative
`(x', y')`, and the cleared doubling relation `x' · ΨSq₂(x₀) = Φ₂(x₀)` turns `Ψ₃(x₀)` into
`(x₀ - x') · Ψ₂Sq(x₀)`, which on the curve is `(x₀ - x') · κ²`. Nagell–Lutz integrality applied at
`2 • P` makes `x'` integral — or, in its order-two case, makes `4x'` integral — and either way the
`4` already present on the left absorbs the difference.

## Main results

* `WeierstrassCurve.evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ`: the companion over a UFD `R`, with
  the guarded squarefreeness hypothesis `isInteger_or_order_two_of_torsion` takes.
* `WeierstrassCurve.evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ_rat`: the `ℤ`/`ℚ` specialisation,
  assuming only that the point is torsion with integral coordinates.
* `WeierstrassCurve.addOrderOf_ne_two_of_evalEval_ψ₂_ne_zero`: `ψ₂ ≠ 0` rules out order two, which
  is what discharges the guard on the squarefreeness hypothesis.
* `WeierstrassCurve.equation_of_algebraMap_eq`: the curve equation descends along `algebraMap R K`.
* `WeierstrassCurve.evalEval_ψ₂_baseChange_of_algebraMap_eq`: `ψ₂` commutes with base change at an
  integral point, so `κ` may be read either over `R` or over `K`.

## Roadmap

New mathematics: `TauCetiRoadmap/EllipticCurves/README.md:821` — "**The torsion subgroup and
Nagell–Lutz**". Line `:827` names this target as `lutz_nagell_integrality_general`'s "discriminant
companion". The short-model sharpening is separate and already present, as
`CubicDiscriminant.lean`'s `sq_dvd_cubic_discr`.

## Provenance

Ported from J. Xu and D. K. Angdinata's
`projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`):
`curveR_equation_of_isInteger` (`:266`), `addOrderOf_ne_two_of_kappa_ne_zero` (`:279`),
`kappa_sq_dvd_four_Psi3_of_torsion` (`:356`) and `lutz_nagell_pid_discriminant_of_torsion`
(`:415`). That file is byte-identical at `9fec8eba7652`, the revision the roadmap pins for this
project (`README:1072`), verified by blob hash, so the citations hold at either.

**Most of the source's discriminant section is not ported, because this repository already carries
it.** `kappa_sq_eq_Psi2Sq` (`:183`), `bezout_identity` (`:192`) and `kappa_sq_dvd_four_delta`
(`:202`) are `Discriminant.lean`'s `evalEval_ψ₂_sq`, `bezout_four_mul_Δ` and
`dvd_four_mul_Δ_of_dvd_Ψ₂Sq_of_dvd_four_mul_Ψ₃` — the last of which is *more general*, taking an
arbitrary `d` where the source fixes `κ²`. The four `eval`-level wrappers (`:300`–`:352`) collapse
into `Basic.lean`'s `eval_Ψ₃_eq_sub_mul_eval_Ψ₂Sq`, and `isInteger_mul_of_den_dvd` (`:338`) is
`NumDen.lean`'s `den_dvd_iff_isInteger_mul`. The source's `lutz_nagell_pid_discriminant` (`:242`)
is likewise declined: it is the on-curve specialisation of the general divisibility, and stating
it separately would add a name for what the headline below already does with the point in hand.

Two adaptations. The base ring is a **UFD**, matching `Torsion.lean` and
`isInteger_or_order_two_of_torsion`, rather than the source's principal ideal domain of
characteristic zero. And `κ` is written as `W.ψ₂.evalEval x₀ y₀` rather than the raw
`2y₀ + a₁x₀ + a₃`, so that `evalEval_ψ₂_sq` applies without a normalisation step.
-/

public section

open Polynomial

namespace WeierstrassCurve

open TauCeti.WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
variable (W : WeierstrassCurve R)

/-- **A nonzero affine point is `.some`.** `Affine.Point` has two constructors, so this is the
`rcases` that names the coordinates and their nonsingularity certificate. Local proof plumbing:
no field structure and no discriminant content, so it stays private rather than joining the
public API. -/
private lemma exists_eq_some_of_ne_zero {F : Type*} [CommRing F] {E : WeierstrassCurve F}
    {P : Affine.Point E.toAffine} (hP : P ≠ 0) :
    ∃ x y, ∃ hns : E.toAffine.Nonsingular x y, P = .some _ _ hns := by
  rcases P with _ | ⟨_, _, hns⟩
  · exact absurd rfl hP
  · exact ⟨_, _, hns, rfl⟩

omit [IsDomain R] [UniqueFactorizationMonoid R] [DecidableEq K] in
/-- **The curve equation descends to `R`.** A point of the base-changed curve whose coordinates
are integral satisfies the equation over `R` itself. -/
lemma equation_of_algebraMap_eq {x y : K} (h : (W.baseChange K).toAffine.Equation x y)
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y) :
    W.toAffine.Equation x₀ y₀ :=
  (W.toAffine.map_equation (IsFractionRing.injective R K) x₀ y₀).mp (hx ▸ hy ▸ h)

omit [IsDomain R] [UniqueFactorizationMonoid R] [DecidableEq K] [IsFractionRing R K] in
/-- **`ψ₂` commutes with base change at an integral point.** -/
lemma evalEval_ψ₂_baseChange_of_algebraMap_eq {x y : K}
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y) :
    (W.baseChange K).ψ₂.evalEval x y = algebraMap R K (W.ψ₂.evalEval x₀ y₀) := by
  rw [← hx, ← hy, WeierstrassCurve.baseChange, map_ψ₂, map_mapRingHom_evalEval]

omit [IsDomain R] [UniqueFactorizationMonoid R] in
/-- **A point with `ψ₂ ≠ 0` is not two-torsion.** Order two forces `ψ₂` to vanish at the point,
so a nonvanishing `ψ₂` rules it out. This is what supplies the `addOrderOf ≠ 2` side condition
that Nagell–Lutz integrality needs at `2 • P`. -/
lemma addOrderOf_ne_two_of_evalEval_ψ₂_ne_zero {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y)
    (hκ : W.ψ₂.evalEval x₀ y₀ ≠ 0) :
    addOrderOf (Affine.Point.some _ _ hns) ≠ 2 := by
  intro h2
  have h2P : (2 : ℕ) • Affine.Point.some _ _ hns = 0 := by
    rw [← h2]; exact addOrderOf_nsmul_eq_zero _
  have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero (W.baseChange K) hns 2
    (zsmul_fromAffine_eq_zero_iff.mpr h2P)
  rw [WeierstrassCurve.ψ_two] at hψ
  refine hκ (IsFractionRing.injective R K ?_)
  rw [map_zero, ← evalEval_ψ₂_baseChange_of_algebraMap_eq W hx hy]
  exact hψ

/-- **The `Ψ₃` divisibility, from torsion.** For a torsion point with integral coordinates and
`κ = ψ₂(x₀, y₀) ≠ 0`, the square `κ²` divides `4·Ψ₃(x₀)`.

`κ ≠ 0` makes `2 • P` nonzero, so it has an affine representative `(x', y')`, and the cleared
doubling relation turns `Ψ₃(x₀)` into `(x₀ - x') · Ψ₂Sq(x₀) = (x₀ - x') · κ²`. Nagell–Lutz
integrality at `2 • P` then makes `x'` integral — or, in its order-two case, makes `4x'` integral,
and the `4` is already on the left. -/
private lemma sq_evalEval_ψ₂_dvd_four_mul_eval_Ψ₃ {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    (hsf : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hns) →
      Squarefree ((p : ℤ) : R))
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y)
    (hκ : W.ψ₂.evalEval x₀ y₀ ≠ 0) :
    W.ψ₂.evalEval x₀ y₀ ^ 2 ∣ 4 * (W.Ψ₃).eval x₀ := by
  set P := Affine.Point.some _ _ hns
  have hord2 : addOrderOf P ≠ 2 := addOrderOf_ne_two_of_evalEval_ψ₂_ne_zero W hns hx hy hκ
  have hord1 : addOrderOf P ≠ 1 := fun h ↦
    Affine.Point.some_ne_zero hns (AddMonoid.addOrderOf_eq_one_iff.mp h)
  have hpos : 0 < addOrderOf P := htor.addOrderOf_pos
  have h2P_ne : (2 : ℕ) • P ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf two_ne_zero (by omega)
  obtain ⟨x', y', hns', h2P_eq⟩ := exists_eq_some_of_ne_zero h2P_ne
  -- The cleared doubling relation, then `Ψ₃ = (x - x') · Ψ₂Sq` over `K`.
  have hcoord := mul_eval_ΨSq_eq_eval_Φ_of_zsmul (W.baseChange K) hns hns'
    (n := 2) (by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, natCast_zsmul]; exact h2P_eq)
  have hΨ₃K := eval_Ψ₃_eq_sub_mul_eval_Ψ₂Sq (W.baseChange K) hcoord
  -- Both evaluations descend: `Ψ₃` and `Ψ₂Sq` commute with base change, and on the curve
  -- `Ψ₂Sq(x₀) = κ²`.
  have hΨ₃ : ((W.baseChange K).Ψ₃).eval x = algebraMap R K ((W.Ψ₃).eval x₀) := by
    rw [← hx, WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_Ψ₃, eval_map,
      eval₂_at_apply]
  have hΨ₂Sq : ((W.baseChange K).Ψ₂Sq).eval x = algebraMap R K (W.ψ₂.evalEval x₀ y₀) ^ 2 := by
    rw [← hx, WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_Ψ₂Sq, eval_map,
      eval₂_at_apply, ← evalEval_ψ₂_sq W (equation_of_algebraMap_eq W hns.left hx hy), map_pow]
  rw [hΨ₃, hΨ₂Sq] at hΨ₃K
  -- Nagell–Lutz at `2 • P`. Both disjuncts hand back the same datum — some `c : R` with
  -- `c = 4x'` — so the divisibility is extracted once rather than twice: the integral case
  -- supplies `c = 4x'₀`, the order-two case supplies `c` directly from the `4x'` bound.
  have hinj := IsFractionRing.injective R K
  have key : ∀ c : R, algebraMap R K c = 4 * x' →
      W.ψ₂.evalEval x₀ y₀ ^ 2 ∣ 4 * (W.Ψ₃).eval x₀ := fun c hc ↦
    ⟨4 * x₀ - c, hinj <| by
      simp only [map_mul, map_sub, map_pow, map_ofNat, hx, hc]
      linear_combination (norm := ring_nf) 4 * hΨ₃K⟩
  have hdvd : addOrderOf (Affine.Point.some _ _ hns') ∣ addOrderOf P := by
    rw [← h2P_eq]; exact addOrderOf_dvd_of_mem_zmultiples ⟨2, rfl⟩
  rcases isInteger_or_order_two_of_torsion_of_squarefree W hns' (h2P_eq ▸ htor.nsmul)
      (fun _ p hp hpd ↦ hsf p hp (hpd.trans hdvd)) with
    ⟨⟨x'₀, hx'₀⟩, _⟩ | ⟨_, ⟨n₀, hn₀⟩, _⟩
  · exact key (4 * x'₀) (by rw [map_mul, map_ofNat, hx'₀])
  · exact key n₀ hn₀

/-- **The discriminant companion of Nagell–Lutz.** For a torsion point with integral coordinates,
either `ψ₂` vanishes there — equivalently the point is two-torsion — or its square divides `4Δ`.

This is the second disjunct of the classical statement. The squarefreeness hypothesis is the
guarded one that `isInteger_or_order_two_of_torsion` takes, and its guard is discharged here for
free: on the branch that uses it, `ψ₂ ≠ 0` has already ruled order two out. -/
theorem evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    (hsf : addOrderOf (Affine.Point.some _ _ hns) ≠ 2 →
      ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hns) →
        Squarefree ((p : ℤ) : R))
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y) :
    W.ψ₂.evalEval x₀ y₀ = 0 ∨ W.ψ₂.evalEval x₀ y₀ ^ 2 ∣ 4 * W.Δ := by
  by_cases hκ : W.ψ₂.evalEval x₀ y₀ = 0
  · exact Or.inl hκ
  -- On the curve `κ² = Ψ₂Sq(x₀)`, so the first premise is that equation read as a divisibility.
  refine Or.inr (dvd_four_mul_Δ_of_dvd_Ψ₂Sq_of_dvd_four_mul_Ψ₃ W
    (evalEval_ψ₂_sq W (equation_of_algebraMap_eq W hns.left hx hy)).dvd ?_)
  exact sq_evalEval_ψ₂_dvd_four_mul_eval_Ψ₃ W hns htor
    (hsf (addOrderOf_ne_two_of_evalEval_ψ₂_ne_zero W hns hx hy hκ)) hx hy hκ

/-- **The discriminant companion over `ℚ`**, the form the roadmap asks for: for an integral long
Weierstrass model, a torsion point with integral coordinates has `ψ₂ = 0` there, or `ψ₂²` divides
`4Δ`. For a short model (`a₁ = a₃ = 0`) `ψ₂` is `2y`, so this reads `y = 0` or `4y² ∣ 4Δ`.

As with `isInteger_or_order_two_of_torsion_rat`, no arithmetic hypothesis survives: over `ℤ` a
rational prime is squarefree, so the general statement's guarded hypothesis discharges outright. -/
theorem evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ_rat {W : WeierstrassCurve ℤ} {x y : ℚ}
    (hns : (W.baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    {x₀ y₀ : ℤ} (hx : algebraMap ℤ ℚ x₀ = x) (hy : algebraMap ℤ ℚ y₀ = y) :
    W.ψ₂.evalEval x₀ y₀ = 0 ∨ W.ψ₂.evalEval x₀ y₀ ^ 2 ∣ 4 * W.Δ :=
  evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ W hns htor
    (fun _ p hp _ ↦ by simpa using (Nat.prime_iff_prime_int.mp hp).squarefree) hx hy

end WeierstrassCurve
