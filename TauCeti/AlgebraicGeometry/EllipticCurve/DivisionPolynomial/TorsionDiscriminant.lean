/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Discriminant
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.NagellLutz

/-!
# The discriminant companion of Nagell–Lutz

Over `ℤ`, a torsion point with integral coordinates either has `ψ₂ = 0` there or has `ψ₂²` dividing
`4Δ`. Writing `κ = ψ₂(x₀, y₀) = 2y₀ + a₁x₀ + a₃`, that is the classical `y = 0 ∨ y² ∣ Δ` disjunct
in the form a long Weierstrass model supports.

Over the fraction field of a general unique factorisation domain the same holds **given a
squarefreeness hypothesis**, exactly as in `NagellLutz.lean`: this route applies integrality at
`2 • P`, so what it needs is squarefreeness at the primes dividing that point's order. Over `ℤ`
that discharges for free, which is why the specialisation carries no arithmetic hypothesis.

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

* `WeierstrassCurve.evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ`: the companion over a UFD `R`,
  asking squarefreeness at the primes dividing `addOrderOf (2 • P)` — the point where the proof
  actually applies `isInteger_or_order_two_of_torsion_of_squarefree`.
* `WeierstrassCurve.evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ_of_squarefree`: the same conclusion
  from the more familiar hypothesis at `P` itself, which is strictly stronger.
* `WeierstrassCurve.evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ_rat`: the `ℤ`/`ℚ` specialisation,
  assuming only that the point is torsion with integral coordinates.

## Why the hypothesis sits at `2 • P`, and is not the sharp disjunction

`isInteger_or_order_two_of_torsion` takes a *sharp* guarded disjunction — `4 ∣ ord ∧ Squarefree 2`,
or some odd prime `p ∣ ord` with `Squarefree p` — and this file does **not** use it, for a reason
worth recording. Integrality is applied at `2 • P`, and that disjunction does not transfer along
`addOrderOf (2 • P) ∣ addOrderOf P`: at `addOrderOf P = 12` it is satisfied by its left disjunct,
supplying only `Squarefree (2 : R)`, whereas `addOrderOf (2 • P) = 6` has `4 ∤ 6` and so forces the
right disjunct, needing `Squarefree (3 : R)`, which nothing provided.

What *does* transfer is the all-primes condition, since the divisors of `addOrderOf (2 • P)` are
divisors of `addOrderOf P`. Stating it **at `2 • P`** rather than at `P` is therefore the weakest
form this route supports, and it needs no guard: when `P` has order two, `2 • P` is zero, no prime
divides `1`, and the hypothesis is vacuous of its own accord.

## Roadmap

New mathematics: `TauCetiRoadmap/EllipticCurves/README.md:821` — "**The torsion subgroup and
Nagell–Lutz**". Line `:827` names this target as `lutz_nagell_integrality_general`'s "discriminant
companion". The short-model sharpening is separate and already present, as
`CubicDiscriminant.lean`'s `sq_dvd_cubic_discr`.

## Provenance

Ported from J. Xu and D. K. Angdinata's
`projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`):
`kappa_sq_dvd_four_Psi3_of_torsion` (`:356`) and `lutz_nagell_pid_discriminant_of_torsion`
(`:415`). That file is byte-identical at `9fec8eba7652`, the revision the roadmap pins for this
project (`README:1072`), verified by blob hash, so the citations hold at either.

Two further declarations of that source file land elsewhere. `addOrderOf_ne_two_of_kappa_ne_zero`
(`:279`) is ported **into `ZSMul.lean`**, beside the `evalEval_ψ_eq_zero_of_zsmul_eq_zero` its
proof consumes, and **generalised** while there: the source states it over the fraction field of a
PID at integral coordinates, but nothing in the argument sees the base ring, so it is stated over
the point's own field and the transport across `algebraMap` happens here, at the call site.
`curveR_equation_of_isInteger` (`:266`) is not ported at all: it is Mathlib's
`Affine.map_equation` with the coordinates substituted, so this file applies that lemma directly.

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

/-- **The `Ψ₃` divisibility, from torsion.** For a torsion point with integral coordinates and
`κ = ψ₂(x₀, y₀) ≠ 0`, the square `κ²` divides `4·Ψ₃(x₀)`.

`κ ≠ 0` makes `2 • P` nonzero, so it has an affine representative `(x', y')`, and the cleared
doubling relation turns `Ψ₃(x₀)` into `(x₀ - x') · Ψ₂Sq(x₀) = (x₀ - x') · κ²`. Nagell–Lutz
integrality at `2 • P` then makes `x'` integral — or, in its order-two case, makes `4x'` integral,
and the `4` is already on the left. -/
private lemma sq_evalEval_ψ₂_dvd_four_mul_eval_Ψ₃ {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    (hsf : ∀ p : ℕ, p.Prime → p ∣ addOrderOf ((2 : ℕ) • Affine.Point.some _ _ hns) →
      Squarefree ((p : ℤ) : R))
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hEq : W.toAffine.Equation x₀ y₀)
    (hκK : (W.baseChange K).ψ₂.evalEval x y ≠ 0) :
    W.ψ₂.evalEval x₀ y₀ ^ 2 ∣ 4 * (W.Ψ₃).eval x₀ := by
  set P := Affine.Point.some _ _ hns
  have hord2 : addOrderOf P ≠ 2 :=
    addOrderOf_ne_two_of_evalEval_ψ₂_ne_zero (W.baseChange K) hns hκK
  have hord1 : addOrderOf P ≠ 1 := fun h ↦
    Affine.Point.some_ne_zero hns (AddMonoid.addOrderOf_eq_one_iff.mp h)
  have hpos : 0 < addOrderOf P := htor.addOrderOf_pos
  have h2P_ne : (2 : ℕ) • P ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf two_ne_zero (by omega)
  obtain ⟨x', y', hns', h2P_eq⟩ := Affine.Point.exists_eq_some_of_ne_zero h2P_ne
  -- The cleared doubling relation, then `Ψ₃ = (x - x') · Ψ₂Sq` over `K`.
  -- The doubling lemma is indexed by `ℤ`, so restate the doubling with an integer scalar.
  have h2P_zsmul : (2 : ℤ) • P = Affine.Point.some x' y' hns' := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from Nat.cast_ofNat.symm, natCast_zsmul]
    exact h2P_eq
  have hcoord := mul_eval_ΨSq_eq_eval_Φ_of_zsmul (W.baseChange K) hns hns' (n := 2) h2P_zsmul
  have hΨ₃K := eval_Ψ₃_eq_sub_mul_eval_Ψ₂Sq (W.baseChange K) hcoord
  -- Both evaluations descend: `Ψ₃` and `Ψ₂Sq` commute with base change, and on the curve
  -- `Ψ₂Sq(x₀) = κ²`.
  have hΨ₃ : ((W.baseChange K).Ψ₃).eval x = algebraMap R K ((W.Ψ₃).eval x₀) := by
    rw [← hx, WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_Ψ₃, eval_map,
      eval₂_at_apply]
  have hΨ₂Sq : ((W.baseChange K).Ψ₂Sq).eval x = algebraMap R K (W.ψ₂.evalEval x₀ y₀) ^ 2 := by
    rw [← hx, WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_Ψ₂Sq, eval_map,
      eval₂_at_apply, ← evalEval_ψ₂_sq W hEq, map_pow]
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
  rcases isInteger_or_order_two_of_torsion_of_squarefree W hns' (h2P_eq ▸ htor.nsmul)
      (fun _ p hp hpd ↦ hsf p hp (by rw [h2P_eq]; exact hpd)) with
    ⟨⟨x'₀, hx'₀⟩, _⟩ | ⟨_, ⟨n₀, hn₀⟩, _⟩
  · exact key (4 * x'₀) (by rw [map_mul, map_ofNat, hx'₀])
  · exact key n₀ hn₀

/-- **The discriminant companion of Nagell–Lutz.** For a torsion point with integral coordinates,
either `ψ₂` vanishes there — equivalently the point is two-torsion — or its square divides `4Δ`.

This is the second disjunct of the classical statement. The squarefreeness hypothesis is asked at
the primes dividing the order of `2 • P`, because that is the point at which the proof applies
Nagell–Lutz integrality; `evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ_of_squarefree` is the same
conclusion from the more familiar hypothesis at `P` itself. -/
theorem evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    (hsf : ∀ p : ℕ, p.Prime → p ∣ addOrderOf ((2 : ℕ) • Affine.Point.some _ _ hns) →
      Squarefree ((p : ℤ) : R))
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y) :
    W.ψ₂.evalEval x₀ y₀ = 0 ∨ W.ψ₂.evalEval x₀ y₀ ^ 2 ∣ 4 * W.Δ := by
  by_cases hκ : W.ψ₂.evalEval x₀ y₀ = 0
  · exact Or.inl hκ
  -- The point satisfies the equation over `R` itself, by injectivity of `algebraMap R K`.
  have hEq : W.toAffine.Equation x₀ y₀ :=
    (W.toAffine.map_equation (IsFractionRing.injective R K) x₀ y₀).mp (hx ▸ hy ▸ hns.left)
  -- `ψ₂` commutes with base change, so nonvanishing over `R` is nonvanishing over `K`.
  have hκK : (W.baseChange K).ψ₂.evalEval x y ≠ 0 := by
    have hbase : (W.baseChange K).ψ₂.evalEval x y = algebraMap R K (W.ψ₂.evalEval x₀ y₀) := by
      rw [← hx, ← hy, WeierstrassCurve.baseChange, map_ψ₂, map_mapRingHom_evalEval]
    rw [hbase]
    exact fun h ↦ hκ (IsFractionRing.injective R K (by rwa [map_zero]))
  -- On the curve `κ² = Ψ₂Sq(x₀)`, so the first premise is that equation read as a divisibility.
  refine Or.inr (dvd_four_mul_Δ_of_dvd_Ψ₂Sq_of_dvd_four_mul_Ψ₃ W (evalEval_ψ₂_sq W hEq).dvd ?_)
  exact sq_evalEval_ψ₂_dvd_four_mul_eval_Ψ₃ W hns htor hsf hx hEq hκK

/-- **The discriminant companion from a uniform hypothesis.** The same conclusion, asking
squarefreeness at every prime dividing the order of `P` itself.

That is strictly stronger than what the theorem above takes — the order of `2 • P` divides the
order of `P` — but it is the form a caller usually already has, needing no knowledge of what
doubling does to the order. The pair mirrors `isInteger_or_order_two_of_torsion` and its
`_of_squarefree` companion. -/
theorem evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ_of_squarefree {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    (hsf : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hns) →
      Squarefree ((p : ℤ) : R))
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y) :
    W.ψ₂.evalEval x₀ y₀ = 0 ∨ W.ψ₂.evalEval x₀ y₀ ^ 2 ∣ 4 * W.Δ := by
  refine evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ W hns htor (fun p hp hpd ↦ hsf p hp ?_) hx hy
  exact hpd.trans (addOrderOf_dvd_of_mem_zmultiples ⟨2, rfl⟩)

/-- **The discriminant companion over `ℚ`**, the form the roadmap asks for: for an integral long
Weierstrass model, a torsion point with integral coordinates has `ψ₂ = 0` there, or `ψ₂²` divides
`4Δ`. For a short model (`a₁ = a₃ = 0`) `ψ₂` is `2y`, so this reads `y = 0` or `4y² ∣ 4Δ`.

As with `isInteger_or_order_two_of_torsion_rat`, no arithmetic hypothesis survives: over `ℤ` a
rational prime is squarefree, so the general statement's hypothesis discharges outright. -/
theorem evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ_rat {W : WeierstrassCurve ℤ} {x y : ℚ}
    (hns : (W.baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    {x₀ y₀ : ℤ} (hx : algebraMap ℤ ℚ x₀ = x) (hy : algebraMap ℤ ℚ y₀ = y) :
    W.ψ₂.evalEval x₀ y₀ = 0 ∨ W.ψ₂.evalEval x₀ y₀ ^ 2 ∣ 4 * W.Δ :=
  evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ W hns htor
    (fun p hp _ ↦ by simpa using (Nat.prime_iff_prime_int.mp hp).squarefree) hx hy

end WeierstrassCurve
