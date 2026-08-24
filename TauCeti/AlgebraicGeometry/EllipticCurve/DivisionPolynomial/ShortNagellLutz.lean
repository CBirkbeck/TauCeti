/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Discriminant
-- Proof-only, and not reachable transitively: `Torsion/Discriminant.lean` imports this
-- module non-publicly, so `evalEval_ψ₂_of_isCharNeTwoNF` is not re-exported through it.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.ShortWeierstrass

/-!
# The Nagell–Lutz theorem for a short Weierstrass model

For `A B : ℤ`, a nonzero rational point of finite order on `y² = x³ + Ax + B` has **integral**
coordinates, and its `y`-coordinate satisfies `y = 0` or `y² ∣ Δ`. That is the classical
statement, and unlike the long-model theorem it has no order-two exception.

The exception disappears for a computable reason rather than by assumption. On a short model
`a₁ = a₃ = 0`, so `ψ₂ = 2y`; a point of order two makes `ψ₂` vanish, hence `y = 0`, and then the
curve equation exhibits `x` as a rational root of the **monic** `X³ + AX + B`, so `x` is an
integer too. The long model's honest bound `4x, 8y ∈ ℤ` therefore sharpens to full integrality
exactly here.

The same collapse turns the discriminant companion into its classical form: it gives
`ψ₂ = 0 ∨ ψ₂² ∣ 4Δ`, and substituting `ψ₂ = 2y₀` yields `2y₀ = 0 ∨ 4y₀² ∣ 4Δ`, from which the `4`
cancels on both sides.

**No `Δ ≠ 0` hypothesis.** The source carries one on all three of its headline theorems and uses
it in none of them; what the argument needs is that the *point* is nonsingular, not that the curve
is elliptic. See the Provenance note.

## Main results

* `WeierstrassCurve.lutz_nagell`: the theorem — integral coordinates together with
  `y₀ = 0 ∨ y₀² ∣ Δ`.
* `WeierstrassCurve.isInteger_of_torsion_short`: the integrality half on its own, with no
  order-two exception.
* `WeierstrassCurve.y_eq_zero_or_sq_dvd_Δ_of_torsion_short`: the discriminant half on its own.
* `WeierstrassCurve.y_eq_zero_of_order_two_short`: the collapse — order two forces `y = 0`.

## Roadmap

New mathematics: `TauCetiRoadmap/EllipticCurves/README.md:821` — "**The torsion subgroup and
Nagell–Lutz**". Lines `:828`–`:830` name this target: for an integral **short** model
`y² = x³ + Ax + B`, "the classical full form — `x, y ∈ ℤ` and `y = 0` or `y² ∣ Δ`
(`lutz_nagell`; AEC VIII.7)".

## Provenance

Ported from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), from two files whose authorship differs and is
credited separately.

**`LutzNagellTheorem/Main.lean` — `Authors: Chris Birkbeck`.** All three headline theorems come
from it: `lutz_nagell_integrality` (`:40`), `lutz_nagell_discriminant` (`:53`) and `lutz_nagell`
(`:71`). That file carries its own author header, so it is credited to Chris Birkbeck rather than
to the project's usual pair, and the header of this file names them accordingly.

**`LutzNagellTheorem/GeneralMain.lean` — no author header.** Its
`lutz_nagell_integrality_short` (`:155`) is where the order-two collapse is carried out; with no
header to go on it is credited to the project, as the sibling ports in this chain are.

**The `Δ ≠ 0` hypothesis is dropped.** All three source theorems take
`hΔ : (shortCurveZ A B).Δ ≠ 0`; none uses it. It occurs in the three signatures and twice in the
bodies, both times in `lutz_nagell` forwarding it to the two theorems whose proofs never mention
it — a pass-through of a hypothesis nothing consumes, which this repository's `unusedArguments`
linter would reject in any case.

One further adaptation: `ψ₂ = 2y` is stated over an arbitrary commutative ring, since the point
lives over `ℚ` while the conclusion is over `ℤ` and both need it. The monic-root step follows the
source and goes through `isInteger_of_is_root_of_monic` — Mathlib's, which is what the source's
own lemma of that name restates.
-/

public section

open Polynomial

namespace WeierstrassCurve

open TauCeti.WeierstrassCurve

variable (A B : ℤ)

/-- **Nagell–Lutz, discriminant half, short model.** For a torsion point with integral coordinates
on `y² = x³ + Ax + B`, either `y₀ = 0` or `y₀²` divides the discriminant.

The general companion gives `ψ₂ = 0 ∨ ψ₂² ∣ 4Δ`; here `ψ₂ = 2y₀`, so the first disjunct is
`2y₀ = 0` and the second is `4y₀² ∣ 4Δ`, and the `4` cancels on both sides. -/
theorem y_eq_zero_or_sq_dvd_Δ_of_torsion_short {x y : ℚ}
    (hns : ((shortCurve A B).baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    {x₀ y₀ : ℤ} (hx : algebraMap ℤ ℚ x₀ = x) (hy : algebraMap ℤ ℚ y₀ = y) :
    y₀ = 0 ∨ y₀ ^ 2 ∣ (shortCurve A B).Δ := by
  rcases evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ_rat hns htor hx hy with hκ | hdvd
  · rw [evalEval_ψ₂_of_isCharNeTwoNF] at hκ
    exact Or.inl (by omega)
  · refine Or.inr ?_
    rw [evalEval_ψ₂_of_isCharNeTwoNF] at hdvd
    ring_nf at hdvd
    exact (mul_dvd_mul_iff_right (by norm_num : (4 : ℤ) ≠ 0)).mp hdvd

/-- **For a short model, a two-torsion point has `y = 0`.** Order two makes `ψ₂` vanish, and on a
short model `ψ₂` is `2y`. This is exactly what collapses the long model's `4x, 8y` exception into
the classical statement.

Nothing here sees `ℤ` or `ℚ`: the argument needs the short-model identity and the ability to
cancel `2` in the point's own field, so those are the hypotheses. The curve is taken up to
equality with a short model rather than as one, which is what lets a caller holding a
*base-changed* short curve apply it — `baseChange_shortCurve` is the equality, and `subst`
transports the point and its order along with it. -/
lemma y_eq_zero_of_order_two_short {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve F} {a b : F} (hW : W = shortCurve a b) (h2F : (2 : F) ≠ 0)
    {x y : F} (hns : W.toAffine.Nonsingular x y)
    (h2 : addOrderOf (Affine.Point.some _ _ hns) = 2) : y = 0 := by
  subst hW
  have hψ : (shortCurve a b).ψ₂.evalEval x y = 0 :=
    (addOrderOf_eq_two_iff_evalEval_ψ₂_eq_zero _ hns).mp h2
  rw [evalEval_ψ₂_of_isCharNeTwoNF] at hψ
  exact (mul_eq_zero.mp hψ).resolve_left h2F

/-- **Nagell–Lutz, integrality half, short model.** On `y² = x³ + Ax + B` a nonzero torsion point
has integral coordinates — with *no* order-two exception.

The long-model theorem leaves order two aside with only `4x, 8y ∈ ℤ`. Here that case collapses:
`ψ₂ = 2y`, so order two forces `y = 0`, and then `x` is a rational root of the monic
`X³ + AX + B`, hence an integer. -/
theorem isInteger_of_torsion_short {x y : ℚ}
    (hns : ((shortCurve A B).baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns)) :
    IsLocalization.IsInteger ℤ x ∧ IsLocalization.IsInteger ℤ y := by
  rcases isInteger_or_order_two_of_torsion_rat hns htor with h | ⟨h2, -, -⟩
  · exact h
  · have hy : y = 0 := y_eq_zero_of_order_two_short (baseChange_shortCurve A B) two_ne_zero hns h2
    refine ⟨?_, hy ▸ ⟨0, by simp⟩⟩
    -- With `y = 0` the curve equation exhibits `x` as a rational root of the monic `X³ + AX + B`,
    -- and Mathlib's integral root theorem over the UFD `ℤ` finishes.
    have hmonic : (X ^ 3 + C A * X + C B : ℤ[X]).Monic := by
      simpa [add_assoc] using monic_X_pow_add (n := 3) (by compute_degree!)
    have heq := hns.left
    -- `baseChange_shortCurve` leaves the coefficients as `algebraMap ℤ ℚ`, where `aeval` reads
    -- them as `Int.cast`, so normalise before transferring.
    rw [baseChange_shortCurve, shortCurve_equation_iff] at heq
    rw [hy] at heq
    simp only [algebraMap_int_eq, eq_intCast] at heq
    exact isInteger_of_is_root_of_monic hmonic
      (by simpa using (by linarith : x ^ 3 + (A : ℚ) * x + (B : ℚ) = 0))

/-- **The Nagell–Lutz theorem.** Let `A B : ℤ` and let `(x, y)` be a nonzero rational point of
finite order on `y² = x³ + Ax + B`. Then `x` and `y` are integers, and either `y = 0` or
`y² ∣ Δ`.

This is the classical statement, and the form
`TauCetiRoadmap/EllipticCurves/README.md:830` names `lutz_nagell`. No hypothesis `Δ ≠ 0` is
needed — see the module docstring. -/
theorem lutz_nagell {x y : ℚ}
    (hns : ((shortCurve A B).baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns)) :
    ∃ x₀ y₀ : ℤ, (x₀ : ℚ) = x ∧ (y₀ : ℚ) = y ∧
      (y₀ = 0 ∨ y₀ ^ 2 ∣ (shortCurve A B).Δ) := by
  obtain ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩ := isInteger_of_torsion_short A B hns htor
  exact ⟨x₀, y₀, by simpa using hx₀, by simpa using hy₀,
    y_eq_zero_or_sq_dvd_Δ_of_torsion_short A B hns htor hx₀ hy₀⟩

end WeierstrassCurve
