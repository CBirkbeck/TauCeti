/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointImage
-- Proof-only: the tautological point is the generic point pushed along the pullback.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.GenericPoint

/-!
# The Frobenius acts on points as the `q`-power map

Let `W` be an elliptic curve over a finite field `F` with `q` elements, and `K` an extension of
`F`. The `q`-power Frobenius isogeny of `W` base-changes to an isogeny `π` of `W⁄K`, whose
pullback raises the functions defined over `F` to the `q`-th power. This file shows that `π` acts
on the points of `W` over `K` as the `q`-power map on coordinates:

    π (x, y) = (x ^ q, y ^ q),

the point map induced by the `q`-power Frobenius of `K` over `F`. This is the lemma "the
Frobenius isogeny induces `(x, y) ↦ (x ^ q, y ^ q)` on points" of the roadmap's Hasse bound.

The proof reads `π (P)` as the reduction of the tautological point
`(genericX ^ q, genericY ^ q)` at the place of `P` (`TauCeti.Isogeny.pointImage`). For
`P = (a, b)`, `genericX ^ q - a ^ q = (genericX - a) ^ q` vanishes at the place of `P` because
`genericX - a` does, and likewise for `y`; for `P = O`, `genericX ^ q` has a pole at infinity
because `genericX` does.

## Main definitions

* `TauCeti.Isogeny.baseChangeFrobenius`: the `q`-power Frobenius of `W`, as an isogeny of `W⁄K`.

## Main results

* `TauCeti.Isogeny.fieldPullback_baseChangeFrobenius_genericX` and
  `TauCeti.Isogeny.fieldPullback_baseChangeFrobenius_genericY`: its pullback raises the generic
  coordinates to the `q`-th power.
* `TauCeti.Isogeny.pointImage_baseChangeFrobenius`: it acts on points as
  `Point.map (FiniteField.frobeniusAlgHom F K)`, the `q`-power map on coordinates.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11, V.1.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K] (W : WeierstrassCurve.Affine F)

variable (K) in
/-- **The Frobenius of `W` over an extension `K` of its finite base**: the base change of the
`q`-power Frobenius isogeny, read as an isogeny of `W⁄K`. -/
noncomputable def baseChangeFrobenius : Isogeny (W⁄K).toAffine (W⁄K).toAffine :=
  (frobeniusIsogeny W).map (algebraMap F K)

/-- **The pullback of `baseChangeFrobenius` raises the functions defined over `F` to the `q`-th
power.** -/
theorem fieldPullback_baseChangeFrobenius_map (z : W.FunctionField) :
    (baseChangeFrobenius K W).fieldPullback (FunctionField.map W (algebraMap F K) z) =
      FunctionField.map W (algebraMap F K) z ^ Nat.card F := by
  refine (map_fieldPullback_map (frobeniusIsogeny W) (algebraMap F K) z).trans ?_
  rw [fieldPullback_frobeniusIsogeny_apply, map_pow]

/-- **The pullback of `baseChangeFrobenius` raises the generic `x`-coordinate to the `q`-th
power.** -/
theorem fieldPullback_baseChangeFrobenius_genericX :
    (baseChangeFrobenius K W).fieldPullback (genericX (W⁄K).toAffine) =
      genericX (W⁄K).toAffine ^ Nat.card F :=
  FunctionField.map_genericX W (algebraMap F K) ▸ fieldPullback_baseChangeFrobenius_map W _

/-- **The pullback of `baseChangeFrobenius` raises the generic `y`-coordinate to the `q`-th
power.** -/
theorem fieldPullback_baseChangeFrobenius_genericY :
    (baseChangeFrobenius K W).fieldPullback (genericY (W⁄K).toAffine) =
      genericY (W⁄K).toAffine ^ Nat.card F :=
  FunctionField.map_genericY W (algebraMap F K) ▸ fieldPullback_baseChangeFrobenius_map W _

-- In a ring receiving the finite field `F`, raising to the order of `F` is additive.
private theorem sub_pow_natCard {L : Type*} [CommRing L] (g : F →+* L) (x y : L) :
    (x - y) ^ Nat.card F = x ^ Nat.card F - y ^ Nat.card F := by
  let _ := g.toAlgebra
  let _ := Fintype.ofFinite F
  simpa only [FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card] using
    map_sub (FiniteField.frobeniusAlgHom F L) x y

variable [DecidableEq K] [W.IsElliptic]

/-- **The Frobenius acts on points as the `q`-power map on coordinates**: `π (x, y) = (x^q, y^q)`,
the point map induced by the `q`-power Frobenius of `K` over `F`. -/
theorem pointImage_baseChangeFrobenius (P : (W⁄K).toAffine.Point) :
    letI := Fintype.ofFinite F
    (baseChangeFrobenius K W).pointImage P = Point.map (FiniteField.frobeniusAlgHom F K) P := by
  let _ := Fintype.ofFinite F
  have hq : Nat.card F ≠ 0 := Nat.card_pos.ne'
  rw [pointImage_eq_iff, tautologicalPoint_eq_map_genericPoint, genericPoint_eq_some,
    Point.map_some]
  rcases P with _ | ⟨a, b, h⟩
  · rw [coe_pointEquivDegreeOnePlace_zero, ← Point.zero_def, map_zero, map_zero, map_zero,
      sub_zero, mem_polePoints_iff, Point.xCoord_some]
    refine Or.inr ?_
    rw [fieldPullback_baseChangeFrobenius_genericX, map_pow, Place.valuation_infinity,
      genericX_eq_algebraMap]
    exact one_lt_pow₀ (one_lt_infinityPlace_X _) hq
  · have hQ : (W⁄K).toAffine.Nonsingular (FiniteField.frobeniusAlgHom F K a)
        (FiniteField.frobeniusAlgHom F K b) :=
      (W.baseChange_nonsingular (FiniteField.frobeniusAlgHom F K).injective a b).mpr h
    have hQ' : ((W⁄K).toAffine⁄K).toAffine.Nonsingular (FiniteField.frobeniusAlgHom F K a)
        (FiniteField.frobeniusAlgHom F K b) :=
      ((W⁄K).toAffine.map_nonsingular (algebraMap K K).injective _ _).mpr hQ
    -- a constant of `F(W⁄K)` raised to the `q`-th power is the image of its `q`-power Frobenius
    have hc (c : K) :
        algebraMap K (W⁄K).toAffine.FunctionField (FiniteField.frobeniusAlgHom F K c) =
          algebraMap K _ c ^ Nat.card F := by
      rw [FiniteField.coe_frobeniusAlgHom, map_pow, Nat.card_eq_fintype_card]
    have hsub :=
      sub_pow_natCard ((algebraMap K (W⁄K).toAffine.FunctionField).comp (algebraMap F K))
    rw [Point.map_some, Point.equivBaseChangeSelf_some _ _ hQ',
      some_sub_baseChange_mem_polePoints_iff, coe_pointEquivDegreeOnePlace_some,
      fieldPullback_baseChangeFrobenius_genericX, fieldPullback_baseChangeFrobenius_genericY, hc,
      hc, ← hsub, ← hsub, map_pow, map_pow]
    exact ⟨pow_lt_one₀ zero_le (valuation_pointPlace_genericX_sub_lt_one _ h.1) hq,
      pow_lt_one₀ zero_le (valuation_pointPlace_genericY_sub_lt_one _ h.1) hq⟩

end TauCeti.Isogeny

end
