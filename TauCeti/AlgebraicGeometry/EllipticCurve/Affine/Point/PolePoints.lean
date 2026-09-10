/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Range
import TauCeti.FieldTheory.FunctionField.AffineModel.Place

/-!
# The points with a pole at a place form a subgroup

Let `W` be an elliptic curve over `F`, let `K` be a field extension of `F` and let `P` be a place
of `K / F`. A point of `W` over `K` either has both coordinates in the valuation ring of `P` or has
a pole of `x` there (`Affine/ValuationIntegrality.lean`). This file shows that the points with a
pole, together with the point at infinity, are closed under the group law, and packages them as a
subgroup of `W(K)`. Classically this is the kernel `E₁(K_P)` of reduction at `P` (Silverman
VII.2.2); no reduction map on points is constructed here, the subgroup being cut out by the
valuation of the `x`-coordinate alone.

The proof passes through the completion of `K` at `P`. A place is the adic place of the maximal
ideal of its own valuation ring, which is a Dedekind domain (`TauCeti.Place.center`), so
`FormalGroup/Point/Range.lean` applies at the completion: the parametrisation of points by the
formal group is an additive homomorphism whose range is exactly the set of points with a pole of
`x`, and the range of an additive homomorphism is closed under addition. Points transport along
the completion map, which is injective and preserves the valuation of the coordinates, so the
closure descends to `K`.

## Main definitions

* `WeierstrassCurve.Affine.polePoints`: the subgroup of `W(K)` of points whose `x`-coordinate has
  a pole at `P`, together with the point at infinity.

## Main results

* `WeierstrassCurve.Affine.one_lt_valuation_xCoord_add`: a pole of `x` at `P` is preserved by
  addition of points, as long as the sum is not the point at infinity.
* `WeierstrassCurve.Affine.mem_polePoints_iff`: membership in `polePoints`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.2.

## Provenance

The closure under addition composes two results already in this repository:
`WeierstrassCurve.range_formalPointHomAdicCompletion` (`FormalGroup/Point/Range.lean`, itself
adapted from Michael Stoll's `EllipticCurves` development, see that file) and
`TauCeti.Place.center` (`FieldTheory/FunctionField/AffineModel/Place.lean`). The AINTLIB
`HasseWeil` project (Chris Birkbeck, Apache-2.0, `513e83879e2f8cbc626eb9e04d660e92be16ccba`) records
the same fact — "the kernel of reduction at `O` is closed under addition" — in
`HasseWeil/FormalIsogenySeries.lean` for the function field of the curve at its own point at
infinity, proved through formal isogeny series; nothing is taken from that proof, the statement
here being for an arbitrary place of an arbitrary extension and the argument going through the
completion instead.
-/

public section

open IsDedekindDomain WeierstrassCurve

namespace WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **A pole of `x` at a place is preserved by addition of points.** If the `x`-coordinates of two
points of `W` over `K` both have a pole at the place `P`, and the points do not cancel, then the
`x`-coordinate of their sum has a pole at `P` too. -/
theorem one_lt_valuation_xCoord_add (P : TauCeti.Place F K) {Q₁ Q₂ : (W⁄K).toAffine.Point}
    (h₁ : 1 < P.valuation Q₁.xCoord) (h₂ : 1 < P.valuation Q₂.xCoord) (h : Q₁ + Q₂ ≠ 0) :
    1 < P.valuation (Q₁ + Q₂).xCoord := by
  classical
  -- The place is the adic place of the maximal ideal of its own valuation ring.
  set u : HeightOneSpectrum P.integers := P.center (R := P.integers) fun r ↦ r.2 with hu_def
  have hu : u.valuation K = P.valuation := P.valuation_center _
  have hval : ∀ x : K, Valued.v (algebraMap K (u.adicCompletion K) x) = P.valuation x := fun x ↦
    (u.valuedAdicCompletion_eq_valuation' x).trans (congrFun (congrArg DFunLike.coe hu) x)
  -- Constants are integral in the completion, so the curve has a model over its integers.
  have hF : ∀ c : F, algebraMap F (u.adicCompletion K) c ∈ u.adicCompletionIntegers K := fun c ↦ by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show algebraMap F (u.adicCompletion K) c = algebraMap K _ (algebraMap F K c) from rfl, hval]
    exact Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _
  let _ : Algebra F (u.adicCompletionIntegers K) :=
    ((algebraMap F (u.adicCompletion K)).codRestrict _ hF).toAlgebra
  have : IsScalarTower F (u.adicCompletionIntegers K) (u.adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsLinearTopology (u.adicCompletionIntegers K) (u.adicCompletionIntegers K) :=
    u.isAdic_maximalIdeal_adicCompletionIntegers (K := K) ▸ Ideal.isLinearTopology _
  have : Fact (IsAdic (IsLocalRing.maximalIdeal (u.adicCompletionIntegers K))) :=
    ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := K)⟩
  let C : WeierstrassCurve (u.adicCompletionIntegers K) := W.map (algebraMap F _)
  have hC : C.baseChange (u.adicCompletion K) = W⁄(u.adicCompletion K) := rfl
  have : (C.baseChange (u.adicCompletion K)).IsElliptic := by rw [hC]; infer_instance
  let ι : K →ₐ[F] u.adicCompletion K := IsScalarTower.toAlgHom F K _
  have hι : ∀ x : K, ι x = algebraMap K (u.adicCompletion K) x := fun _ ↦ rfl
  -- The range of the formal parametrisation, read on the points of `W` over the completion.
  have hrange : ∀ Q' : (W⁄(u.adicCompletion K)).toAffine.Point,
      Q' ∈ Set.range (C.formalPointHomAdicCompletion u) ↔ Q' = 0 ∨ 1 < Valued.v Q'.xCoord :=
    fun Q' ↦ Set.ext_iff.mp (range_formalPointHomAdicCompletion u C) Q'
  -- A point with a pole transports into that range.
  have hmem : ∀ Q : (W⁄K).toAffine.Point, 1 < P.valuation Q.xCoord →
      Point.map ι Q ∈ Set.range (C.formalPointHomAdicCompletion u) := fun Q hQ ↦ by
    refine (hrange _).mpr (Or.inr ?_)
    rwa [Point.xCoord_map, hι, hval]
  -- The range of an additive homomorphism is closed under addition.
  have hsum : Point.map ι (Q₁ + Q₂) ∈ Set.range (C.formalPointHomAdicCompletion u) := by
    obtain ⟨a, ha⟩ := hmem Q₁ h₁
    obtain ⟨b, hb⟩ := hmem Q₂ h₂
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]; exact rfl⟩
  rcases (hrange _).mp hsum with h0 | hlt
  · exact absurd ((Point.map_injective ι) (h0.trans (map_zero _).symm)) h
  · rwa [Point.xCoord_map, hι, hval] at hlt

/-- **The points with a pole at `P`**, together with the point at infinity, as a subgroup of
`W(K)`. Classically this is the kernel `E₁(K_P)` of reduction at `P`. -/
def polePoints (P : TauCeti.Place F K) : AddSubgroup (W⁄K).toAffine.Point where
  carrier := {Q | Q = 0 ∨ 1 < P.valuation Q.xCoord}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro Q₁ Q₂ (rfl | h₁) (rfl | h₂)
    · exact Or.inl (zero_add 0)
    · rw [zero_add]; exact Or.inr h₂
    · rw [add_zero]; exact Or.inr h₁
    · rcases eq_or_ne (Q₁ + Q₂) 0 with h | h
      · exact Or.inl h
      · exact Or.inr (one_lt_valuation_xCoord_add W P h₁ h₂ h)
  neg_mem' := by
    rintro Q (rfl | h)
    · exact Or.inl neg_zero
    · exact Or.inr (by rwa [Point.xCoord_neg])

/-- A point lies in `polePoints` when it is the point at infinity or its `x`-coordinate has a pole
at `P`. -/
@[simp]
theorem mem_polePoints_iff (P : TauCeti.Place F K) (Q : (W⁄K).toAffine.Point) :
    Q ∈ polePoints W P ↔ Q = 0 ∨ 1 < P.valuation Q.xCoord :=
  Iff.rfl

end WeierstrassCurve.Affine

end
