/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Sum
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.DivisorPullback
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
-- Proof-only: the places over a point along `[n]`, affine and at infinity.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.PointPlace
-- Proof-only: the place at infinity restricts to itself.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
-- Proof-only: `[n]` is separable, hence unramified, when `n` is invertible.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
-- Proof-only: `#E[n] = n ²` and `[n]` onto `E[n]`, over a separably closed field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed

/-!
# The pullback of a point along `[n]`

Let `W` be an elliptic curve over a field `F` and `n` an integer invertible in `F`. Pulling the
divisor `(T)` of a point back along multiplication by `n` gives the points `R` with `n • R = T`,
each with multiplicity one. Among the places of points, the places over the place of `T` are the
places of the `[n]`-preimages of `T` (`TauCeti.Isogeny.isEquiv_comap_pointPlace_iff` and
`TauCeti.Isogeny.isEquiv_comap_pointPlace_infinityPlace_iff`), and `[n]` is unramified because it
is separable. Over a separably closed field `[n]` splits every place completely, so a place over a
point place has degree one and is itself a point place, and the pullback is the sum over the
fibre.

At an `n`-torsion point `T` the fibre over `T` is a translate of the fibre `E[n]` over `O`, and
`#E[n] = n ²`, so the sum of `[n]^* (T) - [n]^* (O)` is `n • T = O` and the divisor is principal.
This is the second input to the divisor construction of the Weil pairing (Silverman III.8.1),
after `WeierstrassCurve.Affine.exists_principal_zsmul_pointPlace_sub_infinity`: the pairing is
built from a function with this divisor.

## Main results

* `TauCeti.Isogeny.isEquiv_comap_valuation_pointEquivDegreeOnePlace_iff`: the place of `R`
  restricts along `[n]` to the place of `T` exactly when `n • R = T`, for every pair of points.
* `TauCeti.Isogeny.coeff_divisorPullback_mulByIntIsogeny`: the coefficient of `[n]^* D` at the
  place of `R` is the coefficient of `D` at the place of `n • R`.
* `TauCeti.Isogeny.finite_setOf_zsmul_eq`: the fibre `{R | n • R = T}` is finite.
* `TauCeti.Isogeny.restrict_eq_pointEquivDegreeOnePlace_iff`: over a separably closed field, the
  places over the place of `T` are exactly the places of its `[n]`-preimages.
* `TauCeti.Isogeny.divisorPullback_mulByIntIsogeny_ofPoint`: over a separably closed field,
  `[n]^* (T) = ∑_{n • R = T} (R)`.
* `TauCeti.Isogeny.exists_principal_eq_divisorPullback_mulByIntIsogeny_sub`: at an `n`-torsion
  point `T`, `[n]^* (T) - [n]^* (O)` is the divisor of a function.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10, III.8.1.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain

namespace TauCeti.Isogeny

open AlgebraicGeometry

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- The coordinate ring of an elliptic curve is a Dedekind domain. -/
local instance : IsDedekindDomain W.toAffine.CoordinateRing :=
  have := WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing W.toAffine
  W.toAffine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- **The places over the place of `T` along `[n]` are the places of the `[n]`-preimages of
`T`**, among the places of points. -/
theorem isEquiv_comap_valuation_pointEquivDegreeOnePlace_iff {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (R T : W.toAffine.Point) :
    (((pointEquivDegreeOnePlace W.toAffine R).1.valuation).comap
        (mulByIntIsogeny W hn).fieldPullback.toRingHom).IsEquiv
      (pointEquivDegreeOnePlace W.toAffine T).1.valuation ↔ n • R = T := by
  have hinf : ((infinityPlace W.toAffine).comap
      (mulByIntIsogeny W hn).fieldPullback.toRingHom).IsEquiv (infinityPlace W.toAffine) :=
    isEquiv_comap_infinityPlace _
  rcases R with _ | ⟨xR, yR, hR⟩ <;> rcases T with _ | ⟨xT, yT, hT⟩
  · rw [coe_pointEquivDegreeOnePlace_zero, Place.valuation_infinity, ← Affine.Point.zero_def,
      smul_zero]
    exact iff_of_true hinf rfl
  · rw [coe_pointEquivDegreeOnePlace_zero, Place.valuation_infinity,
      coe_pointEquivDegreeOnePlace_some, Place.valuation_ofPrime, ← Affine.Point.zero_def,
      smul_zero]
    exact iff_of_false
      (fun hE ↦ Place.not_isEquiv_infinityPlace_valuation (CoordinateRing.pointPlace hT.left)
        (hinf.symm.trans hE))
      (Affine.Point.some_ne_zero hT).symm
  · rw [coe_pointEquivDegreeOnePlace_some, Place.valuation_ofPrime,
      coe_pointEquivDegreeOnePlace_zero, Place.valuation_infinity, ← Affine.Point.zero_def]
    exact isEquiv_comap_pointPlace_infinityPlace_iff W hR hn
  · rw [coe_pointEquivDegreeOnePlace_some, coe_pointEquivDegreeOnePlace_some,
      Place.valuation_ofPrime, Place.valuation_ofPrime]
    exact isEquiv_comap_pointPlace_iff W hR hn hT

/-- **The coefficient of `[n]^* D` at the place of `R` is the coefficient of `D` at the place of
`n • R`**, for `n` invertible in `F`: the place of `R` lies over that of `n • R`, and `[n]` is
unramified, being separable. -/
theorem coeff_divisorPullback_mulByIntIsogeny {n : ℤ} (hchar : (n : F) ≠ 0)
    (D : Divisor F W.toAffine.FunctionField) (R : W.toAffine.Point) :
    letI := (mulByIntIsogeny W
      (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
    ((mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).divisorPullback (fun _ ↦ rfl) D).coeff
        (pointEquivDegreeOnePlace W.toAffine R).1 =
      D.coeff (pointEquivDegreeOnePlace W.toAffine (n • R)).1 := by
  let _ := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
  have := isScalarTower_of_algebraMap_eq_fieldPullback
    (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)) (fun _ ↦ rfl)
  have := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).finiteDimensional_functionField
    (fun _ ↦ rfl)
  have := (isSeparable_mulByIntIsogeny_iff W (psiFunctionField_ne_zero W hchar)).2 hchar
  rw [coeff_divisorPullback, ramificationIdx_eq_one _ (fun _ ↦ rfl), Nat.cast_one, one_mul,
    (Place.restrict_eq_iff_isEquiv_comap F W.toAffine.FunctionField _ _).mpr
      ((isEquiv_comap_valuation_pointEquivDegreeOnePlace_iff W _ R (n • R)).mpr rfl)]

omit [DecidableEq F] in
private theorem place_injective :
    Function.Injective fun R : W.toAffine.Point ↦ (pointEquivDegreeOnePlace W.toAffine R).1 :=
  Subtype.val_injective.comp (pointEquivDegreeOnePlace W.toAffine).injective

/-- **The `[n]`-fibre over a point is finite**: the places of its points lie over the place of
`T`, and a place has finitely many places above it in the finite extension `[n]`. -/
theorem finite_setOf_zsmul_eq {n : ℤ} (hn : psiFunctionField W n ≠ 0) (T : W.toAffine.Point) :
    {R : W.toAffine.Point | n • R = T}.Finite := by
  let _ := (mulByIntIsogeny W hn).fieldPullback.toRingHom.toAlgebra
  have := isScalarTower_of_algebraMap_eq_fieldPullback (mulByIntIsogeny W hn) fun _ ↦ rfl
  have := (mulByIntIsogeny W hn).finiteDimensional_functionField fun _ ↦ rfl
  exact ((Place.finite_setOf_restrict_eq (k' := F) (F' := W.toAffine.FunctionField) F
    W.toAffine.FunctionField (pointEquivDegreeOnePlace W.toAffine T).1).preimage
      (place_injective W).injOn).subset fun R hR ↦
    (Place.restrict_eq_iff_isEquiv_comap F _ _ _).mpr
      ((isEquiv_comap_valuation_pointEquivDegreeOnePlace_iff W hn R T).mpr hR)

section SepClosed

variable [IsSepClosed F]

/-- **The places over the place of `T` along `[n]` are the places of its `[n]`-preimages**, over
a separably closed field in which `n` is invertible: a place above a point place has degree one,
since `[n]` splits every place completely. -/
theorem restrict_eq_pointEquivDegreeOnePlace_iff {n : ℤ} (hchar : (n : F) ≠ 0)
    (T : W.toAffine.Point) (P : Place F W.toAffine.FunctionField) :
    letI := (mulByIntIsogeny W
      (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
    haveI := isScalarTower_of_algebraMap_eq_fieldPullback
      (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)) (fun _ ↦ rfl)
    haveI := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).finiteDimensional_functionField
      (fun _ ↦ rfl)
    P.restrict F W.toAffine.FunctionField = (pointEquivDegreeOnePlace W.toAffine T).1 ↔
      ∃ R, n • R = T ∧ (pointEquivDegreeOnePlace W.toAffine R).1 = P := by
  let _ := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
  have := isScalarTower_of_algebraMap_eq_fieldPullback
    (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)) (fun _ ↦ rfl)
  have := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).finiteDimensional_functionField
    (fun _ ↦ rfl)
  have := (isSeparable_mulByIntIsogeny_iff W (psiFunctionField_ne_zero W hchar)).2 hchar
  have hover (R : W.toAffine.Point) :
      (pointEquivDegreeOnePlace W.toAffine R).1.restrict F W.toAffine.FunctionField =
        (pointEquivDegreeOnePlace W.toAffine T).1 ↔ n • R = T :=
    (Place.restrict_eq_iff_isEquiv_comap F _ _ _).trans
      (isEquiv_comap_valuation_pointEquivDegreeOnePlace_iff W _ R T)
  refine ⟨fun hP ↦ ?_, fun ⟨R, hR, hRP⟩ ↦ by rw [← hRP]; exact (hover R).mpr hR⟩
  -- a place over a place of degree one has degree one, the relative degree being one
  have hdeg : P.degree = 1 := by
    rw [Place.degree_eq_degree_restrict_mul_relativeDegree F W.toAffine.FunctionField P, hP,
      (pointEquivDegreeOnePlace W.toAffine T).2, one_mul]
    exact (isSplitCompletely _ (fun _ ↦ rfl) _).relativeDegree_eq_one hP
  obtain ⟨R, hR⟩ : ∃ R, (pointEquivDegreeOnePlace W.toAffine R).1 = P :=
    ⟨(pointEquivDegreeOnePlace W.toAffine).symm ⟨P, hdeg⟩, by simp⟩
  exact ⟨R, (hover R).mp (by rw [hR]; exact hP), hR⟩

/-- **The pullback of a point along `[n]` is its fibre**: over a separably closed field in which
`n` is invertible, `[n]^* (T) = ∑_{n • R = T} (R)`. -/
theorem divisorPullback_mulByIntIsogeny_ofPoint {n : ℤ} (hchar : (n : F) ≠ 0)
    (T : W.toAffine.Point) :
    letI := (mulByIntIsogeny W
      (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
    (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).divisorPullback (fun _ ↦ rfl)
        (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine T).1) =
      ∑ R ∈ (finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) T).toFinset,
        WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine R).1 := by
  classical
  let _ := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
  have := isScalarTower_of_algebraMap_eq_fieldPullback
    (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)) (fun _ ↦ rfl)
  have := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).finiteDimensional_functionField
    (fun _ ↦ rfl)
  have := (isSeparable_mulByIntIsogeny_iff W (psiFunctionField_ne_zero W hchar)).2 hchar
  rw [show ∑ R ∈ (finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) T).toFinset,
        WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine R).1 =
      WeilDivisor.ofFinset ((finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar)
        T).toFinset.map ⟨_, place_injective W⟩) by
    rw [WeilDivisor.ofFinset_eq_sum, Finset.sum_map]; rfl]
  ext P
  rw [coeff_divisorPullback, ramificationIdx_eq_one _ (fun _ ↦ rfl), Nat.cast_one, one_mul,
    WeilDivisor.coeff_ofFinset]
  -- the pullback has coefficient `1` at the places over the place of `T`, and `0` elsewhere
  have hfin := finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) T
  split_ifs with hmem
  · obtain ⟨R, hR, hRP⟩ := Finset.mem_map.mp hmem
    rw [(restrict_eq_pointEquivDegreeOnePlace_iff W hchar T P).mpr
      ⟨R, (Set.Finite.mem_toFinset hfin).mp hR, hRP⟩, WeilDivisor.coeff_ofPoint_self]
  · refine WeilDivisor.coeff_ofPoint_of_ne fun hP ↦ hmem ?_
    obtain ⟨R, hR, rfl⟩ := (restrict_eq_pointEquivDegreeOnePlace_iff W hchar T P).mp hP
    exact Finset.mem_map_of_mem _
      ((Set.Finite.mem_toFinset hfin).mpr (show R ∈ {R | n • R = T} from hR))

/-! ### The divisor `[n]^* (T) - [n]^* (O)` -/

/-- The points of `W` are those of its base change to `F`, where the torsion counts live. -/
private noncomputable def pointEquivBaseChangeSelf :
    W.toAffine.Point ≃+ (W.toAffine⁄F).toAffine.Point :=
  AddEquiv.cast (M := fun W' : Affine F ↦ W'.Point) W.toAffine.baseChange_self.symm

private theorem exists_zsmul_eq {n : ℤ} (hchar : (n : F) ≠ 0) {T : W.toAffine.Point}
    (hT : n • T = 0) : ∃ R : W.toAffine.Point, n • R = T := by
  obtain ⟨P, hP, -⟩ := W.toAffine.exists_zsmul_eq_of_zsmul_eq_zero hchar
    (T := pointEquivBaseChangeSelf W T) (by rw [← map_zsmul, hT, map_zero])
  exact ⟨(pointEquivBaseChangeSelf W).symm P, by rw [← map_zsmul, hP, AddEquiv.symm_apply_apply]⟩

private theorem natCard_setOf_zsmul_eq_zero {n : ℤ} (hchar : (n : F) ≠ 0) :
    Nat.card {R : W.toAffine.Point | n • R = 0} = n.natAbs ^ 2 := by
  rw [← W.toAffine.natCard_torsionBy hchar]
  refine Nat.card_congr ((pointEquivBaseChangeSelf W).toEquiv.subtypeEquiv fun R ↦ ?_)
  simp only [Set.mem_ofPred_eq, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  refine ⟨fun h ↦ (Submodule.mem_torsionBy_iff _ _).mpr ?_, fun h ↦ ?_⟩
  · rw [← map_zsmul, h, map_zero]
  · have := (Submodule.mem_torsionBy_iff _ _).mp h
    rwa [← map_zsmul, AddEquiv.map_eq_zero_iff] at this

/-- **`[n]^* (T) - [n]^* (O)` is principal** at an `n`-torsion point `T`, over a separably closed
field in which `n` is invertible (Silverman III.8.1).

With `n • R₀ = T`, the fibre over `T` is the translate by `R₀` of the fibre over `O`, so the
divisor is `∑_{n • S = O} ((R₀ + S) - (S))`. Its sum is `#E[n] • R₀ = n • (n • R₀) = O`. -/
theorem exists_principal_eq_divisorPullback_mulByIntIsogeny_sub {n : ℤ}
    (hchar : (n : F) ≠ 0) {T : W.toAffine.Point} (hT : n • T = 0) :
    letI := (mulByIntIsogeny W
      (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
    ∃ z : W.toAffine.FunctionFieldˣ, Divisor.principal W.toAffine.isFunctionField z =
      (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).divisorPullback (fun _ ↦ rfl)
          (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine T).1) -
        (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).divisorPullback (fun _ ↦ rfl)
          (WeilDivisor.ofPoint (Place.infinity W.toAffine)) := by
  let _ := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
  obtain ⟨R₀, hR₀⟩ := exists_zsmul_eq W hchar hT
  rw [← coe_pointEquivDegreeOnePlace_zero, divisorPullback_mulByIntIsogeny_ofPoint W hchar T,
    divisorPullback_mulByIntIsogeny_ofPoint W hchar .zero]
  set s₀ := (finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) 0).toFinset with hs₀
  -- the fibre over `T` is the translate by `R₀` of the fibre over `O`
  have hfib : (finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) T).toFinset =
      s₀.map ⟨(R₀ + ·), add_right_injective R₀⟩ := by
    ext R
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_map,
      Function.Embedding.coeFn_mk, hs₀]
    refine ⟨fun hR ↦ ⟨R - R₀, by rw [smul_sub, hR, hR₀, sub_self], add_sub_cancel _ _⟩, ?_⟩
    rintro ⟨S, hS, rfl⟩
    rw [smul_add, hR₀, hS, add_zero]
  rw [hfib, Finset.sum_map, ← Finset.sum_sub_distrib]
  let D : (Divisor.degree (k := F) (F := W.toAffine.FunctionField)).ker :=
    ∑ S ∈ s₀, ⟨_, W.toAffine.ofPoint_sub_ofPoint_mem_ker_degree (R₀ + S) S⟩
  have hσ : W.toAffine.divisorSum D = 0 := by
    simp only [D, map_sum, divisorSum_ofPoint_sub_ofPoint, add_sub_cancel_right,
      Finset.sum_const]
    rw [hs₀, ← Nat.card_eq_card_finite_toFinset, natCard_setOf_zsmul_eq_zero W hchar,
      ← natCast_zsmul, Nat.cast_pow, Int.natAbs_sq, sq, mul_smul, hR₀, hT]
  obtain ⟨z, hz⟩ := W.toAffine.divisorSum_eq_zero_iff.mp hσ
  exact ⟨z, hz.trans (by simp [D])⟩

end SepClosed

end TauCeti.Isogeny

end
