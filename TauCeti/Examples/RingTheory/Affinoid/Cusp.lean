/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Iterate
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.KrullDimension
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient

/-!
# Noether normalization of the affinoid cusp

The native two-variable Tate quotient K⟨X,Y⟩/(Y²-X³) is finite over K⟨X⟩ through its
X-coordinate map, that map is injective, and the quotient has Krull dimension one.
Separating the Y coordinate identifies the quotient with the monic polynomial quotient
K⟨X⟩[Y]/(Y²-X³) by Weierstrass division. The constant coefficient has norm one, so this
example uses the weak coefficient bounds allowed for distinguished polynomials.

The final example records the obstruction for the zero algebra: no Tate algebra over a
field injects into it.
-/

public section

open Polynomial TauCeti.PowerSeries
namespace TauCeti.Examples.Affinoid
variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "T" => MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Unit => (1 : ℝ))
local notation "B" => MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Option Unit => (1 : ℝ))
local notation "S" => PowerSeries.IsRestricted.subring (R := T) 1

/-- The affinoid cusp K⟨X,Y⟩/(Y²-X³), with X indexed by `some ()` and Y by `none`. -/
abbrev Cusp := B ⧸ Ideal.span {
  (⟨MvPowerSeries.X none, MvPowerSeries.isRestricted_X _ _⟩ : B) ^ 2 -
    (⟨MvPowerSeries.X (some ()), MvPowerSeries.isRestricted_X _ _⟩ : B) ^ 3}

private noncomputable def x : T := ⟨MvPowerSeries.X (), MvPowerSeries.isRestricted_X _ _⟩
private noncomputable def flatX : B := ⟨MvPowerSeries.X (some ()), MvPowerSeries.isRestricted_X _ _⟩
private noncomputable def flatY : B := ⟨MvPowerSeries.X none, MvPowerSeries.isRestricted_X _ _⟩
private noncomputable def P : T[X] := X ^ 2 - C (x K ^ 3)
private noncomputable def Φ : B ≃+* S := TauCeti.Huber.restrictedOptionEquiv

omit [CompleteSpace K] in
private theorem monic : (P K).IsMonicOfDegree 2 := by
  apply (isMonicOfDegree_X_pow T 2).sub
  simp

omit [CompleteSpace K] in
private theorem distinguished : IsDistinguished 1 2 ((P K) : PowerSeries T) := by
  apply isDistinguished_of_isMonicOfDegree zero_lt_one (monic K)
  intro k hk
  interval_cases k
  · simp only [P, coeff_sub, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte,
      coeff_C_zero, zero_sub, norm_neg, pow_zero, mul_one, one_pow]
    have hx : ‖x K‖ = 1 := MvPowerSeries.norm_X ()
    rw [norm_pow, hx]
    norm_num
  · simp only [P, coeff_sub, coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte,
      coeff_C, one_ne_zero, zero_sub, neg_zero, norm_zero, zero_mul, one_pow, zero_le_one]

omit [CompleteSpace K] in
private theorem map_relation :
    Φ K (flatY K ^ 2 - flatX K ^ 3) = polynomialToRestricted 1 (P K) := by
  have hy : (Φ K (flatY K) : PowerSeries T) = PowerSeries.X :=
    TauCeti.Huber.coe_restrictedOptionEquiv_X_none (R := K) (σ := Unit)
  have hx : (Φ K (flatX K) : PowerSeries T) = PowerSeries.C (x K) :=
    TauCeti.Huber.coe_restrictedOptionEquiv_X_some (R := K) (σ := Unit) ()
  apply Subtype.ext
  rw [map_sub, map_pow, map_pow]
  simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow]
  rw [hy, hx, coe_polynomialToRestricted]
  simp only [P, Polynomial.coe_sub, Polynomial.coe_pow, coe_X, coe_C, map_pow]

private noncomputable def E :
    (B ⧸ Ideal.span {flatY K ^ 2 - flatX K ^ 3}) ≃+*
    (S ⧸ Ideal.span {polynomialToRestricted 1 (P K)}) :=
  Ideal.quotientEquiv _ _ (Φ K) (by
    simp only [Ideal.map_span, Set.image_singleton, RingEquiv.coe_toRingHom, map_relation])

private noncomputable def Q : AdjoinRoot (P K) ≃ₐ[T]
    (S ⧸ Ideal.span {polynomialToRestricted 1 (P K)}) :=
  (distinguished K).polynomialQuotientEquiv zero_lt_one (monic K)

private noncomputable def cuspMap : T →+* (B ⧸ Ideal.span {flatY K ^ 2 - flatX K ^ 3}) :=
  (E K).symm.toRingHom.comp (algebraMap T _)

omit [CompleteSpace K] in
private theorem cuspMap_C (a : K) : cuspMap K (algebraMap K T a) =
    algebraMap K (B ⧸ Ideal.span {flatY K ^ 2 - flatX K ^ 3}) a := by
  apply (E K).injective
  -- The ring-homomorphism composition retains a toRingHom projection that prevents
  -- rewriting by RingEquiv.apply_symm_apply until this defining application is unfolded.
  change (E K) ((E K).symm _) = _
  rw [RingEquiv.apply_symm_apply, ← Ideal.Quotient.mk_algebraMap,
    ← Ideal.Quotient.mk_algebraMap, E, Ideal.quotientEquiv_mk]
  exact congrArg (Ideal.Quotient.mk _) (TauCeti.Huber.restrictedOptionEquiv_algebraMap
    (R := K) (σ := Unit) (c := fun _ => 1) a).symm

/-- The finite map K⟨X⟩ → K⟨X,Y⟩/(Y²-X³) induced by the X coordinate. -/
noncomputable def cuspFiniteMap : T →ₐ[K] Cusp K where
  __ := cuspMap K
  commutes' := cuspMap_C K

omit [CompleteSpace K] in
/-- On any restricted series, the finite map is the quotient class of its inclusion as a
series independent of Y, expressed by the inverse of the restricted-series iteration map. -/
theorem cuspFiniteMap_apply (f : T) : cuspFiniteMap K f =
    Ideal.Quotient.mk _
      ((TauCeti.Huber.restrictedOptionEquiv (R := K) (σ := Unit)
        (c := fun _ => 1)).symm (algebraMap T S f)) := (rfl)

/-- The X-coordinate map into the affinoid cusp is injective. -/
theorem cuspFiniteMap_injective : Function.Injective (cuspFiniteMap K) := by
  apply (E K).symm.injective.comp
  have h : Function.Injective (algebraMap T (AdjoinRoot (P K))) :=
    AdjoinRoot.of.injective_of_monic_of_degree_pos (monic K).monic (by
      rw [← Polynomial.natDegree_pos_iff_degree_pos, (monic K).natDegree_eq]; norm_num)
  have he : algebraMap T (S ⧸ Ideal.span {polynomialToRestricted 1 (P K)}) =
      (Q K).toRingHom.comp (algebraMap T (AdjoinRoot (P K))) := by ext a; simp
  rw [he]
  exact (Q K).injective.comp h

/-- The affinoid cusp is finite over its X-coordinate Tate algebra. -/
theorem cuspFiniteMap_finite : (cuspFiniteMap K).Finite := by
  have : Module.Finite T (AdjoinRoot (P K)) := (monic K).monic.finite_adjoinRoot
  have : Module.Finite T (S ⧸ Ideal.span {polynomialToRestricted 1 (P K)}) :=
    Module.Finite.equiv (Q K).toLinearEquiv
  exact (RingHom.Finite.of_surjective _ (E K).symm.surjective).comp
    (by rw [RingHom.finite_algebraMap]; infer_instance)

omit [CompleteSpace K] in
/-- The finite map sends X to the class of the X coordinate in the native two-variable quotient. -/
@[simp]
theorem cuspFiniteMap_X : cuspFiniteMap K
    (⟨MvPowerSeries.X (), MvPowerSeries.isRestricted_X _ _⟩ : T) =
    Ideal.Quotient.mk _
      (⟨MvPowerSeries.X (some ()), MvPowerSeries.isRestricted_X _ _⟩ : B) := by
  rw [cuspFiniteMap_apply]
  apply congrArg (Ideal.Quotient.mk _)
  apply (Φ K).injective
  rw [Φ, RingEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (TauCeti.Huber.coe_restrictedOptionEquiv_X_some (R := K) (σ := Unit)
    (c := fun _ => 1) ()).symm

/-- The affinoid cusp has Krull dimension one. -/
theorem ringKrullDim_cusp : ringKrullDim (Cusp K) = 1 := by
  let A := Cusp K
  let := (cuspFiniteMap K).toRingHom.toAlgebra
  have : Module.Finite T A := cuspFiniteMap_finite K
  have : Algebra.IsIntegral T A := Algebra.IsIntegral.of_finite T A
  have : FaithfulSMul T A := (faithfulSMul_iff_algebraMap_injective T A).mpr
    (cuspFiniteMap_injective K)
  simpa only [Nat.card_unique, Nat.cast_one] using
    (TauCeti.MvPowerSeries.ringKrullDim_eq_natCard_of_isIntegral (K := K) (σ := Unit) (A := A))

omit [CompleteSpace K] in
example (n : ℕ) (f : MvPowerSeries.IsRestricted.subring (R := K)
    (fun _ : Fin n => (1 : ℝ)) →+* PUnit) : ¬Function.Injective f := by
  intro h
  exact zero_ne_one (h (Subsingleton.elim (f 0) (f 1)))

end TauCeti.Examples.Affinoid
