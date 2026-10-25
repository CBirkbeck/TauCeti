/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Continuity
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.ClosedIdeal
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Topological boundary examples for affinoid algebras

Automatic continuity applies to quotients by zero, by the unit ideal and by X². The last quotient
retains a nonzero square-zero element. A scalar copy equipped with twice its original norm has
the same topology, although the identity algebra equivalence does not preserve norms.

For the product of two fields, powers of one maximal ideal retain the other factor. Intersecting
powers of both maximal ideals gives zero. This explains why the separation input to automatic
continuity ranges over all maximal ideals.

The scaled norm uses Mathlib's `RingNorm.toNormedRing`, and the nonreduced quotient uses its
coefficient criterion `MvPowerSeries.X_pow_dvd_iff`.
-/

public section

namespace TauCeti.Examples.Affinoid

/-- A copy of a type, used below to double the norm of a normed commutative ring. -/
@[expose] def TwiceNorm (R : Type*) : Type _ := R

section Ring
variable (R : Type*) [CommRing R]

instance : CommRing (TwiceNorm R) := inferInstanceAs (CommRing R)
instance : Algebra R (TwiceNorm R) := inferInstanceAs (Algebra R R)

/-- The identity algebra equivalence from the copy with doubled norm to the original ring. -/
def twiceNormAlgEquiv : TwiceNorm R ≃ₐ[R] R := AlgEquiv.refl

instance [IsNoetherianRing R] : IsNoetherianRing (TwiceNorm R) :=
  inferInstanceAs (IsNoetherianRing R)

end Ring

section ScaledNorm
variable (R : Type*) [NormedCommRing R]

/-- Twice the original norm, bundled as a ring norm on the copied ring. -/
noncomputable def twiceRingNorm : RingNorm (TwiceNorm R) where
  toFun x := 2 * ‖twiceNormAlgEquiv R x‖
  map_zero' := by simp
  add_le' x y := by
    rw [map_add]
    nlinarith [norm_add_le (twiceNormAlgEquiv R x) (twiceNormAlgEquiv R y)]
  neg' x := by simp
  mul_le' x y := by
    rw [map_mul]
    nlinarith [norm_mul_le (twiceNormAlgEquiv R x) (twiceNormAlgEquiv R y),
      mul_nonneg (norm_nonneg (twiceNormAlgEquiv R x)) (norm_nonneg (twiceNormAlgEquiv R y))]
  eq_zero_of_map_eq_zero' x hx := by
    apply (twiceNormAlgEquiv R).injective
    simpa using hx

noncomputable instance : NormedCommRing (TwiceNorm R) where
  __ := (twiceRingNorm R).toNormedRing
  mul_comm := mul_comm

/-- The copied ring has twice the original norm. -/
theorem norm_twiceNorm (x : TwiceNorm R) : ‖x‖ = 2 * ‖twiceNormAlgEquiv R x‖ := (rfl)

instance [IsUltrametricDist R] : IsUltrametricDist (TwiceNorm R) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro x y
  simp only [norm_twiceNorm, map_add]
  rw [← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_add_le_max _ _) (by norm_num)

end ScaledNorm

section NormedField
variable (K : Type*) [NormedField K]

noncomputable instance : NormedAlgebra K (TwiceNorm K) where
  norm_smul_le r x := by
    rw [norm_twiceNorm, map_smul, norm_smul, norm_twiceNorm]
    ring_nf
    exact le_rfl

instance : FiniteDimensional K (TwiceNorm K) :=
  Module.Finite.equiv (twiceNormAlgEquiv K).symm.toLinearEquiv

end NormedField

section Affinoid
open _root_.MvPowerSeries TauCeti
variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

instance : CompleteSpace (TwiceNorm K) := FiniteDimensional.complete K (TwiceNorm K)

/-- Both directions of the identity between the original and doubled norms are continuous,
even though the copied unit has norm 2. Both continuity claims use affinoid automatic continuity. -/
theorem continuous_twiceNormAlgEquiv :
    ‖(1 : TwiceNorm K)‖ = 2 ∧ Continuous (twiceNormAlgEquiv K) ∧
      Continuous (twiceNormAlgEquiv K).symm := by
  have ha : TauCeti.IsAffinoidAlgebra K (TwiceNorm K) :=
    (TauCeti.isAffinoidAlgebra_self (K := K)).of_surjective
      (twiceNormAlgEquiv K).symm.toAlgHom (twiceNormAlgEquiv K).symm.surjective
  refine ⟨by simp [norm_twiceNorm], ?_, ?_⟩
  · exact (TauCeti.isAffinoidAlgebra_self (K := K)).continuous_algHom
      (twiceNormAlgEquiv K).toAlgHom
  · exact ha.continuous_algHom (twiceNormAlgEquiv K).symm.toAlgHom

local notation "T" => IsRestricted.subring (R := K) (fun _ : Unit => (1 : ℝ))

/-- Automatic continuity includes the injective quotient map modulo zero. -/
theorem continuous_quotient_zero : Continuous (Ideal.Quotient.mkₐ K (⊥ : Ideal T)) ∧
    Function.Injective (Ideal.Quotient.mkₐ K (⊥ : Ideal T)) := by
  have hT : IsAffinoidAlgebra K T := isAffinoidAlgebra_tate
  have := hT.isNoetherianRing
  refine ⟨?_, ?_⟩
  · exact TauCeti.IsAffinoidAlgebra.continuous_algHom (K := K)
      (A := T ⧸ (⊥ : Ideal T)) (B := T) (hT.quotient ⊥) (Ideal.Quotient.mkₐ K ⊥)
  · intro x y h
    simpa only [Ideal.mem_bot, sub_eq_zero] using Ideal.Quotient.eq.mp h

/-- Automatic continuity includes the zero-ring quotient by the unit ideal. -/
theorem continuous_quotient_one : Continuous (Ideal.Quotient.mkₐ K (Ideal.span {(1 : T)})) ∧
    Subsingleton (T ⧸ Ideal.span {(1 : T)}) := by
  have hT : IsAffinoidAlgebra K T := isAffinoidAlgebra_tate
  have := hT.isNoetherianRing
  refine ⟨?_, ?_⟩
  · exact TauCeti.IsAffinoidAlgebra.continuous_algHom (K := K)
      (A := T ⧸ Ideal.span {(1 : T)}) (B := T) (hT.quotient _) (Ideal.Quotient.mkₐ K _)
  · rw [Ideal.span_singleton_one]
    infer_instance

/-- The quotient map modulo X² is continuous and retains a nonzero square-zero element. -/
theorem continuous_quotient_X_sq :
    let x : T := ⟨X (), isRestricted_X _ ()⟩
    let q := Ideal.Quotient.mkₐ K (Ideal.span {x ^ 2})
    Continuous q ∧ q x ≠ 0 ∧ (q x) ^ 2 = 0 := by
  intro x q
  have hT : IsAffinoidAlgebra K T := isAffinoidAlgebra_tate
  have := hT.isNoetherianRing
  refine ⟨?_, ?_, ?_⟩
  · exact TauCeti.IsAffinoidAlgebra.continuous_algHom (K := K)
      (A := T ⧸ Ideal.span {x ^ 2}) (B := T) (hT.quotient _) q
  · intro h
    have hdiv := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hd : (X () : MvPowerSeries Unit K) ^ 2 ∣ X () :=
      map_dvd (IsRestricted.subring (R := K) (fun _ : Unit => (1 : ℝ))).subtype hdiv
    have hc := X_pow_dvd_iff.mp hd (Finsupp.single () 1) (by simp)
    simp at hc
  · rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

end Affinoid

section Product
variable (K : Type*) [Field K]

/-- Both coordinate kernels are maximal ideals of the product of two fields. -/
theorem isMaximal_coordinate_kernels :
    (RingHom.ker (RingHom.fst K K)).IsMaximal ∧
      (RingHom.ker (RingHom.snd K K)).IsMaximal :=
  ⟨RingHom.ker_isMaximal_of_surjective _ Prod.fst_surjective,
    RingHom.ker_isMaximal_of_surjective _ Prod.snd_surjective⟩

private lemma ker_fst_mul :
    RingHom.ker (RingHom.fst K K) * RingHom.ker (RingHom.fst K K) =
      RingHom.ker (RingHom.fst K K) := by
  apply le_antisymm Ideal.mul_le_left
  intro x hx
  have h : x.1 = 0 := hx
  have he : ((0, 1) : K × K) ∈ RingHom.ker (RingHom.fst K K) := rfl
  have hprod : x * (0, 1) = x := Prod.ext (by simp [h]) (by simp)
  simpa only [hprod] using Ideal.mul_mem_mul hx he

private lemma ker_fst_pow (n : ℕ) :
    RingHom.ker (RingHom.fst K K) ^ (n + 1) = RingHom.ker (RingHom.fst K K) := by
  induction n with
  | zero => simp
  | succ n hn => rw [pow_succ, hn, ker_fst_mul]

/-- Positive powers of the first coordinate kernel do not separate a product of fields. -/
theorem iInf_pow_ker_fst_ne_bot :
    (⨅ (n : ℕ) (_ : 0 < n), RingHom.ker (RingHom.fst K K) ^ n) ≠ ⊥ := by
  intro h
  have hmem : ((0, 1) : K × K) ∈
      ⨅ (n : ℕ) (_ : 0 < n), RingHom.ker (RingHom.fst K K) ^ n := by
    simp only [Ideal.mem_iInf]
    intro n hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [ker_fst_pow]
    rfl
  simp [h] at hmem

/-- Intersections of powers of both coordinate kernels separate a product of fields. -/
theorem iInf_pow_ker_fst_inf_iInf_pow_ker_snd :
    (⨅ (n : ℕ) (_ : 0 < n), RingHom.ker (RingHom.fst K K) ^ n) ⊓
      (⨅ (n : ℕ) (_ : 0 < n), RingHom.ker (RingHom.snd K K) ^ n) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hfst := Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hx.1 1) Nat.zero_lt_one
  have hsnd := Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hx.2 1) Nat.zero_lt_one
  simp only [pow_one] at hfst hsnd
  exact Prod.ext hfst hsnd

end Product

end TauCeti.Examples.Affinoid
