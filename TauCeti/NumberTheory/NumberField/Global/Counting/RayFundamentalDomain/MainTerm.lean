/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Counting.CongruenceLattice
public import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.Volume
public import TauCeti.NumberTheory.NumberField.Global.RayClass.ClassNumber
public import TauCeti.NumberTheory.NumberField.Global.RayClass.MainTerm

/-!
# The geometric coefficient of the ray ideal count

Counting the points of a coset of `congruenceLattice 𝔪 (mk0 𝔞)` in the norm-`≤ t` section of
`rayFundamentalDomain 𝔪` gives a main term `V / covol · t`, where `V` is the volume of the
norm-one section of the domain and `covol` the covolume of the lattice. This file evaluates the
coefficient that this produces for the ideals of a ray class, where `t = x · N 𝔞`: the norm of
`𝔞` cancels against the covolume, and the volume of the domain, the index of the congruence
units and the ray class number formula combine into the Dedekind-zeta residue.

Writing `w_𝔪` for the number of roots of unity congruent to one modulo `𝔪`, `h_𝔪` for the ray
class number and `𝔪₀` for the finite part of `𝔪`, the coefficient is
`V / covol · N 𝔞 = w_𝔪 · Res_{s=1} ζ_K / h_𝔪 · #(𝓞 K ⧸ 𝔪₀)ˣ / N 𝔪₀`.
For the trivial modulus the right-hand side is `w_K · Res_{s=1} ζ_K / h_K`.

## Main results

* `TauCeti.GlobalNumberFields.measureReal_div_covolume_congruenceLattice_mul_absNorm`: the
  coefficient in terms of the Dedekind-zeta residue.
-/

public section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone NumberField.Units
open scoped nonZeroDivisors Real

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **The geometric coefficient of the ray ideal count.**  The volume of the norm-one section of
`rayFundamentalDomain 𝔪`, over the covolume of the congruence lattice of a nonzero integral ideal
`𝔞`, times the norm of `𝔞`, is `w_𝔪 · Res_{s=1} ζ_K / h_𝔪 · #(𝓞 K ⧸ 𝔪₀)ˣ / N 𝔪₀`, where `w_𝔪`
is the number of roots of unity congruent to one modulo `𝔪`. -/
theorem measureReal_div_covolume_congruenceLattice_mul_absNorm (𝔪 : Modulus K)
    (𝔞 : (Ideal (𝓞 K))⁰) :
    volume.real (rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}) /
        ZLattice.covolume (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)) volume *
          Ideal.absNorm (𝔞 : Ideal (𝓞 K)) =
      Nat.card (unitsCongruenceTorsion 𝔪) * (dedekindZeta_residue K /
        Nat.card (RayClassGroup 𝔪) * (Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ /
          Ideal.absNorm 𝔪.finitePart)) := by
  have hV := congrArg ENNReal.toReal (two_pow_mul_volume_rayFundamentalDomain_inter_normLeOne 𝔪)
  rw [volume_normLeOne] at hV
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_natCast,
    ENNReal.coe_toReal, NNReal.coe_real_pi, ENNReal.toReal_ofReal (regulator_pos K).le,
    ← measureReal_def] at hV
  have hh := congrArg (Nat.cast : ℕ → ℝ) (card_rayClassGroup_mul_index 𝔪)
  have hi := congrArg (Nat.cast : ℕ → ℝ)
    (index_unitsCongruenceSubgroup_mul_card_unitsCongruenceTorsion 𝔪)
  push_cast at hh hi
  have h𝔞 : (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors 𝔞)
  have h𝔪 : (Ideal.absNorm 𝔪.finitePart : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_zero)
  have hd : √|(discr K : ℝ)| ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))
  have hw : (torsionOrder K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have hr : (Nat.card (RayClassGroup 𝔪) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [covolume_congruenceLattice, covolume_idealLattice, FractionalIdeal.coe_mk0,
    FractionalIdeal.coeIdeal_absNorm, dedekindZeta_residue_def, classNumber,
    ← Nat.card_eq_fintype_card]
  push_cast
  field_simp
  have h2 : (1 / 2 : ℝ) ^ nrComplexPlaces K * 2 ^ nrComplexPlaces K = 1 := by
    rw [← mul_pow]
    norm_num
  have hs : (2 : ℝ) ^ 𝔪.infinitePart.card * (unitsCongruenceSubgroup 𝔪).index ≠ 0 :=
    mul_ne_zero (by positivity) (Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero)
  refine mul_left_cancel₀ hs ?_
  -- `2 ^ s · V = N · vol(normLeOne)`, `h_𝔪 · [E : E_𝔪] = h · #(𝓞 K ⧸ 𝔪₀)ˣ · 2 ^ s` and
  -- `[E : E_𝔪] · w_𝔪 = N · w_K`
  set E : ℝ := ((unitsCongruenceSubgroup 𝔪).index : ℝ)
  set P : ℝ := 2 ^ nrRealPlaces K * π ^ nrComplexPlaces K * regulator K
  set w : ℝ := (Nat.card (unitsCongruenceTorsion 𝔪) : ℝ)
  set R : ℝ := (Nat.card (RayClassGroup 𝔪) : ℝ)
  linear_combination (torsionOrder K * R * E) * hV
    - (E * P * w * Nat.card (ClassGroup (𝓞 K)) * Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ *
      2 ^ 𝔪.infinitePart.card) * h2 + (E * P * w) * hh - (E * R * P) * hi

end TauCeti.GlobalNumberFields
