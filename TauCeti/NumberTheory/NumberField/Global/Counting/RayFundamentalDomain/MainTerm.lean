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
import TauCeti.RingTheory.DedekindDomain.Totient

/-!
# The geometric coefficient of the ray ideal count

Counting the points of a coset of `congruenceLattice 𝔪 (mk0 𝔞)` in the norm-`≤ t` section of
`rayFundamentalDomain 𝔪` gives a main term `V / covol · t`, where `V` is the volume of the
norm-one section of the domain and `covol` the covolume of the lattice. This file evaluates the
coefficient that this produces for the ideals of a ray class, where `t = x · N 𝔞`: the norm of
`𝔞` cancels against the covolume, and the volume of the domain, the index of the congruence
units and the ray class number formula combine into the Dedekind-zeta residue, and the
proportion `#(𝓞 K ⧸ 𝔪₀)ˣ / N 𝔪₀` of residues prime to the finite part `𝔪₀` of `𝔪` becomes the
product of the local factors `1 - (N 𝔭)⁻¹`.

Writing `w_𝔪` for the number of roots of unity congruent to one modulo `𝔪`, the coefficient is
`V / covol · N 𝔞 = w_𝔪 · rayClassIdealMainTerm 𝔪`.

## Main results

* `TauCeti.GlobalNumberFields.measureReal_div_covolume_congruenceLattice_mul_absNorm`: the
  coefficient is `w_𝔪` times `rayClassIdealMainTerm 𝔪`.
-/

public section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone NumberField.Units
open scoped nonZeroDivisors Real

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
private theorem measureReal_rayFundamentalDomain_inter_normLeOne (𝔪 : Modulus K) :
    volume.real (rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}) =
      (unitsCongruenceSubgroupSupTorsion 𝔪).index *
        (2 ^ nrRealPlaces K * π ^ nrComplexPlaces K * regulator K) / 2 ^ 𝔪.infinitePart.card := by
  rw [eq_div_iff (by positivity), mul_comm, measureReal_def]
  simpa [volume_normLeOne, (regulator_pos K).le] using
    congrArg ENNReal.toReal (two_pow_mul_volume_rayFundamentalDomain_inter_normLeOne 𝔪)

open scoped Classical in
private theorem covolume_congruenceLattice_mk0_div_absNorm (𝔪 : Modulus K) (𝔞 : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)) volume /
        Ideal.absNorm (𝔞 : Ideal (𝓞 K)) =
      Ideal.absNorm 𝔪.finitePart * √|(discr K : ℝ)| / 2 ^ nrComplexPlaces K := by
  have h𝔞 : (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors 𝔞)
  rw [covolume_congruenceLattice, covolume_idealLattice, FractionalIdeal.coe_mk0,
    FractionalIdeal.coeIdeal_absNorm, inv_pow]
  push_cast
  field_simp

private theorem card_unitsCongruenceTorsion_mul_rayClassIdealMainTerm (𝔪 : Modulus K) :
    Nat.card (unitsCongruenceTorsion 𝔪) * rayClassIdealMainTerm 𝔪 =
      (unitsCongruenceSubgroupSupTorsion 𝔪).index *
          (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
        (2 ^ 𝔪.infinitePart.card * Ideal.absNorm 𝔪.finitePart * √|(discr K : ℝ)|) := by
  have hh := congrArg (Nat.cast : ℕ → ℝ) (card_rayClassGroup_mul_index 𝔪)
  have hi := congrArg (Nat.cast : ℕ → ℝ)
    (index_unitsCongruenceSubgroup_mul_card_unitsCongruenceTorsion 𝔪)
  push_cast at hh hi
  have h𝔪 : (Ideal.absNorm 𝔪.finitePart : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_zero)
  have hd : √|(discr K : ℝ)| ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))
  have hw : (torsionOrder K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have hr : (Nat.card (RayClassGroup 𝔪) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have := Ring.HasFiniteQuotients.finiteQuotient 𝔪.finitePart_ne_bot
  -- the correction product is the proportion of residues modulo `𝔪₀` that are units
  rw [rayClassIdealMainTerm_eq, ← mul_div_cancel_left₀ (∏ v ∈ 𝔪.support, _) h𝔪,
    ← Ideal.card_units_quotient_eq_absNorm_mul_prod 𝔪.finitePart 𝔪.mem_support_iff,
    dedekindZeta_residue_def, classNumber, ← Nat.card_eq_fintype_card]
  field_simp
  -- `h_𝔪 · [E : E_𝔪] = h · #(𝓞 K ⧸ 𝔪₀)ˣ · 2 ^ s` and `[E : E_𝔪] · w_𝔪 = [E : E_𝔪 μ_K] · w_K`
  linear_combination regulator K *
    ((Nat.card (RayClassGroup 𝔪) : ℝ) * hi - (Nat.card (unitsCongruenceTorsion 𝔪) : ℝ) * hh)

open scoped Classical in
/-- **The geometric coefficient of the ray ideal count.**  The volume of the norm-one section of
`rayFundamentalDomain 𝔪`, over the covolume of the congruence lattice of a nonzero integral ideal
`𝔞`, times the norm of `𝔞`, is `w_𝔪 · rayClassIdealMainTerm 𝔪`, where `w_𝔪` is the number of
roots of unity congruent to one modulo `𝔪`. -/
theorem measureReal_div_covolume_congruenceLattice_mul_absNorm (𝔪 : Modulus K)
    (𝔞 : (Ideal (𝓞 K))⁰) :
    volume.real (rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}) /
        ZLattice.covolume (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)) volume *
          Ideal.absNorm (𝔞 : Ideal (𝓞 K)) =
      Nat.card (unitsCongruenceTorsion 𝔪) * rayClassIdealMainTerm 𝔪 := by
  rw [div_mul_eq_mul_div, ← div_div_eq_mul_div, covolume_congruenceLattice_mk0_div_absNorm,
    measureReal_rayFundamentalDomain_inter_normLeOne,
    card_unitsCongruenceTorsion_mul_rayClassIdealMainTerm]
  field_simp
  ring

end TauCeti.GlobalNumberFields
