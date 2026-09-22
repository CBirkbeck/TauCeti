/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Finite
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# The main term of the ray class ideal count

The number of integral ideals of a fixed ray class with absolute norm at most `x` grows linearly
in `x`, with a coefficient that is the same for every class of the ray class group.  This file
defines that coefficient and proves it positive.

The coefficient is the Dedekind-zeta residue divided by the order of the ray class group, times
one Euler factor `1 - (N 𝔭)⁻¹` for each prime `𝔭` in the support of the modulus.  The count runs
over the ideals *prime to* the finite part of the modulus, and `1 - (N 𝔭)⁻¹` is the value at
`s = 1` of the Euler factor that dropping `𝔭` removes from the Dedekind zeta function.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm`: the coefficient.

## Main results

* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm_eq`: the coefficient written out.
* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm_pos`: it is positive.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VIII, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The coefficient common to every ray class: the Dedekind-zeta residue of `K`, divided by the
order of the ray class group of `𝔪`, times one Euler factor `1 - (N 𝔭)⁻¹` for each prime `𝔭` in
the support of `𝔪`. -/
noncomputable def rayClassIdealMainTerm (𝔪 : Modulus K) : ℝ :=
  dedekindZeta_residue K / (Nat.card (RayClassGroup 𝔪) : ℝ) *
    ∏ v ∈ 𝔪.support, (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)

/-- **The explicit main term.**  The Dedekind-zeta residue divided by the order of the ray class
group, times the Euler factors at the primes dividing the finite part of the modulus. -/
theorem rayClassIdealMainTerm_eq (𝔪 : Modulus K) :
    rayClassIdealMainTerm 𝔪 = dedekindZeta_residue K / (Nat.card (RayClassGroup 𝔪) : ℝ) *
      ∏ v ∈ 𝔪.support, (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) :=
  (rfl)

/-- **The main term is positive.** -/
theorem rayClassIdealMainTerm_pos (𝔪 : Modulus K) : 0 < rayClassIdealMainTerm 𝔪 := by
  rw [rayClassIdealMainTerm_eq]
  refine mul_pos (div_pos (dedekindZeta_residue_pos K) (mod_cast Nat.card_pos))
    (Finset.prod_pos fun v _ ↦ ?_)
  -- a height-one prime has absolute norm at least two, so its Euler factor is positive
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (mod_cast HeightOneSpectrum.one_lt_absNorm v))

end TauCeti.GlobalNumberFields
