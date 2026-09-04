/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# The fixed field of a cyclic subgroup meeting the cyclotomic fixers trivially

If `M / L` is an `m`-th cyclotomic extension and `g` generates a cyclic subgroup of `Gal(M/K)`
meeting `Gal(M/K(μ_m))` trivially, then `M` is an `m`-th cyclotomic extension of the fixed field
`M ^ ⟨g⟩` as well.

## Main results

* `IsCyclotomicExtension.fixedField_of_zpowers_inf_fixingSubgroup_eq_bot`
-/

public section

open IntermediateField

namespace IsCyclotomicExtension

/-- **The fixed field of `⟨g⟩` carries the cyclotomic extension**, whenever `⟨g⟩` meets the
fixers of `K(μ_m)` trivially. -/
theorem fixedField_of_zpowers_inf_fixingSubgroup_eq_bot {K M : Type*} [Field K] [Field M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M] {L : Type*} [Field L] [Algebra K L]
    [Algebra L M] [IsScalarTower K L M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (g : M ≃ₐ[K] M)
    (hmeet : Subgroup.zpowers g ⊓ (adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥) :
    IsCyclotomicExtension {m} (fixedField (Subgroup.zpowers g)) M := by
  set F : IntermediateField K M := fixedField (Subgroup.zpowers g)
  set Kμ : IntermediateField K M := adjoin K {b : M | b ^ m = 1}
  obtain ⟨ζ, hζ⟩ : ∃ r : M, IsPrimitiveRoot r m :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M (Set.mem_singleton m) (NeZero.ne m)
  -- `K(ζ) = K(μ_m)`, so the hypothesis is about the fixers of `K(ζ)`
  have hadjζ : adjoin K {ζ} = Kμ :=
    le_antisymm
      (adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (subset_adjoin K _ hζ.pow_eq_one)))
      (adjoin_le_iff.mpr fun x hx ↦ by
        obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one (Set.mem_ofPred_eq ▸ hx)
        exact pow_mem (subset_adjoin K _ (Set.mem_singleton ζ)) i)
  -- trivial meet of the fixers is `F ⊔ K(ζ) = ⊤`
  have hsup : (F ⊔ Kμ).fixingSubgroup = ⊥ := by
    rw [fixingSubgroup_sup, fixingSubgroup_fixedField, hmeet]
  have htop : F ⊔ Kμ = ⊤ := by
    have := congrArg fixedField hsup
    rwa [IsGalois.fixedField_fixingSubgroup, fixedField_bot] at this
  -- hence `ζ` generates `M` over `F`
  have htopF : adjoin F {ζ} = ⊤ := by
    apply restrictScalars_injective K
    rw [restrictScalars_adjoin_eq_sup, hadjζ, htop]
    rfl
  have : Algebra.IsIntegral F M := Algebra.IsIntegral.of_finite F M
  have hcyc : IsCyclotomicExtension {m} F (adjoin F {ζ}) :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := F) hζ
  rw [htopF] at hcyc
  exact IsCyclotomicExtension.equiv (S := {m}) (A := F) (f := topEquiv)

end IsCyclotomicExtension
