/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
public import TauCeti.NumberTheory.NumberField.Frobenius.Tower

/-!
# Contracting a Frobenius fiber to the fixed field

Fix `σ ∈ Gal(L/K)` and let `E = L ^ ⟨σ⟩`. For a prime `Q` of `𝓞 L`, unramified over `𝓞 K`, this
file characterizes "`σ` is an arithmetic Frobenius at `Q`" in terms of the contraction of `Q` to
`𝓞 E`: it holds exactly when that contraction has residue degree one over `𝓞 K` and carries a
relative Frobenius restricting to `σ`.

The forward direction produces the relative Frobenius; the converse recovers `σ` from it. Together
they are the step a fixed-field count runs through, which also needs the injectivity of contraction
supplied by `Ideal.eq_of_smul_eq_of_liesOver_under_fixedField`.

## Main results

* `Ideal.exists_isArithFrobAt_restrictScalars_eq`: a prime carrying `σ` has, over the fixed field,
  a relative Frobenius restricting to `σ`.
* `Ideal.isArithFrobAt_of_restrictScalars_eq`: conversely, at residue degree one such a relative
  Frobenius forces `σ` to be the absolute Frobenius.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
* `TauCetiRoadmap/Chebotarev/README.md`, §8.2.
-/

public section

open scoped NumberField Pointwise

open IntermediateField NumberField

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **A Frobenius fiber has a relative Frobenius over the fixed field.** If `σ` is an arithmetic
Frobenius at an unramified prime `Q`, then over `L ^ ⟨σ⟩` there is an arithmetic Frobenius at `Q`
whose restriction to `Gal(L/K)` is `σ` itself. -/
theorem exists_isArithFrobAt_restrictScalars_eq (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (σ : L ≃ₐ[K] L) (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    ∃ τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L,
      IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q
        ∧ AlgEquiv.restrictScalars K τ = σ := by
  obtain ⟨τ, hτ⟩ := NumberField.exists_isArithFrobAt
    (K := ↥(fixedField (Subgroup.zpowers σ))) Q hσ.ne_bot
  exact ⟨τ, hτ, NumberField.restrictScalars_eq_of_inertiaDeg_eq_one hσ hτ
    (inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt Q hσ.ne_bot hσ)⟩

/-- **Recognising the fiber from the fixed field.** If the prime below `Q` in `L ^ ⟨σ⟩` has residue
degree one over `𝓞 K` and a relative Frobenius there restricts to `σ`, then `σ` is an arithmetic
Frobenius at `Q` over `𝓞 K`.

This is the converse of `exists_isArithFrobAt_restrictScalars_eq`, and the residue-degree
hypothesis is what the forward direction produces. -/
theorem isArithFrobAt_of_restrictScalars_eq (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (σ : L ≃ₐ[K] L)
    {τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L}
    (hτ : IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q)
    (hf : (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1)
    (hres : AlgEquiv.restrictScalars K τ = σ) :
    IsArithFrobAt (𝓞 K) σ Q :=
  hres ▸ NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one hτ hf

end Ideal
