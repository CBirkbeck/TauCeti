module

public import TauCeti.NumberTheory.NumberField.Frobenius.FixedFieldInertia
public import TauCeti.NumberTheory.NumberField.Frobenius.Tower

/-! # 8.2 probe: relative Frobenius over the fixed field is the absolute one -/

public section

namespace TauCeti

open IntermediateField

open scoped NumberField Pointwise

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- at the fixed field of a Frobenius, the relative Frobenius restricts to the absolute one. -/
theorem probe_restrictScalars_fixedField (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ Q)
    {τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L}
    (hτ : IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q) :
    AlgEquiv.restrictScalars K τ = σ := by
  have : IsScalarTower K ↥(fixedField (Subgroup.zpowers σ)) L :=
    (fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  have : IsGalois ↥(fixedField (Subgroup.zpowers σ)) L :=
    IsGalois.tower_top_intermediateField _
  exact NumberField.restrictScalars_eq_of_inertiaDeg_eq_one hσ hτ
    (Ideal.inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt Q hQ hσ)

end TauCeti
