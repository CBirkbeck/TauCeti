module
public import TauCeti.NumberTheory.NumberField.Frobenius.Tower
public import TauCeti.NumberTheory.NumberField.FixedField

/-! # probe: the surjectivity crux of the 8.2 fixed-field fibre count -/

@[expose] public section
open scoped NumberField Pointwise
open IntermediateField NumberField
namespace Probe
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **A degree-one fixed-field prime pulls its relative Frobenius back to the absolute one.**
If the prime below `Q` in `L ^ ⟨σ⟩` has residue degree one over `𝓞 K`, and the relative Frobenius
at `Q` over that field restricts to `σ`, then `σ` is an arithmetic Frobenius at `Q` over `𝓞 K`. -/
theorem isArithFrobAt_of_restrictScalars_eq (σ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q]
    {τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L}
    (hτ : IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q)
    (hf : (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1)
    (hres : AlgEquiv.restrictScalars K τ = σ) :
    IsArithFrobAt (𝓞 K) σ Q := by
  obtain ⟨φ, hφ⟩ := NumberField.exists_isArithFrobAt (K := K) Q hQ
  have : AlgEquiv.restrictScalars K τ = φ :=
    NumberField.restrictScalars_eq_of_inertiaDeg_eq_one hφ hτ hf
  rwa [← hres, this]

end Probe
