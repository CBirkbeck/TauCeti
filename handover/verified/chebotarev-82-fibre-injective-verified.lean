module
public import TauCeti.NumberTheory.NumberField.Frobenius.FiberCount
public import TauCeti.NumberTheory.NumberField.FixedField

/-! # probe: the L-side Frobenius fibre injects into the primes of the fixed field -/

@[expose] public section
open scoped NumberField Pointwise
open IntermediateField NumberField
namespace Probe
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

omit [IsGalois K L] in
/-- Contraction to the fixed field is injective on the primes carrying `σ` as a Frobenius. -/
theorem under_injOn (𝔭 : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    Set.InjOn (fun Q : Ideal (𝓞 L) ↦ Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ))))
      {Q : Ideal (𝓞 L) | ∃ (_ : Q.IsPrime) (_ : Q.LiesOver 𝔭) (_ : Q ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ Q} := by
  rintro Q₁ ⟨_, _, -, h₁⟩ Q₂ ⟨_, _, -, h₂⟩ hEq
  have hstab : σ • Q₁ = Q₁ := h₁.mem_stabilizer
  have : Q₂.LiesOver (Q₁.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))) := ⟨hEq⟩
  exact (Ideal.eq_of_smul_eq_of_liesOver_under_fixedField hstab Q₂).symm

end Probe
