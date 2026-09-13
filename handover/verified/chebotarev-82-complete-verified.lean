module
public import TauCeti.NumberTheory.NumberField.Frobenius.FixedFieldInertia
public import TauCeti.GroupTheory.SpecificGroups.Cyclic.Index
/-! # Chebotarev 8.2(2) in the roadmap's words, against the reordered API -/
public section
open IntermediateField
open scoped NumberField Pointwise
namespace Ideal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

theorem probe_isLeast (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (σ : L ≃ₐ[K] L) {φ : L ≃ₐ[K] L}
    (hφ : IsArithFrobAt (𝓞 K) φ Q) :
    IsLeast {n : ℕ | 0 < n ∧ φ ^ n ∈ Subgroup.zpowers σ}
      ((Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K)) := by
  rw [inertiaDeg_under_fixedField_eq_relIndex Q hQ σ hφ]
  exact Subgroup.isLeast_pow_mem_relIndex_zpowers φ (Subgroup.zpowers σ)

end Ideal

-- RE-VERIFIED r838 against origin/main + #6241 @ 3b8d28d68f + #6250 @ 6c43bb71b6.
-- 3613 jobs, 4.1s, zero sorries. Still two lines after #6241's `naming` reorder (Q first) and its
-- `generality` restatement for arbitrary H. Supersedes the r832 version and its STALE note.
