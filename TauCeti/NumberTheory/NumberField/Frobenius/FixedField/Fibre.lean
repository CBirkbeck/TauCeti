/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
public import TauCeti.NumberTheory.NumberField.Frobenius.Tower

/-!
# Contracting a Frobenius fibre to the fixed field

Fix `σ ∈ Gal(L/K)` and let `E = L ^ ⟨σ⟩`. Among the primes `Q` of `𝓞 L` above an unramified prime
of `𝓞 K`, those admitting `σ` as an arithmetic Frobenius are exactly the ones whose contraction to
`𝓞 E` has residue degree one over `𝓞 K` and carries a relative Frobenius restricting to `σ`; and
distinct such `Q` have distinct contractions.

Both halves are needed to count primes of `E` by counting primes of `L`. The forward direction
supplies the contraction, the converse recognises which primes of `E` arise, and injectivity makes
the two counts equal.

Injectivity holds well beyond that fibre: it needs only that `σ` fix the primes in question, so
neither unramifiedness, nor a base prime of `𝓞 K`, nor `L / K` Galois plays any part in it.

## Main results

* `Ideal.exists_isArithFrobAt_restrictScalars_eq`: a prime carrying `σ` has, over the fixed field,
  a relative Frobenius restricting to `σ`.
* `Ideal.isArithFrobAt_of_restrictScalars_eq`: conversely, at residue degree one such a relative
  Frobenius forces `σ` to be the absolute Frobenius.
* `AlgEquiv.under_fixedField_injOn`: contraction to the fixed field is injective on the primes fixed
  by `σ`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
* `TauCetiRoadmap/Chebotarev/README.md`, §8.2, which asks for exactly this reduction: the primes
  of `L` carrying `σ` are matched with the primes of `L ^ ⟨σ⟩` of residue degree one over `𝓞 K`.
-/

public section

open scoped NumberField Pointwise

open IntermediateField NumberField

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **A Frobenius fibre has a relative Frobenius over the fixed field.** If `σ` is an arithmetic
Frobenius at an unramified nonzero prime `Q`, then over `L ^ ⟨σ⟩` there is an arithmetic Frobenius
at `Q` whose restriction to `Gal(L/K)` is `σ` itself. -/
theorem exists_isArithFrobAt_restrictScalars_eq (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (σ : L ≃ₐ[K] L) (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    ∃ τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L,
      IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q
        ∧ AlgEquiv.restrictScalars K τ = σ := by
  obtain ⟨τ, hτ⟩ := NumberField.exists_isArithFrobAt
    (K := ↥(fixedField (Subgroup.zpowers σ))) Q hQ
  exact ⟨τ, hτ, NumberField.restrictScalars_eq_of_inertiaDeg_eq_one hσ hτ
    (inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt Q hQ hσ)⟩

/-- **Recognising the fibre from the fixed field.** If the prime below `Q` in `L ^ ⟨σ⟩` has residue
degree one over `𝓞 K` and a relative Frobenius there restricts to `σ`, then `σ` is an arithmetic
Frobenius at `Q` over `𝓞 K`.

This is the converse of `exists_isArithFrobAt_restrictScalars_eq`, and the residue-degree
hypothesis is what the forward direction produces. -/
theorem isArithFrobAt_of_restrictScalars_eq (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (σ : L ≃ₐ[K] L)
    {τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L}
    (hτ : IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q)
    (hf : (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1)
    (hres : AlgEquiv.restrictScalars K τ = σ) :
    IsArithFrobAt (𝓞 K) σ Q := by
  obtain ⟨φ, hφ⟩ := NumberField.exists_isArithFrobAt (K := K) Q hQ
  have hrestr : AlgEquiv.restrictScalars K τ = φ :=
    NumberField.restrictScalars_eq_of_inertiaDeg_eq_one hφ hτ hf
  rwa [← hres, hrestr]

end Ideal

namespace AlgEquiv

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Contraction to the fixed field is injective on the primes fixed by `σ`.** Distinct primes of
`𝓞 L` that `σ` fixes have distinct contractions to `𝓞 (L ^ ⟨σ⟩)`.

`σ` need not be a Frobenius, the primes need not be unramified nor lie over a common prime of
`𝓞 K`, and `L / K` need not be Galois. -/
theorem under_fixedField_injOn (σ : L ≃ₐ[K] L) :
    Set.InjOn (fun Q : Ideal (𝓞 L) ↦ Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ))))
      {Q : Ideal (𝓞 L) | ∃ _ : Q.IsPrime, σ • Q = Q} := by
  rintro Q₁ ⟨_, h₁⟩ Q₂ ⟨_, -⟩ hEq
  have : Q₂.LiesOver (Q₁.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))) := ⟨hEq⟩
  exact (Ideal.eq_of_smul_eq_of_liesOver_under_fixedField h₁ Q₂).symm

end AlgEquiv
