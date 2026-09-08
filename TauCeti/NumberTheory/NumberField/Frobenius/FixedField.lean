/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.FixedField
public import TauCeti.NumberTheory.NumberField.Frobenius.Tower

/-!
# The Frobenius over the fixed field of a single automorphism

`TauCeti.NumberField.exists_isArithFrobAt_pow_inertiaDeg` relates an arithmetic Frobenius over `K`
to one over an intermediate field `M`, at the cost of a power: the exponent is the residue degree
`f(𝔓 / 𝔭)` of the intermediate prime. This file records that statement for the one intermediate
field a fibre count actually uses, `L ^ ⟨σ⟩`, and the case in which the exponent disappears.

The base is spelled `IntermediateField.fixedField (Subgroup.zpowers σ)` rather than abbreviated,
following `TauCeti.FieldTheory.Galois.FixedField`.

## Main results

* `AlgEquiv.exists_isArithFrobAt_fixedField_pow_inertiaDeg`: over `L ^ ⟨σ⟩` there is an arithmetic
  Frobenius at `Q` restricting to `τ ^ f(𝔓 / 𝔭)`.
* `AlgEquiv.exists_isArithFrobAt_fixedField_of_inertiaDeg_eq_one`: when `f(𝔓 / 𝔭) = 1` it
  restricts to `τ` itself.
-/

public section

open NumberField IntermediateField

open scoped NumberField

namespace AlgEquiv

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

-- Source. Both statements are specified by the Chebotarev roadmap:
-- `TauCetiRoadmap/Chebotarev/README.md` §8.2 puts `E = L^⟨σ⟩` and needs, for `𝔭` unramified in `L`
-- and `𝔓 = Q ∩ 𝓞 E`, that "8.1 gives `Frob_{L/E}(𝔓) = Frob_{L/K}(Q)` on the nose" exactly when
-- `f(𝔓/𝔭) = 1`; it pins them at `TauCetiRoadmap/Chebotarev/Suggested.lean` as
-- `artinClass_restrict_fixedField` and `isArithFrobAt_fixedField_of_inertiaDeg_one`.

/-- **The tower formula over the fixed field of `⟨σ⟩`.** For a prime `Q` of `𝓞 L` unramified over
`K`, with `𝔓 = Q ∩ 𝓞 (L ^ ⟨σ⟩)` and `𝔭 = Q ∩ 𝓞 K`, an arithmetic Frobenius `τ` at `Q` over `K`
becomes, after raising to the residue degree `f(𝔓 / 𝔭)`, the restriction of an arithmetic Frobenius
at `Q` over `L ^ ⟨σ⟩`.

This is `TauCeti.NumberField.exists_isArithFrobAt_pow_inertiaDeg` at the intermediate field a fibre
count uses. It is stated separately because that base carries the instances only through the fixed
field's own construction, and a caller should not have to rediscover them. -/
theorem exists_isArithFrobAt_fixedField_pow_inertiaDeg (σ : L ≃ₐ[K] L)
    (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (𝔓 : Ideal (𝓞 (fixedField (Subgroup.zpowers σ)))) (𝔭 : Ideal (𝓞 K))
    (hQE : Q.under (𝓞 (fixedField (Subgroup.zpowers σ))) = 𝔓) (hQK : Q.under (𝓞 K) = 𝔭)
    (hur : ∀ (Q' : Ideal (𝓞 L)) [Q'.IsPrime] [Q'.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q')
    (τ : L ≃ₐ[K] L) (hτ : IsArithFrobAt (𝓞 K) τ Q) :
    ∃ τE : L ≃ₐ[fixedField (Subgroup.zpowers σ)] L,
      IsArithFrobAt (𝓞 (fixedField (Subgroup.zpowers σ))) τE Q ∧
        AlgEquiv.restrictScalars K τE = τ ^ 𝔓.inertiaDeg (𝓞 K) :=
  exists_isArithFrobAt_pow_inertiaDeg _ Q 𝔓 𝔭 hQE hQK hur τ hτ

/-- **At residue degree one the exponent disappears.** The relative Frobenius over `L ^ ⟨σ⟩` then
restricts to the absolute one unpowered, which is the only situation in which a fibre count may
compare the two without an exponent. -/
theorem exists_isArithFrobAt_fixedField_of_inertiaDeg_eq_one (σ : L ≃ₐ[K] L)
    (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (𝔓 : Ideal (𝓞 (fixedField (Subgroup.zpowers σ)))) (𝔭 : Ideal (𝓞 K))
    (hQE : Q.under (𝓞 (fixedField (Subgroup.zpowers σ))) = 𝔓) (hQK : Q.under (𝓞 K) = 𝔭)
    (hf : 𝔓.inertiaDeg (𝓞 K) = 1)
    (hur : ∀ (Q' : Ideal (𝓞 L)) [Q'.IsPrime] [Q'.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q')
    (τ : L ≃ₐ[K] L) (hτ : IsArithFrobAt (𝓞 K) τ Q) :
    ∃ τE : L ≃ₐ[fixedField (Subgroup.zpowers σ)] L,
      IsArithFrobAt (𝓞 (fixedField (Subgroup.zpowers σ))) τE Q ∧
        AlgEquiv.restrictScalars K τE = τ := by
  obtain ⟨τE, hfrob, hres⟩ :=
    exists_isArithFrobAt_fixedField_pow_inertiaDeg σ Q 𝔓 𝔭 hQE hQK hur τ hτ
  exact ⟨τE, hfrob, by rw [hres, hf, pow_one]⟩

end AlgEquiv
