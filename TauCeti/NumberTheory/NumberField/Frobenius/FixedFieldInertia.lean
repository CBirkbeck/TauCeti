/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.FixedField
public import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup

/-!
# The residue degree of a prime below the fixed field of an automorphism

Let `σ` be any automorphism of `L` over `K`, let `E = L ^ ⟨σ⟩`, and let `Q` be a nonzero prime of
`𝓞 L` unramified over `𝓞 K` with Frobenius `φ`.  Then the residue degree of `Q ∩ 𝓞 E` over `𝓞 K`
is `orderOf φ` divided by the number of elements of `⟨φ⟩ ⊓ ⟨σ⟩`.

Both factors are decomposition groups.  In the tower `K ⊆ E ⊆ L` the inertia degree at `Q` over
`𝓞 K` is `orderOf φ`, because a Frobenius element generates the decomposition group; over `𝓞 E` it
is the size of the decomposition group inside `Gal(L/E)`, and the Galois correspondence identifies
`Gal(L/E)` with `⟨σ⟩` acting exactly as it does over `K`, so that group is `⟨φ⟩ ⊓ ⟨σ⟩`.
Multiplicativity of the inertia degree in a tower gives the quotient, stated here as a product so
that no natural-number division is truncated.

Taking `σ` to be the Frobenius itself makes the intersection all of `⟨σ⟩` and the residue degree
one; that special case is the hypothesis of
`NumberField.restrictScalars_eq_of_inertiaDeg_eq_one`, and so the step a fixed-field fibre count
runs through, since at residue degree one the relative Frobenius over `E` is the absolute one over
`K` with no power taken.

## Main results

* `Ideal.card_stabilizer_fixedField_eq_card_inf`: the decomposition group of `Q` over `E` has as
  many elements as `⟨φ⟩ ⊓ ⟨σ⟩`.
* `Ideal.inertiaDeg_under_fixedField_mul_card_inf`: that residue degree times the size of the
  intersection is `orderOf φ`.
* `Ideal.inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt`: at `σ = φ` the residue degree is
  one.

## References

Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.  The corresponding step of the
Birkbeck--Brasca Chebotarev development,
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0) at
commit `55a89985d47a3befcf6069aca1da250ff088b5c7`, is the private declaration
`inertiaDeg_under_E_eq_one_of_frobenius` in `CebotarevDensity/FixedFieldDensity.lean`.  There it is
one conjunct of a triple that also records the ramification index and the residue-field count, and
it carries `orderOf σ = Nat.card Gal(L/E)` as a hypothesis; that equality is a consequence of the
Galois correspondence and is derived here rather than assumed.  Upstream states only the `σ = φ`
case; the general residue degree above is not there.
-/

public section

open IntermediateField

open scoped NumberField Pointwise

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **The decomposition group over the fixed field is the intersection.**  For `E = L ^ ⟨σ⟩` and
`φ` a Frobenius at an unramified `Q`, the stabilizer of `Q` in `Gal(L/E)` has as many elements as
`⟨φ⟩ ⊓ ⟨σ⟩`. -/
theorem card_stabilizer_fixedField_eq_card_inf (σ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] {φ : L ≃ₐ[K] L}
    (hφ : IsArithFrobAt (𝓞 K) φ Q) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L) Q)
      = Nat.card ((Subgroup.zpowers φ ⊓ Subgroup.zpowers σ : Subgroup (L ≃ₐ[K] L))) := by
  set Z := Subgroup.zpowers σ with hZ
  set e := subgroupEquivAlgEquiv Z with he
  -- the Galois correspondence does not move points, so it does not move ideals either
  have hsmul : ∀ τ : ↥Z, (e τ) • Q = (τ : L ≃ₐ[K] L) • Q := fun τ ↦ by
    rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
    exact congrArg (Ideal.map · Q) (RingHom.ext fun y ↦ NumberField.RingOfIntegers.ext rfl)
  have hcomap : (MulAction.stabilizer (L ≃ₐ[↥(fixedField Z)] L) Q).comap (e : ↥Z →* _)
      = (MulAction.stabilizer (L ≃ₐ[K] L) Q).subgroupOf Z := by
    ext τ
    simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact Eq.congr_left (hsmul τ)
  have h1 : Nat.card ((MulAction.stabilizer (L ≃ₐ[↥(fixedField Z)] L) Q).comap (e : ↥Z →* _))
      = Nat.card (MulAction.stabilizer (L ≃ₐ[↥(fixedField Z)] L) Q) := by
    rw [Subgroup.comap_equiv_eq_map_symm]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ e.symm.injective).symm.toEquiv
  have h2 : Nat.card ((MulAction.stabilizer (L ≃ₐ[K] L) Q).subgroupOf Z)
      = Nat.card ((MulAction.stabilizer (L ≃ₐ[K] L) Q ⊓ Z : Subgroup (L ≃ₐ[K] L))) := by
    rw [← Subgroup.subgroupOf_map_subtype]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).toEquiv
  rw [← h1, hcomap, h2, zpowers_eq_stabilizer_of_isArithFrobAt Q hQ hφ]

/-- **The residue degree over the base, in the fixed field of any automorphism.**  For `E = L ^ ⟨σ⟩`
and `φ` a Frobenius at an unramified `Q`, the residue degree of `Q ∩ 𝓞 E` over `𝓞 K` is
`orderOf φ` divided by the size of `⟨φ⟩ ⊓ ⟨σ⟩`.  Stated as a product, so no natural-number division
is truncated.

`σ` is arbitrary here: it need not be a Frobenius at `Q`, nor fix `Q`. -/
theorem inertiaDeg_under_fixedField_mul_card_inf (σ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] {φ : L ≃ₐ[K] L}
    (hφ : IsArithFrobAt (𝓞 K) φ Q) :
    (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K)
        * Nat.card ((Subgroup.zpowers φ ⊓ Subgroup.zpowers σ : Subgroup (L ≃ₐ[K] L)))
      = orderOf φ := by
  set E := fixedField (Subgroup.zpowers σ) with hE
  have : IsScalarTower K ↥E L := E.isScalarTower_mid'
  have : IsGalois ↥E L := IsGalois.tower_top_intermediateField _
  have : Algebra.IsUnramifiedAt (𝓞 ↥E) Q := Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 K) Q
  have htower : Q.inertiaDeg (𝓞 K)
      = (Q.under (𝓞 ↥E)).inertiaDeg (𝓞 K) * Q.inertiaDeg (𝓞 ↥E) :=
    inertiaDeg_tower (Q.under (𝓞 ↥E)) Q
  have hE' : Q.inertiaDeg (𝓞 ↥E)
      = Nat.card ((Subgroup.zpowers φ ⊓ Subgroup.zpowers σ : Subgroup (L ≃ₐ[K] L))) := by
    rw [← card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt Q hQ]
    exact card_stabilizer_fixedField_eq_card_inf σ Q hQ hφ
  rw [(orderOf_eq_inertiaDeg_of_isArithFrobAt Q hQ hφ).symm, hE'] at htower
  exact htower.symm

/-- **The prime below `Q` in the fixed field of a Frobenius at `Q` has degree one.**  If `σ` is an
arithmetic Frobenius at a nonzero prime `Q` of `𝓞 L` unramified over `𝓞 K`, then `Q ∩ 𝓞 (L ^ ⟨σ⟩)`
has residue degree one over `𝓞 K`. -/
theorem inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1 := by
  have h := inertiaDeg_under_fixedField_mul_card_inf σ Q hQ hσ
  rw [inf_idem, Nat.card_zpowers] at h
  exact Nat.eq_of_mul_eq_mul_right (orderOf_pos σ) (by rw [one_mul]; exact h)

end Ideal
