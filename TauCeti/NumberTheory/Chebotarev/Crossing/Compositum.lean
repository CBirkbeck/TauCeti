/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import TauCeti.FieldTheory.IntermediateField.Adjoin.SupFieldRange
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank

/-!
# The cyclotomic compositum `M = L(μ_m)` and its joint restriction isomorphism

Let `L / K` be a Galois extension of number fields and let `M = L(μ_m)` be obtained from `L`
by adjoining the `m`-th roots of unity. When `m` is coprime to the discriminant of `L`, the
two restriction maps out of `Gal(M/K)` — to `Gal(L/K)`, and to `(ZMod m)ˣ` via the cyclotomic
character — are *jointly* bijective:

`Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ`.

## Main results

* `NumberField.Chebotarev.isGalois_of_isGalois_of_isCyclotomicExtension`: `M / K` is itself
  Galois, so `Gal(M/K)` below is not an extra assumption.
* `NumberField.Chebotarev.autToPow_bijective`: the cyclotomic character
  `Gal(M/L) → (ZMod m)ˣ` is bijective.
* `NumberField.Chebotarev.restrictNormalHom_prod_autToPow_injective`: the joint restriction
  is faithful (no arithmetic hypothesis needed).
* `NumberField.Chebotarev.restrictNormalHom_prod_autToPow_bijective`: it is bijective.
* `NumberField.Chebotarev.galEquivProd`: that map packaged as a `MulEquiv`, with
  `NumberField.Chebotarev.galEquivProd_apply` computing both of its components.

The two general prerequisites this rests on are stated where they belong rather than here:
the degree identity `[M : K] = φ m` is `IsCyclotomicExtension.finrank_eq_totient` in
`TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank`, and the compositum step
`K(ζ) ⊔ L = ⊤` is `TauCeti.IntermediateField.adjoin_sup_fieldRange_eq_top` in
`TauCeti.FieldTheory.IntermediateField.Adjoin.SupFieldRange`. Neither mentions Chebotarev.

## Implementation notes

That `M / K` is Galois is *derived*, not assumed: `M` is the compositum of `L` with `K(ζ)`,
both of which are normal over `K`, and the engine for a compositum of two normal extensions is
Mathlib's `IntermediateField.normal_sup`. So `Gal(M/K)` below rests on no hypothesis beyond
`IsGalois K L` and the cyclotomic tower.

Faithfulness of the joint restriction is *not* re-derived here: it is Mathlib's compositum
engine `IntermediateField.fixingSubgroup_sup` (with `fixingSubgroup_top`), applied to `K(ζ)`
and the image of `L` inside `M`. We invoke that shared lemma rather than
`IntermediateField.restrictRestrictAlgEquivMapHom_injective`, which is built from it, because
the latter concerns `Gal(M/L) →* Gal(K(ζ)/K)` whereas the map here is defined on `Gal(M/K)`;
using it would first require transporting an element of `Gal(M/K)` that fixes `L` into
`Gal(M/L)`, which is strictly more work than calling the underlying lemma directly.

Surjectivity does go through a degree count. That is not an oversight: surjectivity onto the
`(ZMod m)ˣ` factor *is* the assertion that the `m`-th cyclotomic polynomial stays irreducible
over `L`, which is exactly what the coprimality hypothesis `hcop` buys. Mathlib's companion
`restrictRestrictAlgEquivMapHom_surjective` needs `K(ζ) ⊓ L = ⊥`, and the proof of that
intersection statement is the same discriminant input, so it would not avoid the arithmetic.

Adapted from the Birkbeck–Brasca Chebotarev density project.
-/

public section

namespace NumberField.Chebotarev

section Compositum

variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]

include L m in
omit [NumberField L] in
/-- **The cyclotomic compositum of a Galois extension is Galois.** If `L / K` is Galois and
`M = L(μ_m)`, then `M / K` is Galois: `M` is the compositum of `L` with `K(ζ)`
(`TauCeti.IntermediateField.adjoin_sup_fieldRange_eq_top`), both of which are normal over `K`,
and a compositum of normal extensions is normal (`IntermediateField.normal_sup`). Separability
is automatic in characteristic zero.

Both tower hypotheses are needed, which is what the name records: the cyclotomic extension is
`M / L`, and `L / K` is Galois. Mathlib's `IsCyclotomicExtension.isGalois` is the one-step
statement, for a cyclotomic extension of the base itself.

This is what makes `IsGalois K M` a *conclusion* of this file rather than a hypothesis of the
results below. It is a theorem and not an `instance` because neither `L` nor `m` can be
recovered from the goal `IsGalois K M`, so there is no synthesization order; call sites
introduce it with `have` instead. -/
theorem isGalois_of_isGalois_of_isCyclotomicExtension : IsGalois K M := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M
    (Set.mem_singleton m) (NeZero.ne m)
  have hcyc : IsCyclotomicExtension {m} K (IntermediateField.adjoin K {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := K)
  have : IsGalois K (IntermediateField.adjoin K {ζ}) :=
    IsCyclotomicExtension.isGalois (S := {m}) (K := K) (L := IntermediateField.adjoin K {ζ})
  have : Normal K ((IsScalarTower.toAlgHom K L M).fieldRange) :=
    Normal.of_algEquiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L M))
  have hsup : Normal K
      (IntermediateField.adjoin K {ζ} ⊔ (IsScalarTower.toAlgHom K L M).fieldRange :
        IntermediateField K M) := IntermediateField.normal_sup K M _ _
  rw [TauCeti.IntermediateField.adjoin_sup_fieldRange_eq_top K L M
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ)] at hsup
  have : Normal K M := Normal.of_algEquiv (h := hsup) IntermediateField.topEquiv
  exact ⟨⟩

/-- **The cyclotomic character of the top layer is bijective.** For `M = L(μ_m)` with `m`
coprime to `discr L`, the character `Gal(M/L) → (ZMod m)ˣ` is a bijection: it is injective by
`IsPrimitiveRoot.autToPow_injective`, and both sides have `φ m` elements by
`IsCyclotomicExtension.finrank_eq_totient`. -/
theorem autToPow_bijective (hcop : ((NumberField.discr L).natAbs).Coprime m)
    {ζ : M} (hζ : IsPrimitiveRoot ζ m) : Function.Bijective (hζ.autToPow L) := by
  have : IsGalois L M := IsCyclotomicExtension.isGalois (S := {m}) (K := L) (L := M)
  have hcard : Nat.card Gal(M/L) = Nat.card (ZMod m)ˣ := by
    rw [IsGalois.card_aut_eq_finrank L M, IsCyclotomicExtension.finrank_eq_totient L M m hcop,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  exact (Nat.bijective_iff_injective_and_card _).mpr ⟨hζ.autToPow_injective L, hcard⟩

omit [NumberField K] [NumberField L] in
/-- **The joint restriction is faithful.** An automorphism of `M = L(μ_m)` over `K` that is
trivial on `L` and trivial on the `m`-th roots of unity is the identity. No arithmetic
hypothesis is needed: this is Mathlib's compositum engine
(`IntermediateField.fixingSubgroup_sup`) applied to `K(ζ)` and `L`, whose compositum is `M`. -/
theorem restrictNormalHom_prod_autToPow_injective {ζ : M} (hζ : IsPrimitiveRoot ζ m) :
    Function.Injective ((AlgEquiv.restrictNormalHom L).prod (hζ.autToPow K)) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  rw [MonoidHom.prod_apply, Prod.mk_eq_one] at hσ
  obtain ⟨hσL, hσζ⟩ := hσ
  have hζfix : σ ζ = ζ := by
    have hspec := hζ.autToPow_spec K σ
    rw [hσζ] at hspec
    rw [← hspec, Units.val_one]
    rcases eq_or_lt_of_le (NeZero.one_le (n := m)) with h1 | h1
    · have hm1 : m = 1 := h1.symm
      subst hm1
      have : ζ = 1 := by simpa using hζ.pow_eq_one
      simp [this]
    · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, pow_one]
  have hLfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
    intro x
    have hcomm := σ.restrictNormal_commutes L x
    have hrn : σ.restrictNormal L = (1 : Gal(L/K)) := hσL
    rw [hrn] at hcomm
    simpa using hcomm.symm
  -- `σ` fixes the compositum of `K(ζ)` and (the image of) `L`, which is all of `M`.
  have hmem : σ ∈ IntermediateField.fixingSubgroup
      (IntermediateField.adjoin K {ζ} ⊔ (IsScalarTower.toAlgHom K L M).fieldRange) := by
    rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem y hy => rw [Set.mem_singleton_iff] at hy; subst hy; exact hζfix
      | algebraMap r => exact σ.commutes r
      | add a b _ _ ha hb => rw [map_add, ha, hb]
      | inv a _ ha => rw [map_inv₀, ha]
      | mul a b _ _ ha hb => rw [map_mul, ha, hb]
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      rintro _ ⟨x, rfl⟩
      exact hLfix x
  have htop : IntermediateField.adjoin K {ζ} ⊔ (IsScalarTower.toAlgHom K L M).fieldRange
      = (⊤ : IntermediateField K M) :=
    TauCeti.IntermediateField.adjoin_sup_fieldRange_eq_top K L M
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ)
  rw [htop, IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at hmem
  exact hmem

/-- **The joint restriction is bijective.** The two restrictions out of `Gal(M/K)` — to
`Gal(L/K)`, and to `(ZMod m)ˣ` via the cyclotomic character — are jointly bijective.
Faithfulness is `restrictNormalHom_prod_autToPow_injective`; surjectivity is then forced by
the degree identity `IsCyclotomicExtension.finrank_eq_totient`, since `[M : K] = [L : K] · φ m`.
-/
theorem restrictNormalHom_prod_autToPow_bijective
    (hcop : ((NumberField.discr L).natAbs).Coprime m) {ζ : M} (hζ : IsPrimitiveRoot ζ m) :
    Function.Bijective ((AlgEquiv.restrictNormalHom L).prod (hζ.autToPow K)) := by
  have : IsGalois L M := IsCyclotomicExtension.isGalois (S := {m}) (K := L) (L := M)
  have : IsGalois K M := isGalois_of_isGalois_of_isCyclotomicExtension K L M m
  have hcard : Nat.card Gal(M/K) = Nat.card (Gal(L/K) × (ZMod m)ˣ) := by
    rw [Nat.card_prod, IsGalois.card_aut_eq_finrank K M, IsGalois.card_aut_eq_finrank K L,
      ← Module.finrank_mul_finrank K L M, IsCyclotomicExtension.finrank_eq_totient L M m hcop,
      Nat.card_eq_fintype_card (α := (ZMod m)ˣ), ZMod.card_units_eq_totient]
  exact (Nat.bijective_iff_injective_and_card _).mpr
    ⟨restrictNormalHom_prod_autToPow_injective K L M m hζ, hcard⟩

/-- The joint restriction `Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ`, packaged as a `MulEquiv`. -/
noncomputable def galEquivProd (hcop : ((NumberField.discr L).natAbs).Coprime m)
    {ζ : M} (hζ : IsPrimitiveRoot ζ m) : Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ :=
  MulEquiv.ofBijective _ (restrictNormalHom_prod_autToPow_bijective K L M m hcop hζ)

/-- Both components of `galEquivProd`: it sends `σ` to its restriction to `L` paired with its
cyclotomic character. Consumers should compute with this rather than unfolding the
`MulEquiv.ofBijective` that packages it. -/
@[simp]
theorem galEquivProd_apply (hcop : ((NumberField.discr L).natAbs).Coprime m)
    {ζ : M} (hζ : IsPrimitiveRoot ζ m) (σ : Gal(M/K)) :
    galEquivProd K L M m hcop hζ σ = (σ.restrictNormal L, hζ.autToPow K σ) := by
  -- Not a bare `rfl`: this theorem is exported, so `galEquivProd`'s body is not available for
  -- unfolding downstream. Rewriting by its equation lemma first leaves a defeq between
  -- `AlgEquiv.restrictNormalHom L σ` and `σ.restrictNormal L`, which is Mathlib's to discharge.
  rw [galEquivProd]
  rfl

end Compositum

end NumberField.Chebotarev
