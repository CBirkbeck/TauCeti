/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# The cyclotomic compositum `M = L(μ_m)` and its joint restriction isomorphism

Let `L / K` be a Galois extension of number fields and let `M = L(μ_m)` be obtained from `L`
by adjoining the `m`-th roots of unity. When `m` is coprime to the discriminant of `L`, the
two restriction maps out of `Gal(M/K)` — to `Gal(L/K)`, and to `(ZMod m)ˣ` via the cyclotomic
character — are *jointly* bijective:

`Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ`.

## Main results

* `NumberField.Chebotarev.finrank_eq_totient`: the degree identity `[M : K] = φ m` for an
  `m`-th cyclotomic extension `M / K` of number fields with `m` coprime to `discr K`.
* `NumberField.Chebotarev.restrictNormalHom_prod_autToPow_injective`: the joint restriction
  is faithful (no arithmetic hypothesis needed).
* `NumberField.Chebotarev.restrictNormalHom_prod_autToPow_bijective`: it is bijective.
* `NumberField.Chebotarev.galEquivProd`: that map packaged as a `MulEquiv`.
* `NumberField.Chebotarev.autToPow_bijective`: the cyclotomic character
  `Gal(M/L) → (ZMod m)ˣ` is bijective.

## Implementation notes

Faithfulness of the joint restriction is *not* re-derived here: it is Mathlib's compositum
engine `IntermediateField.fixingSubgroup_sup` (with `fixingSubgroup_top`), applied to `K(ζ)`
and the image of `L` inside `M`, whose compositum is `M` by `adjoin_sup_fieldRange_eq_top`.
We invoke that shared lemma rather than
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

/-- **The compositum step.** If `M` is generated over `L` by `ζ`, then inside `M` the
compositum of `K(ζ)` with the image of `L` is all of `M`, for any base field `K` of the
tower. This is the input to Mathlib's compositum engine
(`IntermediateField.fixingSubgroup_sup`) and is used both for the degree identity and for
faithfulness of the joint restriction. -/
theorem adjoin_sup_fieldRange_eq_top (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] {ζ : M}
    (hadj : Algebra.adjoin L ({ζ} : Set M) = ⊤) :
    IntermediateField.adjoin K {ζ} ⊔ (IsScalarTower.toAlgHom K L M).fieldRange = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ ?_
  have hx : x ∈ Algebra.adjoin L ({ζ} : Set M) := hadj ▸ Algebra.mem_top
  refine Algebra.adjoin_induction (fun y hy ↦ ?_) (fun r ↦ ?_)
    (fun a b _ _ ha hb ↦ add_mem ha hb) (fun a b _ _ ha hb ↦ mul_mem ha hb) hx
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact le_sup_left (α := IntermediateField K M)
      (IntermediateField.mem_adjoin_simple_self K y)
  · exact le_sup_right (α := IntermediateField K M) ⟨r, rfl⟩

/-- A prime dividing the discriminant of an `m`-th cyclotomic extension of `ℚ` divides `m`. -/
theorem prime_dvd_of_dvd_natAbs_discr (E : Type*) [Field E] [NumberField E] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} ℚ E] {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ (NumberField.discr E).natAbs) : p ∣ m := by
  refine hp.dvd_of_dvd_pow (n := m.totient) (hpd.trans ?_)
  obtain ⟨c, hc⟩ := Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos m)
  rw [IsCyclotomicExtension.Rat.natAbs_discr (K := E) (n := m), hc,
    Nat.mul_div_cancel_left _ (Finset.prod_pos fun q hq ↦
      pow_pos (Nat.prime_of_mem_primeFactors hq).pos _)]
  exact dvd_mul_left _ _

/-- **The cyclotomic degree over a number field base.** If `M / K` is an `m`-th cyclotomic
extension of number fields and `m` is coprime to `discr K`, then `[M : K] = φ m`. -/
theorem finrank_eq_totient (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M]
    (hcop : ((NumberField.discr K).natAbs).Coprime m) :
    Module.finrank K M = m.totient := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) K M
    (Set.mem_singleton m) (NeZero.ne m)
  set K₁ : IntermediateField ℚ M := IntermediateField.adjoin ℚ {ζ}
  set K₂ : IntermediateField ℚ M := (IsScalarTower.toAlgHom ℚ K M).fieldRange
  have : IsCyclotomicExtension {m} ℚ K₁ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ)
  have : IsGalois ℚ K₁ := IsCyclotomicExtension.isGalois (S := {m}) (K := ℚ) (L := K₁)
  have hfinK₁ : Module.finrank ℚ K₁ = m.totient :=
    IsCyclotomicExtension.finrank K₁ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  have hsup : K₁ ⊔ K₂ = ⊤ :=
    adjoin_sup_fieldRange_eq_top ℚ K M
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ)
  let eK₂ : K ≃+* K₂ := ((IsScalarTower.toAlgHom ℚ K M : K →+* M)).rangeRestrictFieldEquiv
  have hdiscrK₂ : NumberField.discr K₂ = NumberField.discr K :=
    (NumberField.discr_eq_discr_of_ringEquiv (f := eK₂)).symm
  have hcoprime : IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) := by
    rw [hdiscrK₂, Int.isCoprime_iff_gcd_eq_one, Int.gcd]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    rw [Nat.dvd_gcd_iff] at hpdvd
    obtain ⟨hpa, hpb⟩ := hpdvd
    have hpm : p ∣ m := prime_dvd_of_dvd_natAbs_discr K₁ m hp hpa
    have hpgcd : p ∣ Nat.gcd (NumberField.discr K).natAbs m := Nat.dvd_gcd hpb hpm
    rw [hcop] at hpgcd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpgcd)
  have hld : K₁.LinearDisjoint K₂ :=
    NumberField.linearDisjoint_of_isGalois_isCoprime_discr (L := M) K₁ K₂ hcoprime
  have hfr : Module.finrank K₂ M = Module.finrank ℚ K₁ := hld.finrank_right_eq_finrank hsup
  have hrelabel : Module.finrank K M = Module.finrank K₂ M := by
    refine Algebra.finrank_eq_of_equiv_equiv eK₂ (RingEquiv.refl M) ?_
    ext x
    -- Both sides are the image of `x` in `M`; `eK₂` is that map with its range restricted,
    -- so unfolding the range coercion makes the two sides syntactically equal.
    change ((eK₂ x : M)) = (IsScalarTower.toAlgHom ℚ K M : K →+* M) x
    rfl
  rw [hrelabel, hfr, hfinK₁]

section Compositum

variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]

/-- **The cyclotomic character of the top layer is bijective.** For `M = L(μ_m)` with `m`
coprime to `discr L`, the character `Gal(M/L) → (ZMod m)ˣ` is a bijection: it is injective by
`IsPrimitiveRoot.autToPow_injective`, and both sides have `φ m` elements by
`finrank_eq_totient`. -/
theorem autToPow_bijective (hcop : ((NumberField.discr L).natAbs).Coprime m)
    {ζ : M} (hζ : IsPrimitiveRoot ζ m) : Function.Bijective (hζ.autToPow L) := by
  have : IsGalois L M := IsCyclotomicExtension.isGalois (S := {m}) (K := L) (L := M)
  have hcard : Nat.card Gal(M/L) = Nat.card (ZMod m)ˣ := by
    rw [IsGalois.card_aut_eq_finrank L M, finrank_eq_totient L M m hcop,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  exact (Nat.bijective_iff_injective_and_card _).mpr ⟨hζ.autToPow_injective L, hcard⟩

omit [NumberField K] [NumberField L] [IsGalois K M] in
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
    adjoin_sup_fieldRange_eq_top K L M
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ)
  rw [htop, IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at hmem
  exact hmem

/-- **The joint restriction is bijective.** The two restrictions out of `Gal(M/K)` — to
`Gal(L/K)`, and to `(ZMod m)ˣ` via the cyclotomic character — are jointly bijective.
Faithfulness is `restrictNormalHom_prod_autToPow_injective`; surjectivity is then forced by
the degree identity `finrank_eq_totient`, since `[M : K] = [L : K] · φ m`. -/
theorem restrictNormalHom_prod_autToPow_bijective
    (hcop : ((NumberField.discr L).natAbs).Coprime m) {ζ : M} (hζ : IsPrimitiveRoot ζ m) :
    Function.Bijective ((AlgEquiv.restrictNormalHom L).prod (hζ.autToPow K)) := by
  have : IsGalois L M := IsCyclotomicExtension.isGalois (S := {m}) (K := L) (L := M)
  have hcard : Nat.card Gal(M/K) = Nat.card (Gal(L/K) × (ZMod m)ˣ) := by
    rw [Nat.card_prod, IsGalois.card_aut_eq_finrank K M, IsGalois.card_aut_eq_finrank K L,
      ← Module.finrank_mul_finrank K L M, finrank_eq_totient L M m hcop,
      Nat.card_eq_fintype_card (α := (ZMod m)ˣ), ZMod.card_units_eq_totient]
  exact (Nat.bijective_iff_injective_and_card _).mpr
    ⟨restrictNormalHom_prod_autToPow_injective K L M m hζ, hcard⟩

/-- The joint restriction `Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ`, packaged as a `MulEquiv`. -/
noncomputable def galEquivProd (hcop : ((NumberField.discr L).natAbs).Coprime m)
    {ζ : M} (hζ : IsPrimitiveRoot ζ m) : Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ :=
  MulEquiv.ofBijective _ (restrictNormalHom_prod_autToPow_bijective K L M m hcop hζ)

end Compositum

end NumberField.Chebotarev
