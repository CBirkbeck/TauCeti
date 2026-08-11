/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.SpvOfIdeal
public import TauCeti.RingTheory.Valuation.CofinalIdeal.Restrict

/-!
# The restriction underlying the retraction `r_I`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), §7.1.2.**

A point of `Spv A` is sent to the class of its canonical valuation restricted to `cΓ_v(I)`. The
restriction itself, together with its interface, lives in
`TauCeti.RingTheory.Valuation.CofinalIdeal.Restrict`; this file only carries it to the level of
points.

Wedhorn's retraction has two properties beyond being this map: it **lands in** `Spv (A, I)`, and
it **fixes** that subspace pointwise. The first is proved here. The second is not, so the map
still carries codomain `Spv A` rather than the subspace, and is still named for what it does —
restriction to `I` — rather than for the retraction property it does not yet carry.

## Main definitions

* `TauCeti.ValuationSpectrum.restrictToIdeal` : the restriction, at the level of points of
  `Spv A`.

## Main results

* `TauCeti.ValuationSpectrum.restrictToIdeal_def` : the point map, unfolded through the
  canonical valuation.
* `TauCeti.ValuationSpectrum.vle_restrictToIdeal` : the valuative relation of the restricted
  point, in terms of the original one.
* `TauCeti.ValuationSpectrum.restrictToIdeal_mem_spvOfIdeal` : the restriction lands in
  `Spv (A, I)`. The case split is Wedhorn's: where `I` meets `cΓ_v`, the subgroup `cΓ_v(I)`
  collapses to `cΓ_v` and a generator brackets the bound; where it does not, `cΓ_v(I)` is the
  greatest ideal-cofinal convex subgroup and the bound is cofinal by that maximality.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.1.2
-/

public section

namespace TauCeti.ValuationSpectrum

open MonoidWithZeroHom TauCeti TauCeti.Valuation

variable {A : Type*} [CommRing A]

/-- **The underlying map of Wedhorn's §7.1.2 retraction.** A point of `Spv A` is sent to the
class of its canonical valuation restricted to `cΓ_v(I)`. -/
noncomputable def restrictToIdeal (v : Spv A) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) : Spv A :=
  ofValuation (v.valuation.restrictToIdeal I hfg)

/-- **The point map, unfolded through the canonical valuation.** Consumers rewrite through this
to reach the valuation-level restriction rather than unfolding the definition, whose body is not
exposed. Note this is the definitional unfolding at `v.valuation`, not a formula valid at an
arbitrary representative of the class. -/
theorem restrictToIdeal_def (v : Spv A) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    restrictToIdeal v I hfg = ofValuation (v.valuation.restrictToIdeal I hfg) :=
  (rfl)

/-- **The valuative relation of the restricted point.** Comparison is the whole observable
content of a point of `Spv A`, so this is the interface to `restrictToIdeal` at the level of
points: `a ≤ b` after restriction exactly when `a`'s value is discarded, or `b`'s is kept and
`a ≤ b` held already. The side conditions are discharged by
`TauCeti.Valuation.restrictToIdeal_eq_zero_iff`. -/
@[simp]
theorem vle_restrictToIdeal (v : Spv A) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (a b : A) :
    (restrictToIdeal v I hfg).toValuativeRel.vle a b ↔
      v.valuation.restrictToIdeal I hfg a = 0 ∨
        v.valuation.restrictToIdeal I hfg b ≠ 0 ∧ v.toValuativeRel.vle a b := by
  rw [restrictToIdeal_def, vle_ofValuation, TauCeti.Valuation.restrictToIdeal_le_iff]
  exact or_congr_right (and_congr_right fun _ ↦ valuation_le_iff v a b)

/-- The **meets** branch of `restrictToIdeal_mem_spvOfIdeal`. When `I` meets `cΓ_v`, Wedhorn's
`cΓ_v(I)` collapses to `cΓ_v` itself, so every element of the restricted value group is bracketed
by a characteristic generator `g ≥ 1` and its inverse; the ring element realising `g` is then the
witness that the restricted valuation has full characteristic group. -/
private theorem characteristicSubgroup_restrictToIdeal_eq_top_of_meets (v : Spv A) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (hm : IdealMeetsCharacteristicSubgroup v.valuation I) :
    characteristicSubgroup (v.valuation.restrictToIdeal I hfg) = ⊤ := by
  rw [← hasFullCharacteristicGroup_iff_characteristicSubgroup_eq_top,
    hasFullCharacteristicGroup_iff]
  intro γ hγ
  have hγ0 : ValueGroup₀.embedding γ ≠ 0 := fun h =>
    hγ.ne' (ValueGroup₀.embedding_injective (by simpa using h))
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.mp hγ0
  -- rewriting the goal, not the hypothesis: `u`'s own type mentions `cΓ_v(I)`, so rewriting
  -- that away inside the hypothesis is not type correct
  have hmem : OrderMonoidIso.unitsWithZero (u : (ValueGroup₀ (.ofClass v.valuation))ˣ)
      ∈ characteristicSubgroup v.valuation := by
    rw [← characteristicSubgroupOfIdeal_of_meets hfg hm]
    exact ConvexSubgroup.mem_comapUnitsWithZero.mp u.2
  obtain ⟨g, hg, hginv, hgle⟩ := mem_characteristicSubgroup_iff.mp hmem
  obtain ⟨hg1, a, hga⟩ := mem_characteristicGenerators.mp hg
  refine ⟨a, ?_, ?_⟩
  · -- `a` is kept by the restriction, since its value is the generator `g ≥ 1`
    have h1a : (1 : RestrictedValues v.valuation I hfg) ≤
        Valuation.restrictToIdeal v.valuation I hfg a :=
      one_le_restrictToIdeal _ _ _ (by rw [hga]; exact_mod_cast hg1)
    rw [← ValueGroup₀.embedding_strictMono.le_iff_le, map_inv₀,
      Valuation.embedding_restrict, ← hu,
      inv_le_comm₀ (zero_lt_one.trans_le h1a) (pos_iff_ne_zero.mpr WithZero.coe_ne_zero),
      ← WithZero.coe_inv, restrictToIdeal_coe_le_iff, hga]
    have hcoe : ((OrderMonoidIso.unitsWithZero
          ((u⁻¹ : (ConvexSubgroup.comapUnitsWithZero
            (characteristicSubgroupOfIdeal v.valuation I hfg)).toSubgroup) :
            (ValueGroup₀ (.ofClass v.valuation))ˣ) :
          valueGroup (.ofClass v.valuation)) : ValueGroup₀ (.ofClass v.valuation)) =
        (((u⁻¹ : (ConvexSubgroup.comapUnitsWithZero
            (characteristicSubgroupOfIdeal v.valuation I hfg)).toSubgroup) :
          (ValueGroup₀ (.ofClass v.valuation))ˣ) : ValueGroup₀ (.ofClass v.valuation)) :=
      WithZero.coe_unitsWithZeroEquiv_eq_units_val _
    rw [← hcoe, WithZero.coe_le_coe]
    simp only [map_inv, InvMemClass.coe_inv]
    simpa using inv_le_inv_iff.mpr hginv
  · rw [← ValueGroup₀.embedding_strictMono.le_iff_le, Valuation.embedding_restrict, ← hu,
      restrictToIdeal_coe_le_iff, hga]
    have hcoe : ((OrderMonoidIso.unitsWithZero (u : (ValueGroup₀ (.ofClass v.valuation))ˣ) :
        valueGroup (.ofClass v.valuation)) : ValueGroup₀ (.ofClass v.valuation)) =
        ((u : (ValueGroup₀ (.ofClass v.valuation))ˣ) : ValueGroup₀ (.ofClass v.valuation)) :=
      WithZero.coe_unitsWithZeroEquiv_eq_units_val _
    rw [← hcoe, WithZero.coe_le_coe]
    exact hgle

/-- The **not-meets** branch of `restrictToIdeal_mem_spvOfIdeal`. When `I` does not meet `cΓ_v`,
`cΓ_v(I)` is the *greatest* ideal-cofinal convex subgroup, so each `a ∈ I` is already cofinal
below every member of it — and the members are exactly the nonzero values the restriction keeps,
so cofinality transfers to the restricted valuation. -/
private theorem cofinalValue_restrictToIdeal_of_not_meets (v : Spv A) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (hm : ¬ IdealMeetsCharacteristicSubgroup v.valuation I) :
    ∀ a ∈ I, CofinalValue (v.valuation.restrictToIdeal I hfg) a := by
  intro a ha
  have hgreat : IdealCofinalFor v.valuation
      (characteristicSubgroupOfIdeal v.valuation I hfg) I :=
    (isGreatestIdealCofinal_characteristicSubgroupOfIdeal hfg hm).1
  have hcof := cofinalValueFor_def.mp (idealCofinalFor_def.mp hgreat a ha)
  rw [cofinalValue_iff]
  intro γ hγ
  -- the bound is a nonzero element of the restricted value monoid, hence a member of `cΓ_v(I)`
  have hγ0 : ValueGroup₀.embedding γ ≠ 0 := fun h =>
    hγ.ne' (ValueGroup₀.embedding_injective (by simpa using h))
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.mp hγ0
  -- its image in the value group of `v` lies in `cΓ_v(I)`, so `a` is cofinal below it
  have hmem := ConvexSubgroup.mem_comapUnitsWithZero.mp u.2
  obtain ⟨n, hn⟩ := hcof _ hmem
  refine ⟨n, ?_⟩
  rw [← map_pow, Valuation.restrict_lt_iff_lt_embedding, ← hu,
    restrictToIdeal_lt_coe_iff, map_pow]
  -- `OrderMonoidIso.unitsWithZero` and `WithZero.unitsWithZeroEquiv` agree, but only up to
  -- defeq, so the bridge has to be stated rather than rewritten with
  have hcoe : ((OrderMonoidIso.unitsWithZero (u : (ValueGroup₀ (.ofClass v.valuation))ˣ) :
      valueGroup (.ofClass v.valuation)) : ValueGroup₀ (.ofClass v.valuation)) =
      ((u : (ValueGroup₀ (.ofClass v.valuation))ˣ) : ValueGroup₀ (.ofClass v.valuation)) :=
    WithZero.coe_unitsWithZeroEquiv_eq_units_val _
  rwa [hcoe] at hn

/-- **Wedhorn §7.1.2: the restriction lands in `Spv (A, I)`.** This is the substantive half of
the roadmap's `r_I : Spv A → Spv (A, I)`: the point `restrictToIdeal v I` really does satisfy the
condition cutting out the subspace. The two branches are Wedhorn's own case split on whether `I`
meets `cΓ_v`, and each is proved above. -/
@[simp]
theorem restrictToIdeal_mem_spvOfIdeal (v : Spv A) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    restrictToIdeal v I hfg ∈ spvOfIdeal I hfg := by
  rw [restrictToIdeal_def, mem_spvOfIdeal_ofValuation,
    characteristicSubgroupOfIdeal_eq_top_iff]
  by_cases hm : IdealMeetsCharacteristicSubgroup v.valuation I
  · exact Or.inr (characteristicSubgroup_restrictToIdeal_eq_top_of_meets v I hfg hm)
  · exact Or.inl (cofinalValue_restrictToIdeal_of_not_meets v I hfg hm)

/-- **The roadmap's `r_I : Spv A → Spv (A, I)`**, with the codomain the roadmap asks for. This is
`restrictToIdeal` corestricted along the landing theorem, so a consumer receives a point of the
subspace rather than an `Spv A`-point plus a membership proof to carry around.

It is named for the restriction rather than for a retraction: that it *is* a retraction needs the
second law — that it fixes `Spv (A, I)` pointwise — which is proved separately. -/
noncomputable def restrictToIdealCodRestrict (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (v : Spv A) :
    (spvOfIdeal I hfg : Set (Spv A)) :=
  ⟨restrictToIdeal v I hfg, restrictToIdeal_mem_spvOfIdeal v I hfg⟩

/-- The corestricted map is the plain one, read in `Spv A`. -/
@[simp]
theorem coe_restrictToIdealCodRestrict (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (v : Spv A) :
    (restrictToIdealCodRestrict I hfg v : Spv A) = restrictToIdeal v I hfg :=
  (rfl)

end TauCeti.ValuationSpectrum
