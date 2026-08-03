/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.MeasureTheory.Group.FundamentalDomain
public import TauCeti.NumberTheory.Modular.PSLFundamentalDomain

/-!
# A fundamental domain for `Γ₁(N)`

The image `Gamma1PSL N` of the congruence subgroup `Γ₁(N) ⊆ SL(2, ℤ)` in
`PSL(2, ℤ)` has finite index, so the `[PSL(2, ℤ) : Gamma1PSL N]`-fold coset tiling
`gamma1FundDomain N = ⋃ q, (q.out)⁻¹ • 𝒟ᵒ` is a fundamental domain for its action on
`(ℍ, volume)` — the coset-tiling theorem applied to
`ModularGroup.isFundamentalDomain_fdo_PSL`. The tiling is finite, so the domain has
finite invariant measure, integrals over it decompose as finite sums over tiles, and
the Petersson integrand of a pair of `Γ₁(N)`-cusp forms is integrable on it.

## Main definitions

* `CongruenceSubgroup.Gamma1PSL`: the image of `Γ₁(N)` in `PSL(2, ℤ)`, with its
  `FiniteIndex` instance.
* `CongruenceSubgroup.gamma1FundDomain`: the coset tiling of `𝒟ᵒ`.

## Main results

* `CongruenceSubgroup.isFundamentalDomain_gamma1FundDomain`: it is a `Gamma1PSL N`-
  fundamental domain.
* `CongruenceSubgroup.volume_gamma1FundDomain_lt_top`: it has finite invariant measure.
* `CongruenceSubgroup.setIntegral_gamma1FundDomain_eq_sum`: integrals over it are finite
  sums of integrals over the tiles.
* `CongruenceSubgroup.integrableOn_petersson_gamma1FundDomain`: integrability of the
  Petersson integrand of `Γ₁(N)`-cusp forms.

This realizes the "measurable finite-volume fundamental domain for every finite-index
subgroup" milestone of the ModularForms roadmap's Layer 3 for `Γ₁(N)`. Ported from the
AINTLIB `LeanModularForms` project (`LeanModularForms/Modularforms/PeterssonLevelN.lean`).
-/

public section

noncomputable section

open scoped MatrixGroups Pointwise

open UpperHalfPlane ModularGroup MeasureTheory Matrix.SpecialLinearGroup

namespace CongruenceSubgroup

variable {N : ℕ} [NeZero N]

/-- The image of `Γ₁(N) ⊆ SL(2, ℤ)` in `PSL(2, ℤ) = SL(2, ℤ) ⧸ center`. -/
def Gamma1PSL (N : ℕ) [NeZero N] : Subgroup PSL(2, ℤ) :=
  (Gamma1 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- The image of the finite-index subgroup `Γ₁(N)` under the surjection onto `PSL(2, ℤ)`
has finite index. -/
instance : (Gamma1PSL N).FiniteIndex := by
  refine ⟨fun h ↦ ?_⟩
  have h_dvd : (Gamma1PSL N).index ∣ (Gamma1 N).index :=
    Subgroup.index_map_dvd _ QuotientGroup.mk_surjective
  rw [h] at h_dvd
  exact Subgroup.FiniteIndex.index_ne_zero (Nat.eq_zero_of_zero_dvd h_dvd)

instance : Countable (PSL(2, ℤ) ⧸ Gamma1PSL N) := Quotient.countable

instance : Fintype (PSL(2, ℤ) ⧸ Gamma1PSL N) := Subgroup.fintypeQuotientOfFiniteIndex

/-- The coset tiling of the open modular domain: the union of the
`[PSL(2, ℤ) : Gamma1PSL N]` translates `(q.out)⁻¹ • 𝒟ᵒ`, a fundamental domain
for `Γ₁(N)` (through its projective image) acting on `ℍ`. -/
def gamma1FundDomain (N : ℕ) [NeZero N] : Set ℍ :=
  ⋃ q : PSL(2, ℤ) ⧸ Gamma1PSL N, ((q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ)

/-- The coset tiling `gamma1FundDomain N` is a fundamental domain for the image of
`Γ₁(N)` in `PSL(2, ℤ)` acting on `ℍ` with the invariant measure. -/
theorem isFundamentalDomain_gamma1FundDomain :
    IsFundamentalDomain (Gamma1PSL N) (gamma1FundDomain N) (volume : Measure ℍ) :=
  isFundamentalDomain_fdo_PSL.subgroup_iUnion_out_inv_smul _

/-- Distinct coset tiles `(q.out)⁻¹ • 𝒟ᵒ` are pairwise a.e.-disjoint. -/
theorem aedisjoint_gamma1_coset_tiles :
    Pairwise (fun q₁ q₂ : PSL(2, ℤ) ⧸ Gamma1PSL N ↦
      AEDisjoint (volume : Measure ℍ) ((q₁.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))
        ((q₂.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))) := fun q₁ q₂ hne ↦
  isFundamentalDomain_fdo_PSL.aedisjoint fun hg ↦ hne <| by
    rw [← q₁.out_eq, ← q₂.out_eq, inv_injective hg]

/-- Each coset tile is null-measurable. -/
theorem nullMeasurableSet_gamma1_coset_tile (q : PSL(2, ℤ) ⧸ Gamma1PSL N) :
    NullMeasurableSet ((q.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ)) (volume : Measure ℍ) :=
  isFundamentalDomain_fdo_PSL.nullMeasurableSet_smul _

/-- **Integral over the `Γ₁(N)`-fundamental domain decomposes as a tile sum.** For an
integrable function `h`, the integral over `gamma1FundDomain N` equals the finite sum of
the integrals over the coset tiles. -/
theorem setIntegral_gamma1FundDomain_eq_sum (h : ℍ → ℂ)
    (h_int : IntegrableOn h (gamma1FundDomain N) (volume : Measure ℍ)) :
    ∫ τ in gamma1FundDomain N, h τ =
      ∑ q : PSL(2, ℤ) ⧸ Gamma1PSL N,
        ∫ τ in ((q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ := by
  rw [gamma1FundDomain,
    integral_iUnion_ae nullMeasurableSet_gamma1_coset_tile aedisjoint_gamma1_coset_tiles
      h_int,
    tsum_fintype]

/-- The `Γ₁(N)`-fundamental domain has finite invariant measure: finitely many tiles,
each of measure `vol 𝒟ᵒ ≤ vol 𝒟 < ∞`. -/
theorem volume_gamma1FundDomain_lt_top : (volume : Measure ℍ) (gamma1FundDomain N) < ⊤ := by
  rw [gamma1FundDomain]
  refine lt_of_le_of_lt (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr fun q _ ↦ ?_
  rw [measure_smul]
  exact lt_of_le_of_lt (measure_mono fdo_subset_fd) volume_fd_lt_top

/-- The Petersson integrand `petersson k f g` of two `Γ₁(N)`-cusp forms is integrable on
the `Γ₁(N)`-fundamental domain. -/
theorem integrableOn_petersson_gamma1FundDomain {k : ℤ}
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IntegrableOn (fun τ ↦ petersson k ⇑f ⇑g τ) (gamma1FundDomain N) (volume : Measure ℍ) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k ((Gamma1 N).map (mapGL ℝ)) f g
  exact IntegrableOn.of_bound volume_gamma1FundDomain_lt_top
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous g)).aestronglyMeasurable.restrict)
    C (ae_of_all _ fun τ ↦ hC τ)

end CongruenceSubgroup
