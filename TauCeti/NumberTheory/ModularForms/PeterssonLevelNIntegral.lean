/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.Gamma1FundamentalDomain
public import TauCeti.NumberTheory.ModularForms.PeterssonCuspForm
public import TauCeti.NumberTheory.ModularForms.PeterssonLevelN

/-!
# The level-`N` Petersson pairing as an integral

The coset-sum definition of `CuspForm.petN` is identified with a genuine integral over
the `Γ₁(N)`-fundamental domain, and positive definiteness follows:

* `CuspForm.petN_eq_setIntegral_gamma1FundDomain`:
  `petN f g = c_N • ∫ τ in gamma1FundDomain N, petersson k f g τ`, where
  `c_N = slToPslQuotFiberCard N` is the (uniform) fiber size of the reindexing map
  `SL(2, ℤ) ⧸ Γ₁(N) → PSL(2, ℤ) ⧸ Gamma1PSL N`.
* `CuspForm.petN_definite`: `petN f f = 0 → f = 0`.

The route: each `petN` summand is an integral over the `SL(2, ℤ)`-translate
`q.out⁻¹ • 𝒟` (`petN_summand_eq_setIntegral`), the `𝒟`/`𝒟ᵒ` switch is free by the null
boundary, the sum reindexes along the fibers of `slToPslQuot` (each fiber contributing
the same tile integral, by `Γ₁(N)`-invariance of the Petersson integrand), and the
resulting `PSL`-tile sum is exactly the tile decomposition of `gamma1FundDomain N`.

Definiteness needs none of that identification: the `⟦1⟧`-summand of `petN f f` is the
level-one inner product of `f` with itself, every summand is a nonnegative real, so
`petN f f = 0` forces the level-one self-pairing to vanish and
`CuspForm.peterssonInner_definite` applies.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/PeterssonLevelN.lean`), completing the level-`N`
construction milestones of the ModularForms roadmap's Layer 3.
-/

public section

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

open UpperHalfPlane ModularGroup CongruenceSubgroup MeasureTheory Matrix.SpecialLinearGroup

namespace CuspForm

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ## Reindexing `SL(2, ℤ) ⧸ Γ₁(N)` along `PSL(2, ℤ) ⧸ Gamma1PSL N` -/

/-- The natural quotient map `SL(2, ℤ) ⧸ Γ₁(N) → PSL(2, ℤ) ⧸ Gamma1PSL N`, sending each
`Γ₁(N)`-coset `[g]` to the `Gamma1PSL N`-coset of the projective image of `g`. -/
def slToPslQuot : SL(2, ℤ) ⧸ Gamma1 N → PSL(2, ℤ) ⧸ Gamma1PSL N :=
  Quotient.lift
    (fun g : SL(2, ℤ) ↦
      (QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Gamma1PSL N))
    (fun a b hab ↦ by
      refine (QuotientGroup.eq).mpr ?_
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      exact mem_Gamma1PSL_iff.mpr ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, rfl⟩)

@[simp]
theorem slToPslQuot_mk (g : SL(2, ℤ)) :
    slToPslQuot (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) =
      QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) := (rfl)

/-- `slToPslQuot` is surjective. -/
theorem slToPslQuot_surjective : Function.Surjective (slToPslQuot (N := N)) := by
  intro q'
  obtain ⟨g_psl, hg_psl⟩ := QuotientGroup.mk_surjective q'
  obtain ⟨g_sl, hg_sl⟩ := QuotientGroup.mk_surjective g_psl
  exact ⟨QuotientGroup.mk g_sl, by rw [slToPslQuot_mk, hg_sl, hg_psl]⟩

private def slLeftMul (h : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 N → SL(2, ℤ) ⧸ Gamma1 N :=
  Quotient.lift (fun g : SL(2, ℤ) ↦ (QuotientGroup.mk (h * g) : SL(2, ℤ) ⧸ Gamma1 N))
    (fun a b hab ↦ by
      refine QuotientGroup.eq.mpr ?_
      have h_shift : (h * a)⁻¹ * (h * b) = a⁻¹ * b := by group
      rw [h_shift]
      exact QuotientGroup.leftRel_apply.mp hab)

omit [NeZero N] in
@[simp]
private theorem slLeftMul_mk (h g : SL(2, ℤ)) :
    slLeftMul h (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) =
      QuotientGroup.mk (h * g) := (rfl)

omit [NeZero N] in
private theorem slLeftMul_one (q : SL(2, ℤ) ⧸ Gamma1 N) : slLeftMul 1 q = q := by
  induction q using QuotientGroup.induction_on with
  | _ g => simp

omit [NeZero N] in
private theorem slLeftMul_comp (h₁ h₂ : SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    slLeftMul h₁ (slLeftMul h₂ q) = slLeftMul (h₁ * h₂) q := by
  induction q using QuotientGroup.induction_on with
  | _ g => simp [mul_assoc]

private theorem slToPslQuot_slLeftMul (h : SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    slToPslQuot (slLeftMul h q) =
      Quotient.map' (fun x : PSL(2, ℤ) ↦ (QuotientGroup.mk h : PSL(2, ℤ)) * x)
        (fun a b hab ↦ by
          rw [QuotientGroup.leftRel_apply] at hab ⊢
          have h_shift : ((QuotientGroup.mk h : PSL(2, ℤ)) * a)⁻¹ *
              ((QuotientGroup.mk h : PSL(2, ℤ)) * b) = a⁻¹ * b := by group
          rw [h_shift]
          exact hab)
        (slToPslQuot q) := by
  induction q using QuotientGroup.induction_on with
  | _ g =>
    rw [slLeftMul_mk, slToPslQuot_mk, slToPslQuot_mk]
    have h_mul : (QuotientGroup.mk (h * g) : PSL(2, ℤ)) =
        (QuotientGroup.mk h : PSL(2, ℤ)) * (QuotientGroup.mk g : PSL(2, ℤ)) :=
      (QuotientGroup.mk_mul _ _ _)
    rw [h_mul]
    rfl

private theorem slToPslQuot_slLeftMul_eq_of_eq (h : SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Gamma1 N)
    (gs gt : SL(2, ℤ))
    (hq : slToPslQuot q = QuotientGroup.mk (QuotientGroup.mk gs : PSL(2, ℤ)))
    (hh : (QuotientGroup.mk h : PSL(2, ℤ)) =
      QuotientGroup.mk gt * (QuotientGroup.mk gs)⁻¹) :
    slToPslQuot (slLeftMul h q) = QuotientGroup.mk (QuotientGroup.mk gt : PSL(2, ℤ)) := by
  rw [slToPslQuot_slLeftMul h q, hq, Quotient.map'_mk'', hh]
  congr 1
  group

open Classical in
/-- **Uniform fiber size**: any two fibers of `slToPslQuot` have equal cardinality. -/
theorem slToPslQuot_fiber_card_uniform (q₁' q₂' : PSL(2, ℤ) ⧸ Gamma1PSL N) :
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ slToPslQuot q = q₁')).card =
      (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ slToPslQuot q = q₂')).card := by
  obtain ⟨q₁, hq₁⟩ := slToPslQuot_surjective q₁'
  obtain ⟨q₂, hq₂⟩ := slToPslQuot_surjective q₂'
  induction q₁ using QuotientGroup.induction_on with | _ g₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | _ g₂ => ?_
  set h := g₂ * g₁⁻¹ with hh_def
  refine Finset.card_bij'
    (fun q _ ↦ slLeftMul h q)
    (fun q _ ↦ slLeftMul h⁻¹ q)
    (fun q hq ↦ ?_)
    (fun q hq ↦ ?_)
    (fun q _ ↦ by rw [slLeftMul_comp, inv_mul_cancel, slLeftMul_one])
    (fun q _ ↦ by rw [slLeftMul_comp, mul_inv_cancel, slLeftMul_one])
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    have hq₂' : q₂' = QuotientGroup.mk (QuotientGroup.mk g₂ : PSL(2, ℤ)) := by
      rw [← slToPslQuot_mk]
      exact hq₂.symm
    rw [hq₂']
    refine slToPslQuot_slLeftMul_eq_of_eq h q g₁ g₂ ?_ ?_
    · rw [hq, ← slToPslQuot_mk]
      exact hq₁.symm
    · rw [hh_def, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    have hq₁' : q₁' = QuotientGroup.mk (QuotientGroup.mk g₁ : PSL(2, ℤ)) := by
      rw [← slToPslQuot_mk]
      exact hq₁.symm
    rw [hq₁']
    refine slToPslQuot_slLeftMul_eq_of_eq h⁻¹ q g₂ g₁ ?_ ?_
    · rw [hq, ← slToPslQuot_mk]
      exact hq₂.symm
    · rw [hh_def, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      group

/-! ## Tile integrals -/

private lemma psl_smul_set_eq_sl (g : SL(2, ℤ)) (S : Set ℍ) :
    ((QuotientGroup.mk g : PSL(2, ℤ))) • S = (g : SL(2, ℤ)) • S := by
  ext τ
  simp only [Set.mem_smul_set, PSL_smul_coe]

private lemma psl_inv_smul_set_eq_sl (g : SL(2, ℤ)) (S : Set ℍ) :
    ((QuotientGroup.mk g : PSL(2, ℤ)))⁻¹ • S = (g : SL(2, ℤ))⁻¹ • S := by
  rw [← QuotientGroup.mk_inv, psl_smul_set_eq_sl g⁻¹ S]

/-- The integral over an `SL₂(ℤ)`-translate `δ • S` reduces to an integral over `S`:
`∫_{δ • S} h = ∫_S h (δ • ·)`. -/
theorem setIntegral_smul_eq (h : ℍ → ℂ) (δ : SL(2, ℤ)) (S : Set ℍ) :
    ∫ τ in δ • S, h τ = ∫ τ in S, h (δ • τ) := by
  rw [← Set.image_smul,
    (measurePreserving_smul δ (volume : Measure ℍ)).setIntegral_image_emb
      (measurableEmbedding_const_smul δ)]

omit [NeZero N] in
/-- The Petersson integrand of two `Γ₁(N)`-cusp forms is `Γ₁(N)`-invariant. -/
theorem petersson_Gamma1_invariant (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) (τ : ℍ) :
    petersson k ⇑f ⇑g (γ • τ) = petersson k ⇑f ⇑g τ := by
  rw [← petersson_slash_SL, slash_Gamma1_eq f γ hγ, slash_Gamma1_eq g γ hγ]

omit [NeZero N] in
/-- Each `petN` summand equals an integral over a translate of `𝒟`:
`UpperHalfPlane.peterssonInner k fd (f∣q⁻¹) (g∣q⁻¹) = ∫ τ in q.out⁻¹ • 𝒟, petersson k f g τ`. -/
theorem petN_summand_eq_setIntegral
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹) =
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), petersson k ⇑f ⇑g τ := by
  simp only [UpperHalfPlane.peterssonInner_def, petersson_slash_SL]
  rw [setIntegral_smul_eq]

omit [NeZero N] in
/-- For `Γ₁(N)`-invariant integrands, integrals over `η • S` and `S` agree
([DS] Lemma 5.5.1). -/
theorem setIntegral_Gamma1_smul_eq (h : ℍ → ℂ) (η : SL(2, ℤ)) (_hη : η ∈ Gamma1 N)
    (h_inv : ∀ τ, h (η • τ) = h τ) (S : Set ℍ) :
    ∫ τ in η • S, h τ = ∫ τ in S, h τ := by
  rw [setIntegral_smul_eq h η S]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ h_inv τ)

-- Fiber-invariance of the tile integral: for a `Γ₁(N)`-invariant integrand, the `SL`-tile
-- integral equals the corresponding `PSL`-tile integral (the discrepancy acts by an actual
-- element of `Γ₁(N)`, extracted through `mem_Gamma1PSL_iff`).
private theorem setIntegral_sl_tile_eq_psl_tile (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, h (γ • τ) = h τ) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ =
      ∫ τ in ((slToPslQuot q).out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ := by
  have h_quot_eq : (QuotientGroup.mk (QuotientGroup.mk q.out : PSL(2, ℤ)) :
      PSL(2, ℤ) ⧸ Gamma1PSL N) = QuotientGroup.mk ((slToPslQuot q).out : PSL(2, ℤ)) := by
    have h1 : slToPslQuot q =
        QuotientGroup.mk (QuotientGroup.mk q.out : PSL(2, ℤ)) := by
      conv_lhs => rw [← q.out_eq]
      exact slToPslQuot_mk q.out
    exact h1.symm.trans (slToPslQuot q).out_eq.symm
  rw [QuotientGroup.eq] at h_quot_eq
  obtain ⟨γ, hγ_mem, hγ_eq⟩ := mem_Gamma1PSL_iff.mp h_quot_eq
  have h_eq_psl : ((slToPslQuot q).out : PSL(2, ℤ)) =
      QuotientGroup.mk q.out * QuotientGroup.mk γ := by
    have h_mul : (QuotientGroup.mk q.out : PSL(2, ℤ)) *
        ((QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹ * (slToPslQuot q).out) =
        (slToPslQuot q).out := by group
    rw [← h_mul, ← hγ_eq]
  have h_tile : ((slToPslQuot q).out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ) =
      (QuotientGroup.mk γ : PSL(2, ℤ))⁻¹ •
        ((QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ)) := by
    rw [h_eq_psl, mul_inv_rev, mul_smul]
  rw [h_tile, psl_inv_smul_set_eq_sl q.out fdo, psl_inv_smul_set_eq_sl γ _]
  symm
  rw [setIntegral_smul_eq]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ h_inv γ⁻¹ ((Gamma1 N).inv_mem hγ_mem) τ)

open Classical in
-- `SL`→`PSL` fiber-sum reindexing for `Γ₁(N)`-invariant integrands, weighted by
-- fiber cardinalities.
private theorem sum_sl_tile_eq_fiberwise_psl_tile (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, h (γ • τ) = h τ) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ =
      ∑ q' : PSL(2, ℤ) ⧸ Gamma1PSL N,
        (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ slToPslQuot q = q')).card •
          ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ := by
  calc ∑ q : SL(2, ℤ) ⧸ Gamma1 N, ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ
      = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in ((slToPslQuot q).out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_sl_tile_eq_psl_tile h h_inv q
    _ = ∑ q' : PSL(2, ℤ) ⧸ Gamma1PSL N,
          ∑ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ slToPslQuot q = q'),
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ :=
        (Finset.sum_fiberwise' Finset.univ (slToPslQuot (N := N))
          (fun q' ↦ ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ)).symm
    _ = ∑ q' : PSL(2, ℤ) ⧸ Gamma1PSL N,
          (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ slToPslQuot q = q')).card •
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ :=
        Finset.sum_congr rfl fun q' _ ↦ Finset.sum_const _

omit [NeZero N] in
private theorem setIntegral_sl_tile_fd_eq_fdo (h : ℍ → ℂ) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ =
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ := by
  rw [setIntegral_smul_eq, setIntegral_smul_eq, setIntegral_fd_eq_fdo]

/-! ## `petN` as an integral over the `Γ₁(N)`-fundamental domain -/

open Classical in
/-- `petN` as the fiber-weighted sum of `PSL`-tile integrals. -/
theorem petN_eq_weighted_sum_setIntegral_psl_tile
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f g =
      ∑ q' : PSL(2, ℤ) ⧸ Gamma1PSL N,
        (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ slToPslQuot q = q')).card •
          ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), petersson k ⇑f ⇑g τ := by
  calc petN f g
      = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), petersson k ⇑f ⇑g τ := by
        rw [petN_def]
        exact Finset.sum_congr rfl fun q _ ↦ petN_summand_eq_setIntegral f g q
    _ = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), petersson k ⇑f ⇑g τ :=
        Finset.sum_congr rfl fun q _ ↦
          setIntegral_sl_tile_fd_eq_fdo (petersson k ⇑f ⇑g) q
    _ = _ :=
        sum_sl_tile_eq_fiberwise_psl_tile (petersson k ⇑f ⇑g)
          (fun γ hγ τ ↦ petersson_Gamma1_invariant f g γ hγ τ)

open Classical in
/-- The uniform fiber cardinality of `slToPslQuot`, computed at the identity coset. -/
def slToPslQuotFiberCard (N : ℕ) [NeZero N] : ℕ :=
  (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
    slToPslQuot q = (QuotientGroup.mk (1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Gamma1PSL N))).card

open Classical in
/-- Every fiber of `slToPslQuot` has cardinality `slToPslQuotFiberCard N`. -/
theorem slToPslQuot_fiberCard_eq (q' : PSL(2, ℤ) ⧸ Gamma1PSL N) :
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ slToPslQuot q = q')).card =
      slToPslQuotFiberCard N := by
  rw [slToPslQuotFiberCard]
  convert slToPslQuot_fiber_card_uniform q' _ using 2

open Classical in
/-- **`petN` as a single integral over the `Γ₁(N)`-fundamental domain**:
`petN f g = c_N • ∫ τ in gamma1FundDomain N, petersson k f g τ`, with
`c_N = slToPslQuotFiberCard N` the uniform fiber count of the `SL`→`PSL` reindexing. -/
theorem petN_eq_setIntegral_gamma1FundDomain
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f g = (slToPslQuotFiberCard N) •
      ∫ τ in gamma1FundDomain N, petersson k ⇑f ⇑g τ := by
  rw [petN_eq_weighted_sum_setIntegral_psl_tile f g,
    setIntegral_gamma1FundDomain_eq_sum _ (integrableOn_petersson_gamma1FundDomain f g),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun q' _ ↦ ?_
  congr 1
  convert slToPslQuot_fiberCard_eq q' using 2

/-! ## Positive definiteness -/

omit [NeZero N] in
private theorem petersson_self_ofReal (h : ℍ → ℂ) (τ : ℍ) :
    petersson k h h τ = ↑(Complex.normSq (h τ) * τ.im ^ k) := by
  simp only [petersson, ← Complex.normSq_eq_conj_mul_self]
  push_cast
  ring

omit [NeZero N] in
private theorem peterssonInner_self_real (h : ℍ → ℂ) :
    UpperHalfPlane.peterssonInner k fd h h = ↑(∫ τ in fd, Complex.normSq (h τ) * τ.im ^ k) := by
  rw [UpperHalfPlane.peterssonInner_def]
  simp_rw [petersson_self_ofReal]
  exact integral_ofReal

omit [NeZero N] in
/-- Each summand of `petN f f` is a nonnegative real number. -/
theorem petN_summand_nonneg (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ∃ r : ℝ, 0 ≤ r ∧
      UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑f ∣[k] (q.out)⁻¹) = ↑r := by
  set h := ⇑f ∣[k] (q.out)⁻¹
  exact ⟨∫ τ in fd, Complex.normSq (h τ) * τ.im ^ k,
    setIntegral_nonneg isClosed_fd.measurableSet fun τ _ ↦
      mul_nonneg (Complex.normSq_nonneg _) (zpow_nonneg τ.im_pos.le _),
    peterssonInner_self_real h⟩

omit [NeZero N] in
private theorem out_one_mem_Gamma1 :
    ((⟦1⟧ : SL(2, ℤ) ⧸ Gamma1 N)).out ∈ Gamma1 N := by
  have h := Quotient.exact ((⟦1⟧ : SL(2, ℤ) ⧸ Gamma1 N).out_eq)
  have h' := QuotientGroup.leftRel_apply.mp h
  simpa using h'

omit [NeZero N] in
private theorem identity_coset_eq_peterssonInner (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    UpperHalfPlane.peterssonInner k fd
      (⇑f ∣[k] ((⟦(1 : SL(2, ℤ))⟧ : SL(2, ℤ) ⧸ Gamma1 N)).out⁻¹)
      (⇑g ∣[k] ((⟦(1 : SL(2, ℤ))⟧ : SL(2, ℤ) ⧸ Gamma1 N)).out⁻¹) =
    CuspForm.peterssonInner f g := by
  have hmem := (Gamma1 N).inv_mem out_one_mem_Gamma1
  rw [slash_Gamma1_eq f _ hmem, slash_Gamma1_eq g _ hmem, CuspForm.peterssonInner_def]

/-- **Positive definiteness of the level-`N` Petersson pairing**: `petN f f = 0` forces
`f = 0`. Every summand is a nonnegative real, so all vanish; the `⟦1⟧`-summand is
the level-one inner product of `f` with itself, and
`CuspForm.peterssonInner_definite` concludes. -/
theorem petN_definite (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hpet : petN f f = 0) : f = 0 := by
  apply CuspForm.peterssonInner_definite f
  rw [← identity_coset_eq_peterssonInner f f]
  choose r hr_nonneg hr_eq using petN_summand_nonneg f
  have hsum : (↑(∑ q, r q) : ℂ) = 0 := by
    rw [Complex.ofReal_sum]
    simp_rw [← hr_eq]
    rw [← petN_def]
    exact hpet
  rw [hr_eq ⟦1⟧,
    (Finset.sum_eq_zero_iff_of_nonneg fun q _ ↦ hr_nonneg q).mp
      (Complex.ofReal_eq_zero.mp hsum) ⟦1⟧ (Finset.mem_univ _),
    Complex.ofReal_zero]

end CuspForm
