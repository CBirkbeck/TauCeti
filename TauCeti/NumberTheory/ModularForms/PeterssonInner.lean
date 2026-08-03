/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.NumberTheory.ModularForms.Petersson
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Petersson inner product

The **Petersson inner product**
$$\langle f, g \rangle = \int_D \overline{f(\tau)} \, g(\tau) \, (\operatorname{Im}\tau)^k
\, d\mu(\tau)$$
of two functions on the upper half-plane, integrated over a fundamental domain `D` against
Mathlib's invariant measure `volume : Measure ℍ` (`dx dy / y²`,
`Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`), with the integrand
`petersson k f g` from `Mathlib/NumberTheory/ModularForms/Petersson.lean`.

## Main definitions

* `UpperHalfPlane.peterssonInner`: the Petersson inner product, parameterized by weight `k`
  and fundamental domain `D`.
* `CuspForm.pet`: the inner product of two cusp forms over the standard fundamental domain.

## Main results

* `ModularGroup.volume_fd_lt_top`: the standard fundamental domain has finite invariant
  measure.
* `UpperHalfPlane.peterssonInner_conj_symm`: Hermitian symmetry.
* `UpperHalfPlane.peterssonInner_integrableOn_left`: integrability of the Petersson integrand of a
  cusp form against a modular form over the standard fundamental domain.
* `ModularGroup.volume_frontier_fd`, `ModularGroup.setIntegral_fd_eq_fdo`: the frontier of
  the fundamental domain is null, so integrals over `𝒟` and `𝒟ᵒ` agree.
* `UpperHalfPlane.eq_zero_on_fd_of_peterssonInner_self_eq_zero`: definiteness on the
  fundamental domain.

The inner product is parameterized by a fundamental domain `D : Set ℍ` rather than fixing a
subgroup; for `SL₂(ℤ)` use `D = ModularGroup.fd`, and for a congruence subgroup of index `n` a
union of `n` translates. The topology of `𝒟`/`𝒟ᵒ` (`ModularGroup.isClosed_fd`,
`ModularGroup.isOpen_fdo`, `ModularGroup.fd_eq_closure_fdo`) comes from
`Mathlib/NumberTheory/Modular.lean`; this file adds their measure theory.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.4
* Miyake, *Modular forms*, §2.5
-/

public section

noncomputable section

open MeasureTheory Measure UpperHalfPlane ModularGroup Complex Set ENNReal

open scoped ComplexConjugate MatrixGroups NNReal Pointwise

namespace UpperHalfPlane

/-- Mathlib's invariant measure on `ℍ`, respelled with the density `(Im τ)⁻²` in
`ENNReal.ofReal` form. -/
theorem volume_eq_withDensity_ofReal :
    (volume : Measure ℍ) = (Measure.comap UpperHalfPlane.coe volume).withDensity
      (fun τ ↦ ENNReal.ofReal (τ.im ^ (-2 : ℤ))) := by
  rw [volume_def]
  congr 1
  funext τ
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast [NNReal.coe_mk]
  rw [one_div, inv_pow, zpow_neg]
  norm_num

/-- The pullback of the Lebesgue measure along `ℍ ↪ ℂ` is positive on nonempty open sets. -/
instance : IsOpenPosMeasure (Measure.comap UpperHalfPlane.coe (volume : Measure ℂ)) :=
  IsOpenPosMeasure.comap volume isOpenEmbedding_coe

/-- The invariant measure is absolutely continuous w.r.t. the pullback of the Lebesgue
measure along `ℍ ↪ ℂ`. -/
theorem volume_absolutelyContinuous_comap :
    (volume : Measure ℍ) ≪ Measure.comap UpperHalfPlane.coe volume := by
  rw [volume_eq_withDensity_ofReal]
  exact withDensity_absolutelyContinuous _ _

/-- The pullback of the Lebesgue measure along `ℍ ↪ ℂ` is absolutely continuous w.r.t. the
invariant measure, since the density `(Im τ)⁻²` is everywhere positive on `ℍ`. -/
theorem comap_absolutelyContinuous_volume :
    Measure.comap UpperHalfPlane.coe (volume : Measure ℂ) ≪ (volume : Measure ℍ) := by
  rw [volume_eq_withDensity_ofReal]
  exact withDensity_absolutelyContinuous'
    ((continuous_im.zpow₀ _ fun τ ↦ Or.inl τ.im_pos.ne').measurable.ennreal_ofReal.aemeasurable)
    (ae_of_all _ fun τ ↦ by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact zpow_pos τ.im_pos _)

/-- The invariant measure gives positive mass to nonempty open sets. -/
instance : IsOpenPosMeasure (volume : Measure ℍ) :=
  comap_absolutelyContinuous_volume.isOpenPosMeasure

/-- If a subset of `ℂ` has zero Lebesgue measure, its preimage in `ℍ` has zero invariant
measure. -/
theorem volume_preimage_coe_null {S : Set ℂ} (hS : volume S = 0) :
    (volume : Measure ℍ) (UpperHalfPlane.coe ⁻¹' S) = 0 := by
  refine volume_absolutelyContinuous_comap ?_
  rw [isOpenEmbedding_coe.measurableEmbedding.comap_apply]
  exact measure_mono_null (image_preimage_subset _ _) hS

end UpperHalfPlane

namespace ModularGroup

private theorem integrableOn_zpow_neg_two_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (· ^ (-2 : ℤ)) (Ioi c) (volume : Measure ℝ) := by
  have h := integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hc
  rwa [show (· ^ (-2 : ℝ) : ℝ → ℝ) = (· ^ (-2 : ℤ)) from funext fun _ ↦ by
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_cast, Real.rpow_intCast]] at h

private theorem strip_lintegral_lt_top {c : ℝ} (hc : 0 < c) :
    ∫⁻ p in Icc (-1/2 : ℝ) (1/2) ×ˢ Ioi c,
      ENNReal.ofReal (p.2 ^ (-2 : ℤ)) ∂(volume : Measure (ℝ × ℝ)) < ⊤ := by
  rw [volume_eq_prod ℝ ℝ, setLIntegral_prod_symm _ (by fun_prop)]
  simp_rw [setLIntegral_const]
  calc ∫⁻ y in Ioi c, ENNReal.ofReal (y ^ (-2 : ℤ)) *
        volume (Icc (-1/2 : ℝ) (1/2)) ∂volume
      ≤ ∫⁻ y in Ioi c, ENNReal.ofReal (y ^ (-2 : ℤ)) * 1 ∂volume := by
        gcongr with y; rw [Real.volume_Icc]; norm_num
    _ = _ := by simp
    _ < ⊤ := lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi
        fun y _ ↦ Real.ofReal_le_enorm _)
        (integrableOn_zpow_neg_two_Ioi hc).hasFiniteIntegral

private theorem setLIntegral_im_eq_prod (g : ℝ → ENNReal) (T : Set (ℝ × ℝ)) :
    ∫⁻ z in equivRealProd ⁻¹' T, g z.im ∂(volume : Measure ℂ) =
      ∫⁻ p in T, g p.2 ∂(volume : Measure (ℝ × ℝ)) := by
  rw [show (⇑equivRealProd : ℂ → ℝ × ℝ) = ⇑measurableEquivRealProd from rfl]
  have h := volume_preserving_equiv_real_prod.setLIntegral_comp_emb
      measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ ↦ g p.2)
      (measurableEquivRealProd ⁻¹' T)
  rw [MeasurableEquiv.image_preimage] at h
  simpa only [measurableEquivRealProd_apply] using h

/-- The invariant measure of the standard fundamental domain is finite. -/
theorem volume_fd_lt_top : (volume : Measure ℍ) fd < ⊤ := by
  rw [volume_eq_lintegral]
  set T := Icc (-1/2 : ℝ) (1/2) ×ˢ Ioi (Real.sqrt 3 / 4)
  calc ∫⁻ z in UpperHalfPlane.coe '' fd, ↑((1 / ‖z.im‖₊) ^ 2 : ℝ≥0)
      = ∫⁻ z in UpperHalfPlane.coe '' fd, ENNReal.ofReal (z.im ^ (-2 : ℤ)) := by
        refine setLIntegral_congr_fun
          (isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr
            isClosed_fd.measurableSet) fun z hz ↦ ?_
        obtain ⟨τ, -, rfl⟩ := hz
        rw [← ENNReal.ofReal_coe_nnreal]
        congr 1
        push_cast [Real.nnnorm_of_nonneg τ.im_pos.le]
        rw [one_div, inv_pow, zpow_neg]
        norm_num
    _ ≤ ∫⁻ z in equivRealProd ⁻¹' T, ENNReal.ofReal (z.im ^ (-2 : ℤ)) :=
        lintegral_mono_set fun z ↦ by
          rintro ⟨τ, hτ, rfl⟩
          simp only [mem_preimage, equivRealProd_apply, coe_re, coe_im]
          refine ⟨⟨by linarith [(abs_le.mp hτ.2).1], (abs_le.mp hτ.2).2⟩,
            mem_Ioi.mpr ?_⟩
          have h := three_le_four_mul_im_sq_of_mem_fd hτ
          rw [show (4 : ℝ) * τ.im ^ 2 = (2 * τ.im) ^ 2 from by ring] at h
          have h2 := Real.sqrt_le_sqrt h
          rw [Real.sqrt_sq (by linarith [τ.im_pos])] at h2
          nlinarith [Real.sqrt_pos_of_pos (show (3 : ℝ) > 0 by norm_num)]
    _ = ∫⁻ p in T, ENNReal.ofReal (p.2 ^ (-2 : ℤ)) ∂volume :=
        setLIntegral_im_eq_prod (fun y ↦ ENNReal.ofReal (y ^ (-2 : ℤ))) T
    _ < ⊤ := strip_lintegral_lt_top (by positivity)

private theorem volume_complex_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  rw [show {z : ℂ | z.re = c} = measurableEquivRealProd ⁻¹' ({c} ×ˢ univ) from by
    ext z; simp [measurableEquivRealProd]]
  rw [volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet,
    volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

private theorem volume_complex_normSq_eq (c : ℝ) :
    volume {z : ℂ | Complex.normSq z = c} = 0 := by
  rcases le_or_gt 0 c with hc | hc
  · rw [show {z : ℂ | Complex.normSq z = c} = Metric.sphere (0 : ℂ) (Real.sqrt c) from by
      ext z
      simp only [mem_ofPred_eq, Complex.normSq_eq_norm_sq, mem_sphere_zero_iff_norm]
      constructor
      · intro h
        rw [← h, Real.sqrt_sq (norm_nonneg z)]
      · intro h
        rw [h, Real.sq_sqrt hc]]
    exact Measure.addHaar_sphere volume 0 _
  · rw [show {z : ℂ | Complex.normSq z = c} = ∅ from eq_empty_iff_forall_notMem.mpr
      fun z hz ↦ not_le.mpr hc (hz ▸ Complex.normSq_nonneg z)]
    exact measure_empty

/-- **The frontier of the standard fundamental domain has zero invariant measure.**

`frontier 𝒟 = 𝒟 \ 𝒟ᵒ ⊆ {normSq = 1} ∪ {Re = 1/2} ∪ {Re = −1/2}`, each of which has
zero Lebesgue measure in `ℂ`. -/
theorem volume_frontier_fd : (volume : Measure ℍ) (frontier (fd : Set ℍ)) = 0 := by
  rw [frontier, isClosed_fd.closure_eq, ← fdo_eq_interior_fd]
  apply measure_mono_null _ (volume_preimage_coe_null
    (measure_union_null
      (measure_union_null (volume_complex_normSq_eq 1) (volume_complex_re_eq (1/2)))
      (volume_complex_re_eq (-1/2))))
  intro τ ⟨hfd, hfdo⟩
  simp only [fd, fdo, mem_ofPred_eq, not_and, not_lt] at hfd hfdo
  obtain ⟨h1, h2⟩ := hfd
  simp only [mem_preimage, mem_union, mem_ofPred_eq]
  by_cases h : Complex.normSq (τ : ℂ) = 1
  · left; left; exact h
  · have hns : 1 < Complex.normSq (τ : ℂ) := lt_of_le_of_ne h1 (Ne.symm h)
    have habs : |τ.re| = 1 / 2 := le_antisymm h2 (hfdo hns)
    by_cases hre : 0 ≤ τ.re
    · left; right; rw [coe_re]; rwa [abs_of_nonneg hre] at habs
    · push Not at hre; right
      rw [coe_re]; rw [abs_of_neg hre] at habs; linarith

/-- `fd` and `fdo` are a.e. equal w.r.t. the invariant measure. -/
theorem fd_ae_eq_fdo : (fd : Set ℍ) =ᶠ[ae (volume : Measure ℍ)] fdo :=
  ((fdo_eq_interior_fd.symm ▸ interior_ae_eq_of_null_frontier volume_frontier_fd :
    (fdo : Set ℍ) =ᶠ[ae (volume : Measure ℍ)] fd)).symm

/-- Integrals over `fd` and `fdo` agree against the invariant measure. -/
theorem setIntegral_fd_eq_fdo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℍ → E) : ∫ τ in fd, f τ = ∫ τ in fdo, f τ :=
  setIntegral_congr_set fd_ae_eq_fdo

end ModularGroup

namespace UpperHalfPlane

/-- The Petersson inner product of two functions `f, g : ℍ → ℂ` of weight `k`,
integrated over a fundamental domain `D` with respect to the invariant measure.

The integrand is `conj(f(τ)) · g(τ) · (Im τ)^k`, which equals
`petersson k f g τ` from `Mathlib.NumberTheory.ModularForms.Petersson`. -/
def peterssonInner (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) : ℂ :=
  ∫ τ in D, petersson k f g τ

/-- Hermitian symmetry: `conj ⟨g, f⟩ = ⟨f, g⟩`. -/
theorem peterssonInner_conj_symm (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    conj (peterssonInner k D g f) = peterssonInner k D f g := by
  simp only [peterssonInner, ← integral_conj, petersson_symm k g f]

/-- The pairing with zero on the right vanishes. -/
theorem peterssonInner_zero_right (k : ℤ) (D : Set ℍ) (f : ℍ → ℂ) :
    peterssonInner k D f 0 = 0 := by
  simp [peterssonInner, petersson]

/-- The pairing with zero on the left vanishes. -/
theorem peterssonInner_zero_left (k : ℤ) (D : Set ℍ) (g : ℍ → ℂ) :
    peterssonInner k D 0 g = 0 := by
  simp [peterssonInner, petersson]

/-- Negation in the right argument. -/
theorem peterssonInner_neg_right (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    peterssonInner k D f (-g) = -peterssonInner k D f g := by
  simp only [peterssonInner, petersson, Pi.neg_apply, mul_neg, neg_mul, integral_neg]

/-- Negation in the left argument. -/
theorem peterssonInner_neg_left (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    peterssonInner k D (-f) g = -peterssonInner k D f g := by
  simp only [peterssonInner, petersson, Pi.neg_apply, map_neg, neg_mul, integral_neg]

/-- The Petersson integrand of a cusp form against a modular form is integrable over the
standard fundamental domain. -/
theorem peterssonInner_integrableOn_left {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    [CuspFormClass F Γ k] [ModularFormClass F' Γ k]
    (f : F) (f' : F') :
    IntegrableOn (fun τ ↦ petersson k f f' τ) fd (volume : Measure ℍ) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ f f'
  exact IntegrableOn.of_bound ModularGroup.volume_fd_lt_top
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f')).aestronglyMeasurable.restrict) C
    (ae_of_all _ fun τ ↦ hC τ)

/-- The Petersson integrand of a modular form against a cusp form is integrable over the
standard fundamental domain. -/
theorem peterssonInner_integrableOn_right {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    [ModularFormClass F Γ k] [CuspFormClass F' Γ k]
    (f : F) (f' : F') :
    IntegrableOn (fun τ ↦ petersson k f f' τ) fd (volume : Measure ℍ) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_right k Γ f f'
  exact IntegrableOn.of_bound ModularGroup.volume_fd_lt_top
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f')).aestronglyMeasurable.restrict) C
    (ae_of_all _ fun τ ↦ hC τ)

/-- Additivity in the second argument. -/
theorem peterssonInner_add_right (k : ℤ) (D : Set ℍ) (f g₁ g₂ : ℍ → ℂ)
    (hg₁ : IntegrableOn (fun τ ↦ petersson k f g₁ τ) D (volume : Measure ℍ))
    (hg₂ : IntegrableOn (fun τ ↦ petersson k f g₂ τ) D (volume : Measure ℍ)) :
    peterssonInner k D f (g₁ + g₂) = peterssonInner k D f g₁ + peterssonInner k D f g₂ := by
  rw [show peterssonInner k D f (g₁ + g₂) =
      ∫ τ in D, (petersson k f g₁ τ + petersson k f g₂ τ) from by
    simp only [peterssonInner, petersson, Pi.add_apply]; congr 1; ext τ; ring]
  exact integral_add hg₁ hg₂

/-- Additivity in the first argument, given integrability of both summands. -/
theorem peterssonInner_add_left (k : ℤ) (D : Set ℍ) (f₁ f₂ g : ℍ → ℂ)
    (hf₁ : IntegrableOn (fun τ ↦ petersson k f₁ g τ) D (volume : Measure ℍ))
    (hf₂ : IntegrableOn (fun τ ↦ petersson k f₂ g τ) D (volume : Measure ℍ)) :
    peterssonInner k D (f₁ + f₂) g = peterssonInner k D f₁ g + peterssonInner k D f₂ g := by
  rw [show peterssonInner k D (f₁ + f₂) g =
      ∫ τ in D, (petersson k f₁ g τ + petersson k f₂ g τ) from by
    simp only [peterssonInner, petersson, Pi.add_apply, map_add]; congr 1; ext τ; ring]
  exact integral_add hf₁ hf₂

/-- Scalar multiplication in the second argument. -/
theorem peterssonInner_smul_right (k : ℤ) (D : Set ℍ) (c : ℂ) (f g : ℍ → ℂ) :
    peterssonInner k D f (c • g) = c * peterssonInner k D f g := by
  rw [show peterssonInner k D f (c • g) = ∫ τ in D, c * petersson k f g τ from by
    simp only [peterssonInner, petersson, Pi.smul_apply, smul_eq_mul]
    congr 1; ext τ; ring]
  exact integral_const_mul c _

/-- Conjugate-scalar multiplication in the left argument. -/
theorem peterssonInner_conj_smul_left (k : ℤ) (D : Set ℍ) (c : ℂ) (f g : ℍ → ℂ) :
    peterssonInner k D (c • f) g = conj c * peterssonInner k D f g := by
  rw [show peterssonInner k D (c • f) g = ∫ τ in D, conj c * petersson k f g τ from by
    simp only [peterssonInner, petersson, Pi.smul_apply, smul_eq_mul, map_mul]
    congr 1; ext τ; ring]
  exact integral_const_mul (conj c) _

private lemma petersson_self_re_eq (z : ℂ) (y : ℝ) (k : ℤ) :
    (starRingEnd ℂ z * z * (↑y : ℂ) ^ k).re = Complex.normSq z * y ^ k := by
  rw [show starRingEnd ℂ z * z = ↑(Complex.normSq z) from Complex.normSq_eq_conj_mul_self.symm,
    ← Complex.ofReal_zpow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Definiteness of the Petersson pairing on the fundamental domain**: a cusp form whose
Petersson self-pairing over `𝒟` vanishes is zero everywhere on `𝒟`.

The nonnegative continuous integrand `normSq (f τ) · (Im τ)^k` is a.e. zero, hence zero on
the open domain `𝒟ᵒ`, hence zero on `𝒟 = closure 𝒟ᵒ` by continuity. -/
theorem eq_zero_on_fd_of_peterssonInner_self_eq_zero {F : Type*} [FunLike F ℍ ℂ]
    {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    [CuspFormClass F Γ k]
    (f : F) (hpet : peterssonInner k fd (fun τ ↦ f τ) (fun τ ↦ f τ) = 0)
    {τ : ℍ} (hτ : τ ∈ fd) : f τ = 0 := by
  set g : ℍ → ℝ := fun z ↦ (petersson k (⇑f) (⇑f) z).re
  have hint := peterssonInner_integrableOn_left k Γ f f
  have hg_zero : ∫ z in fd, g z = 0 := by
    trans RCLike.re (∫ z in fd, petersson k (⇑f) (⇑f) z)
    · exact integral_re hint
    · simp only [peterssonInner] at hpet; rw [hpet]; simp
  have hg_ae : g =ᶠ[ae ((volume : Measure ℍ).restrict fd)] 0 := by
    rwa [← integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ fun z ↦ show 0 ≤ g z from by
        simp only [g, petersson]
        exact (petersson_self_re_eq (f z) z.im k).symm ▸
          mul_nonneg (Complex.normSq_nonneg _) (zpow_nonneg z.im_pos.le _)) hint.re]
  have hg_cont : Continuous g :=
    Complex.continuous_re.comp (petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f))
  have hg_fdo : EqOn g 0 fdo :=
    Measure.eqOn_open_of_ae_eq
      (hg_ae.filter_mono (ae_mono (restrict_mono fdo_subset_fd le_rfl)))
      isOpen_fdo hg_cont.continuousOn continuousOn_const
  have hgτ : g τ = 0 :=
    (EqOn.of_subset_closure hg_fdo hg_cont.continuousOn continuousOn_const
      fdo_subset_fd fd_eq_closure_fdo.subset) hτ
  simp only [g, petersson] at hgτ
  rw [petersson_self_re_eq] at hgτ
  exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hgτ).elim id
    (fun h ↦ absurd h (ne_of_gt (zpow_pos τ.im_pos k))))

end UpperHalfPlane

namespace CuspForm

open UpperHalfPlane

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- The Petersson pairing of two cusp forms, integrated over the standard fundamental
domain `𝒟` for `SL₂(ℤ)`.

This is the level-one-domain pairing, **not** the `Γ \ ℍ`-normalized Petersson inner
product: for `Γ ≤ SL₂(ℤ)` of index `n`, the latter integrates over `n` translates of `𝒟`.
The two differ by that positive factor, so `pet` is nonetheless Hermitian-sesquilinear and
positive definite for cusp forms of any arithmetic level (`CuspForm.pet_definite`). -/
def pet (f g : CuspForm Γ k) : ℂ :=
  peterssonInner k ModularGroup.fd f g

@[simp]
theorem pet_def (f g : CuspForm Γ k) : pet f g = peterssonInner k ModularGroup.fd f g := (rfl)

end CuspForm
