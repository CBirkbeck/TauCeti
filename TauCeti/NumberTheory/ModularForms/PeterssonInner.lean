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
of two functions on the upper half-plane, integrated over a set `D` — in applications a
fundamental domain — against
Mathlib's invariant measure `volume : Measure ℍ` (`dx dy / y²`,
`Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`), with the integrand
`petersson k f g` from `Mathlib/NumberTheory/ModularForms/Petersson.lean`.

## Main definitions

* `UpperHalfPlane.peterssonInner`: the Petersson pairing — the set integral of the
  Petersson integrand over an arbitrary `D : Set ℍ`; it is an inner product only once a
  domain and integrability are supplied.
* `CuspForm.peterssonInnerFd`: the level-one-domain pairing of two cusp forms (over `𝒟`,
  whatever the level).

## Main results

* `ModularGroup.volume_fd_lt_top`: the standard fundamental domain has finite invariant
  measure.
* `UpperHalfPlane.peterssonInner_conj_symm`: Hermitian symmetry.
* `UpperHalfPlane.integrableOn_petersson_fd_left`: integrability of the Petersson integrand of a
  cusp form against a modular form over the standard fundamental domain.
* `ModularGroup.volume_frontier_fd`, `ModularGroup.setIntegral_fd_eq_fdo`: the frontier of
  the fundamental domain is null, so integrals over `𝒟` and `𝒟ᵒ` agree.
* `UpperHalfPlane.eq_zero_on_fd_of_peterssonInner_self_eq_zero`: definiteness on the
  fundamental domain.

The pairing is parameterized by an arbitrary `D : Set ℍ` rather than fixing a subgroup;
for `SL₂(ℤ)` use `D = ModularGroup.fd`, and for a congruence subgroup a union of
translates of `𝒟`. The topology of `𝒟`/`𝒟ᵒ` (`ModularGroup.isClosed_fd`,
`ModularGroup.isOpen_fdo`, `ModularGroup.fd_eq_closure_fdo`) comes from
`Mathlib/NumberTheory/Modular.lean`; this file adds their measure theory.

Ported from the AINTLIB `LeanModularForms` project's
`LeanModularForms/Modularforms/PeterssonInnerProduct.lean` (Chris Birkbeck), rewritten to
consume Mathlib's `MeasureSpace ℍ` instance instead of constructing the hyperbolic measure.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.4
* Miyake, *Modular forms*, §2.5
* The AINTLIB `LeanModularForms` project,
  <https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>
  (`Modularforms/PeterssonInnerProduct.lean`)
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
  have h := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc
  have h_eq : (· ^ (-2 : ℝ) : ℝ → ℝ) = (· ^ (-2 : ℤ)) := by
    funext x
    rw [← Real.rpow_intCast]
    norm_num
  rwa [h_eq] at h

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
    ∫⁻ z in measurableEquivRealProd ⁻¹' T, g z.im ∂(volume : Measure ℂ) =
      ∫⁻ p in T, g p.2 ∂(volume : Measure (ℝ × ℝ)) := by
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
    _ ≤ ∫⁻ z in measurableEquivRealProd ⁻¹' T, ENNReal.ofReal (z.im ^ (-2 : ℤ)) :=
        lintegral_mono_set fun z ↦ by
          rintro ⟨τ, hτ, rfl⟩
          simp only [mem_preimage, measurableEquivRealProd_apply, coe_re, coe_im]
          refine ⟨⟨by linarith [(abs_le.mp hτ.2).1], (abs_le.mp hτ.2).2⟩,
            mem_Ioi.mpr ?_⟩
          have h := three_le_four_mul_im_sq_of_mem_fd hτ
          have h_sq : (4 : ℝ) * τ.im ^ 2 = (2 * τ.im) ^ 2 := by ring
          rw [h_sq] at h
          have h2 := Real.sqrt_le_sqrt h
          rw [Real.sqrt_sq (by linarith [τ.im_pos])] at h2
          nlinarith [Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3)]
    _ = ∫⁻ p in T, ENNReal.ofReal (p.2 ^ (-2 : ℤ)) ∂volume :=
        setLIntegral_im_eq_prod (fun y ↦ ENNReal.ofReal (y ^ (-2 : ℤ))) T
    _ < ⊤ := strip_lintegral_lt_top (by positivity)

private theorem volume_complex_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h_eq : {z : ℂ | z.re = c} = measurableEquivRealProd ⁻¹' ({c} ×ˢ univ) := by
    ext z
    simp [measurableEquivRealProd_apply]
  rw [h_eq, volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet,
    volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

private theorem volume_complex_normSq_eq (c : ℝ) :
    volume {z : ℂ | Complex.normSq z = c} = 0 := by
  rcases le_or_gt 0 c with hc | hc
  · have h_eq : {z : ℂ | Complex.normSq z = c} = Metric.sphere (0 : ℂ) (Real.sqrt c) := by
      ext z
      simp only [mem_ofPred_eq, Complex.normSq_eq_norm_sq, mem_sphere_zero_iff_norm]
      constructor
      · intro h
        rw [← h, Real.sqrt_sq (norm_nonneg z)]
      · intro h
        rw [h, Real.sq_sqrt hc]
    rw [h_eq]
    exact Measure.addHaar_sphere volume 0 _
  · have h_empty : {z : ℂ | Complex.normSq z = c} = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun z hz ↦ not_le.mpr hc (hz ▸ Complex.normSq_nonneg z)
    rw [h_empty]
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

/-- The Petersson pairing of two functions `f, g : ℍ → ℂ` of weight `k`, integrated over
an arbitrary set `D` (in applications, a fundamental domain) with respect to the
invariant measure.

The integrand is `conj(f(τ)) · g(τ) · (Im τ)^k`, which equals
`petersson k f g τ` from `Mathlib.NumberTheory.ModularForms.Petersson`. -/
def peterssonInner (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) : ℂ :=
  ∫ τ in D, petersson k f g τ

theorem peterssonInner_def (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    peterssonInner k D f g = ∫ τ in D, petersson k f g τ := (rfl)

/-- Hermitian symmetry: `conj ⟨g, f⟩ = ⟨f, g⟩`. -/
theorem peterssonInner_conj_symm (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    conj (peterssonInner k D g f) = peterssonInner k D f g := by
  simp only [peterssonInner, ← integral_conj, petersson_symm k g f]

/-- The pairing with zero on the right vanishes. -/
@[simp]
theorem peterssonInner_zero_right (k : ℤ) (D : Set ℍ) (f : ℍ → ℂ) :
    peterssonInner k D f 0 = 0 := by
  simp [peterssonInner, petersson]

/-- The pairing with zero on the left vanishes. -/
@[simp]
theorem peterssonInner_zero_left (k : ℤ) (D : Set ℍ) (g : ℍ → ℂ) :
    peterssonInner k D 0 g = 0 := by
  simp [peterssonInner, petersson]

/-- Negation in the right argument. -/
@[simp]
theorem peterssonInner_neg_right (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    peterssonInner k D f (-g) = -peterssonInner k D f g := by
  simp only [peterssonInner, petersson, Pi.neg_apply, mul_neg, neg_mul, integral_neg]

/-- Negation in the left argument. -/
@[simp]
theorem peterssonInner_neg_left (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    peterssonInner k D (-f) g = -peterssonInner k D f g := by
  simp only [peterssonInner, petersson, Pi.neg_apply, map_neg, neg_mul, integral_neg]

/-- The Petersson integrand of a cusp form against a modular form is integrable over the
standard fundamental domain. -/
theorem integrableOn_petersson_fd_left {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
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
theorem integrableOn_petersson_fd_right {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
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
  simp only [peterssonInner]
  rw [← integral_add hg₁ hg₂]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ by
    simp only [petersson, Pi.add_apply]
    ring)

/-- Additivity in the first argument, given integrability of both summands. -/
theorem peterssonInner_add_left (k : ℤ) (D : Set ℍ) (f₁ f₂ g : ℍ → ℂ)
    (hf₁ : IntegrableOn (fun τ ↦ petersson k f₁ g τ) D (volume : Measure ℍ))
    (hf₂ : IntegrableOn (fun τ ↦ petersson k f₂ g τ) D (volume : Measure ℍ)) :
    peterssonInner k D (f₁ + f₂) g = peterssonInner k D f₁ g + peterssonInner k D f₂ g := by
  simp only [peterssonInner]
  rw [← integral_add hf₁ hf₂]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ by
    simp only [petersson, Pi.add_apply, map_add]
    ring)

/-- Scalar multiplication in the second argument. -/
@[simp]
theorem peterssonInner_smul_right (k : ℤ) (D : Set ℍ) (c : ℂ) (f g : ℍ → ℂ) :
    peterssonInner k D f (c • g) = c * peterssonInner k D f g := by
  simp only [peterssonInner]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ by
    simp only [petersson, Pi.smul_apply, smul_eq_mul]
    ring)

/-- Conjugate-scalar multiplication in the left argument. -/
@[simp]
theorem peterssonInner_smul_left (k : ℤ) (D : Set ℍ) (c : ℂ) (f g : ℍ → ℂ) :
    peterssonInner k D (c • f) g = conj c * peterssonInner k D f g := by
  simp only [peterssonInner]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ by
    simp only [petersson, Pi.smul_apply, smul_eq_mul, map_mul]
    ring)

private lemma petersson_self_re_eq (z : ℂ) (y : ℝ) (k : ℤ) :
    (starRingEnd ℂ z * z * (↑y : ℂ) ^ k).re = Complex.normSq z * y ^ k := by
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_zpow, ← Complex.ofReal_mul,
    Complex.ofReal_re]

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
  have hint := integrableOn_petersson_fd_left k Γ f f
  have hg_zero : ∫ z in fd, g z = 0 := by
    trans RCLike.re (∫ z in fd, petersson k (⇑f) (⇑f) z)
    · exact integral_re hint
    · simp only [peterssonInner] at hpet; rw [hpet]; simp
  have hg_nonneg : ∀ z, 0 ≤ g z := fun z ↦ by
    simp only [g, petersson]
    exact (petersson_self_re_eq (f z) z.im k).symm ▸
      mul_nonneg (Complex.normSq_nonneg _) (zpow_nonneg z.im_pos.le _)
  have hg_ae : g =ᶠ[ae ((volume : Measure ℍ).restrict fd)] 0 := by
    rwa [← integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hg_nonneg) hint.re]
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

/-- The **level-one-domain Petersson pairing** of two cusp forms: the integral over the
standard fundamental domain `𝒟` for `SL₂(ℤ)`, whatever the level `Γ` — the `Fd` in the
name marks that the integration domain is `𝒟`, not a `Γ`-fundamental domain.

This is **not** the `Γ \ ℍ`-normalized Petersson inner product, which integrates over a
`Γ`-fundamental domain. It is nonetheless Hermitian-sesquilinear
(`peterssonInnerFd_add_left`/`_right`, `peterssonInnerFd_smul_left`/`_right`) and positive
definite for cusp forms of any arithmetic level (`peterssonInnerFd_definite`, below). -/
def peterssonInnerFd (f g : CuspForm Γ k) : ℂ :=
  UpperHalfPlane.peterssonInner k ModularGroup.fd f g

theorem peterssonInnerFd_def (f g : CuspForm Γ k) :
    peterssonInnerFd f g = UpperHalfPlane.peterssonInner k ModularGroup.fd f g := (rfl)

/-- Hermitian symmetry of the level-one-domain pairing. -/
theorem peterssonInnerFd_conj_symm (f g : CuspForm Γ k) :
    conj (peterssonInnerFd g f) = peterssonInnerFd f g := by
  simp only [peterssonInnerFd_def]
  exact UpperHalfPlane.peterssonInner_conj_symm k ModularGroup.fd f g

@[simp]
theorem peterssonInnerFd_zero_right (f : CuspForm Γ k) : peterssonInnerFd f 0 = 0 := by
  simp [peterssonInnerFd_def]

@[simp]
theorem peterssonInnerFd_zero_left (g : CuspForm Γ k) : peterssonInnerFd 0 g = 0 := by
  simp [peterssonInnerFd_def]

section HasDetOne

variable [Γ.HasDetOne]

/-- The level-one-domain pairing is ℂ-linear in the second argument. -/
theorem peterssonInnerFd_smul_right (c : ℂ) (f g : CuspForm Γ k) :
    peterssonInnerFd f (c • g) = c * peterssonInnerFd f g := by
  simp only [peterssonInnerFd_def, IsGLPos.coe_smul]
  exact UpperHalfPlane.peterssonInner_smul_right k ModularGroup.fd c f g

/-- The level-one-domain pairing is conjugate-linear in the first argument. -/
theorem peterssonInnerFd_smul_left (c : ℂ) (f g : CuspForm Γ k) :
    peterssonInnerFd (c • f) g = conj c * peterssonInnerFd f g := by
  simp only [peterssonInnerFd_def, IsGLPos.coe_smul]
  exact UpperHalfPlane.peterssonInner_smul_left k ModularGroup.fd c f g

end HasDetOne

section IsArithmetic

variable [Γ.IsArithmetic]

/-- Additivity of the level-one-domain pairing in the second argument. -/
theorem peterssonInnerFd_add_right (f g₁ g₂ : CuspForm Γ k) :
    peterssonInnerFd f (g₁ + g₂) = peterssonInnerFd f g₁ + peterssonInnerFd f g₂ := by
  simp only [peterssonInnerFd_def, coe_add]
  exact UpperHalfPlane.peterssonInner_add_right k ModularGroup.fd f g₁ g₂
    (integrableOn_petersson_fd_left k Γ f g₁) (integrableOn_petersson_fd_left k Γ f g₂)

/-- Additivity of the level-one-domain pairing in the first argument. -/
theorem peterssonInnerFd_add_left (f₁ f₂ g : CuspForm Γ k) :
    peterssonInnerFd (f₁ + f₂) g = peterssonInnerFd f₁ g + peterssonInnerFd f₂ g := by
  rw [← peterssonInnerFd_conj_symm, peterssonInnerFd_add_right, map_add,
    peterssonInnerFd_conj_symm, peterssonInnerFd_conj_symm]

/-- **Positive definiteness of the level-one-domain pairing**: a cusp form of any
arithmetic level with vanishing self-pairing is zero.

The self-pairing vanishing forces `f = 0` on the open fundamental domain `𝒟ᵒ`
(`eq_zero_on_fd_of_peterssonInner_self_eq_zero`), and a holomorphic function on `ℍ`
vanishing on a nonempty open set vanishes identically
(`UpperHalfPlane.eq_zero_of_frequently`). -/
theorem peterssonInnerFd_definite (f : CuspForm Γ k) (hpet : peterssonInnerFd f f = 0) :
    f = 0 := by
  rw [peterssonInnerFd_def] at hpet
  have hfdo : ∀ τ ∈ ModularGroup.fdo, f τ = 0 := fun τ hτ ↦
    eq_zero_on_fd_of_peterssonInner_self_eq_zero f hpet (ModularGroup.fdo_subset_fd hτ)
  set τ₀ : ℍ := ⟨⟨0, 2⟩, by norm_num⟩ with hτ₀_def
  have hτ₀ : τ₀ ∈ ModularGroup.fdo := by
    constructor
    · norm_num [hτ₀_def, Complex.normSq_apply]
    · norm_num [hτ₀_def]
  have hev := Filter.eventually_of_mem (ModularGroup.isOpen_fdo.mem_nhds hτ₀) hfdo
  have h := UpperHalfPlane.eq_zero_of_frequently (CuspFormClass.holo f)
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  ext τ
  exact congr_fun h τ

end IsArithmetic

end CuspForm
