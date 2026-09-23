/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.Complex

/-!
# How multiplication on the mixed space scales volume

Multiplication by a fixed point `c` of the mixed space is an `ℝ`-linear endomorphism, so it
scales Lebesgue measure by the absolute value of its determinant.  That determinant is computed
here: it is `mixedEmbedding.norm c`, the same product of local absolute values that measures the
index of an ideal lattice.

The consequence used downstream is that the action of a unit is measure preserving, because a
unit has mixed norm one.  Counting lattice points in a region built from unit translates — a ray
fundamental domain, say — needs exactly that.

## Main results

* `TauCeti.NumberField.mixedEmbedding.det_lmul`: the determinant of multiplication by `c`,
  as a product over the real and the complex places;
* `TauCeti.NumberField.mixedEmbedding.abs_det_lmul`: its absolute value is `mixedEmbedding.norm c`;
* `TauCeti.NumberField.mixedEmbedding.volume_mul_left_image`: multiplication by `c` scales volume
  by `mixedEmbedding.norm c`;
* `TauCeti.NumberField.mixedEmbedding.volume_unitSMul`: the action of a unit preserves volume.
-/

public section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Pointwise

namespace TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- Multiplication on the mixed space is componentwise, so as an `ℝ`-linear map it is the product
of the two componentwise multiplications, one on the real places and one on the complex ones. -/
theorem lmul_eq_prodMap (c : mixedSpace K) :
    Algebra.lmul ℝ (mixedSpace K) c = LinearMap.prodMap
      (LinearMap.pi fun w ↦ (Algebra.lmul ℝ ℝ (c.1 w)).comp (LinearMap.proj w))
      (LinearMap.pi fun w ↦ (Algebra.lmul ℝ ℂ (c.2 w)).comp (LinearMap.proj w)) := rfl

open scoped Classical in
/-- **The determinant of multiplication on the mixed space.**  Each real coordinate contributes
its own factor and each complex coordinate contributes the norm of multiplication by a complex
number, namely `Complex.normSq`. -/
theorem det_lmul (c : mixedSpace K) :
    LinearMap.det (Algebra.lmul ℝ (mixedSpace K) c) =
      (∏ w, c.1 w) * ∏ w, Complex.normSq (c.2 w) := by
  rw [lmul_eq_prodMap, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  congr 1
  · exact Finset.prod_congr rfl fun i _ ↦ by simp
  · exact Finset.prod_congr rfl fun i _ ↦
      (Algebra.norm_apply ℝ (c.2 i)).symm.trans (Algebra.norm_complex_apply (c.2 i))

/-- **The absolute determinant of multiplication by `c` is the mixed norm of `c`.**  The two are
the same product of local absolute values: a real place contributes `|c w|` and a complex place
contributes `‖c w‖ ^ 2`, which is `Complex.normSq`. -/
theorem abs_det_lmul (c : mixedSpace K) :
    |LinearMap.det (Algebra.lmul ℝ (mixedSpace K) c)| = mixedEmbedding.norm c := by
  classical
  rw [det_lmul, abs_mul, Finset.abs_prod, Finset.abs_prod, mixedEmbedding.norm_apply,
    ← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K ↦ w.IsReal)]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [normAtPlace_apply_of_isReal w.prop, InfinitePlace.mult_isReal, pow_one, Real.norm_eq_abs]
  · refine Fintype.prod_equiv
      (Equiv.subtypeEquivRight fun w ↦ (not_isReal_iff_isComplex (w := w)).symm) _ _ fun w ↦ ?_
    simp only [Equiv.subtypeEquivRight_apply_coe]
    rw [abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq,
      normAtPlace_apply_of_isComplex w.prop, w.prop.mult_eq_two]

open scoped Classical in
/-- **Multiplication by `c` scales volume by the mixed norm of `c`.** -/
theorem volume_mul_left_image (c : mixedSpace K) (A : Set (mixedSpace K)) :
    volume ((c * ·) '' A) = ENNReal.ofReal (mixedEmbedding.norm c) * volume A := by
  have : ((c * ·) : mixedSpace K → mixedSpace K) = Algebra.lmul ℝ (mixedSpace K) c := rfl
  rw [this, Measure.addHaar_image_linearMap, abs_det_lmul]

open scoped Classical in
/-- **A unit acts by a volume preserving map.**  Its mixed norm is one, so the scaling factor in
`volume_mul_left_image` is one. -/
theorem volume_unitSMul (u : (𝓞 K)ˣ) (A : Set (mixedSpace K)) :
    volume (u • A) = volume A := by
  have himg : u • A = ((mixedEmbedding K (u : K) * ·) '' A) := by
    ext x
    simp [Set.mem_smul_set, unitSMul_smul, eq_comm]
  rw [himg, volume_mul_left_image, norm_unit, ENNReal.ofReal_one, one_mul]

end TauCeti.NumberField.mixedEmbedding
