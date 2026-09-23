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
theorem det_lmul (c : mixedSpace K) : LinearMap.det (Algebra.lmul ℝ (mixedSpace K) c) =
    (∏ w, c.1 w) * ∏ w, Complex.normSq (c.2 w) := by
  -- `simp only`: full `simp` rewrites `Algebra.lmul` to `LinearMap.mul` and blocks `norm_apply`.
  simp only [lmul_eq_prodMap, LinearMap.det_prodMap, LinearMap.det_pi, ← Algebra.norm_apply,
    Algebra.norm_self, MonoidHom.id_apply, Algebra.norm_complex_apply]

/-- **The absolute determinant of multiplication by `c` is the mixed norm of `c`.**  Reach for
this rather than `det_lmul` when the determinant feeds a measure-scaling lemma such as
`Measure.addHaar_image_linearMap`, which asks for the absolute value. -/
theorem abs_det_lmul (c : mixedSpace K) :
    |LinearMap.det (Algebra.lmul ℝ (mixedSpace K) c)| = mixedEmbedding.norm c := by
  -- Both sides are the same product of local absolute values: a real place contributes `|c.1 w|`
  -- with `mult w = 1`, a complex place `Complex.normSq (c.2 w) = ‖c.2 w‖ ^ 2` with `mult w = 2`.
  rw [det_lmul, abs_mul, Finset.abs_prod, Finset.abs_prod, mixedEmbedding.norm_apply,
    InfinitePlace.prod_eq_prod_mul_prod]
  simp [normAtPlace_apply_of_isReal, normAtPlace_apply_of_isComplex, Complex.normSq_eq_norm_sq,
    Subtype.prop]

open scoped Classical in
/-- **Multiplication by `c` scales volume by the mixed norm of `c`.**  The set `A` is arbitrary,
so there is no measurability hypothesis to discharge; for `c` the image of a unit, where the
factor is one, use `volume_unitSMul`. -/
theorem volume_mul_left_image (c : mixedSpace K) (A : Set (mixedSpace K)) :
    volume ((c * ·) '' A) = ENNReal.ofReal (mixedEmbedding.norm c) * volume A := by
  rw [← abs_det_lmul]
  -- `(c * ·)` is definitionally the `ℝ`-linear map `Algebra.lmul ℝ (mixedSpace K) c`.
  exact Measure.addHaar_image_linearMap volume (Algebra.lmul ℝ (mixedSpace K) c) A

open scoped Classical in
/-- **A unit acts by a volume-preserving map.**  For a general multiplier `c`, where the factor is
`mixedEmbedding.norm c`, use `volume_mul_left_image`. -/
@[simp]
theorem volume_unitSMul (u : (𝓞 K)ˣ) (A : Set (mixedSpace K)) : volume (u • A) = volume A := by
  -- A unit has mixed norm one, so the factor `volume_mul_left_image` supplies is one.
  simp [← Set.image_smul, volume_mul_left_image]

end TauCeti.NumberField.mixedEmbedding
