/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
public import Mathlib.RingTheory.Complex
public import TauCeti.RingTheory.NormTrace.Pi

/-!
# The volume scaling of multiplication on the mixed space

Multiplication by a fixed point `c` of the mixed space is an `ℝ`-linear endomorphism, so it
scales Lebesgue measure by the absolute value of its determinant.  That determinant is computed
here as one factor per real place and one `Complex.normSq` per complex place, and its absolute
value is `mixedEmbedding.norm c`.

Specialising to the image of a unit, which has mixed norm one, gives that the unit action on the
mixed space leaves the volume of every set unchanged.

## Main results

* `NumberField.mixedEmbedding.lmul_eq_prodMap`: multiplication by `c` as the product of the
  multiplications by its real and its complex component;
* `NumberField.mixedEmbedding.det_lmul`: its determinant, as a product over the places;
* `NumberField.mixedEmbedding.abs_det_lmul`: the absolute value of that determinant is
  `mixedEmbedding.norm c`;
* `NumberField.mixedEmbedding.volume_image_mul_left`: multiplication by `c` scales volume by
  `mixedEmbedding.norm c`;
* `NumberField.mixedEmbedding.volume_unitSMul`: the unit action preserves volume.
-/

public section

open MeasureTheory NumberField NumberField.InfinitePlace

open scoped Pointwise

namespace NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- Multiplication on the mixed space acts on its two factors independently, so as an `ℝ`-linear
map it is the product of multiplication by the real component and by the complex component. -/
theorem lmul_eq_prodMap (c : mixedSpace K) :
    Algebra.lmul ℝ (mixedSpace K) c = LinearMap.prodMap
      (Algebra.lmul ℝ ({w : InfinitePlace K // IsReal w} → ℝ) c.1)
      (Algebra.lmul ℝ ({w : InfinitePlace K // IsComplex w} → ℂ) c.2) := rfl

open scoped Classical in
/-- **The determinant of multiplication on the mixed space.**  Each real coordinate contributes
its own factor and each complex coordinate contributes the norm of multiplication by a complex
number, namely `Complex.normSq`. -/
theorem det_lmul (c : mixedSpace K) : LinearMap.det (Algebra.lmul ℝ (mixedSpace K) c) =
    (∏ w, c.1 w) * ∏ w, Complex.normSq (c.2 w) := by
  -- `simp only`: full `simp` rewrites `Algebra.lmul` to `LinearMap.mul` and blocks `norm_apply`.
  simp only [lmul_eq_prodMap, LinearMap.det_prodMap, ← Algebra.norm_apply,
    TauCeti.Algebra.norm_pi, Algebra.norm_self, MonoidHom.id_apply, Algebra.norm_complex_apply]

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
so there is no measurability hypothesis to discharge.  Its specialisation to the action of a
unit, stated as `u • A` and with factor one, is `volume_unitSMul`. -/
theorem volume_image_mul_left (c : mixedSpace K) (A : Set (mixedSpace K)) :
    volume ((c * ·) '' A) = ENNReal.ofReal (mixedEmbedding.norm c) * volume A := by
  rw [← abs_det_lmul]
  -- `(c * ·)` is definitionally the `ℝ`-linear map `Algebra.lmul ℝ (mixedSpace K) c`.
  exact Measure.addHaar_image_linearMap volume (Algebra.lmul ℝ (mixedSpace K) c) A

open scoped Classical in
/-- **A unit acts by a volume-preserving map.**  For a general multiplier `c`, where the factor is
`mixedEmbedding.norm c`, use `volume_image_mul_left`.  This is in `simp` normal form: the
pointwise action on a set is not rewritten by `unitSMul_smul`, which acts on points. -/
@[simp]
theorem volume_unitSMul (u : (𝓞 K)ˣ) (A : Set (mixedSpace K)) : volume (u • A) = volume A := by
  -- A unit has mixed norm one, so the factor `volume_image_mul_left` supplies is one.
  simp [← Set.image_smul, volume_image_mul_left]

end NumberField.mixedEmbedding
