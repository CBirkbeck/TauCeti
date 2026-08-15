/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# The degree above the range of a field embedding

An `F`-algebra map `f : K →ₐ[F] L` of fields is injective, so it identifies `K` with the
intermediate field `f.fieldRange`. This file records that the two therefore support the same
degree: `[L : f.fieldRange] = [L : K]`, whenever `L` is a `K`-algebra through `f`.

Both dimensions are needed in practice. A degree over `K` is what an abstract extension
supplies, while a degree over `f.fieldRange` is what any argument comparing two subfields of
`L` — a tower, or a relative degree — must work with, since those subfields are intermediate
fields of one extension rather than separate types.

The `K`-algebra structure on `L` is a hypothesis rather than `f.toRingHom.toAlgebra`, because
the structure the caller already has need only agree with `f`, and for a fixed pair `K`, `L`
different embeddings `f` induce different structures, so none can be registered globally.

## Main results

* `TauCeti.AlgHom.finrank_fieldRange`: `[L : f.fieldRange] = [L : K]`.
* `TauCeti.AlgHom.finSepDegree_fieldRange` and `TauCeti.AlgHom.finInsepDegree_fieldRange`: the
  same for the separable and inseparable degrees.
-/

public section

namespace TauCeti.AlgHom

variable {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]

/-- **The degree above the range of a field embedding equals the degree above its source.**
Stated for an arbitrary `K`-algebra structure on `L` whose structure map is `f`, rather than for
`f.toRingHom.toAlgebra`, so that it applies to a structure the caller already has. -/
theorem finrank_fieldRange (f : K →ₐ[F] L) [Algebra K L] (h : ∀ z, algebraMap K L z = f z) :
    Module.finrank f.fieldRange L = Module.finrank K L := by
  -- transport along `f.equivFieldRange`, the range restriction of `f`, which is the identity
  -- on `L`; both squares commute because `h` says the structure map is `f`
  have hsquare : (algebraMap f.fieldRange L).comp f.equivFieldRange.toRingEquiv.toRingHom =
      (RingEquiv.refl L).toRingHom.comp (algebraMap K L) := by
    ext z
    exact (_root_.AlgHom.equivFieldRange_apply_coe f z).trans (h z).symm
  exact (Algebra.finrank_eq_of_equiv_equiv f.equivFieldRange.toRingEquiv (RingEquiv.refl L)
    hsquare).symm

/-- **The separable degree is unchanged by a surjective base change.** For a tower
`K → E → L` whose lower map is onto, an `L`-embedding is `E`-linear exactly when it is
`K`-linear, so the two embedding sets coincide. -/
theorem _root_.Field.finSepDegree_of_surjective {E : Type*} [Field E] [Algebra K L] [Algebra K E]
    [Algebra E L] [IsScalarTower K E L] (hsurj : Function.Surjective (algebraMap K E)) :
    Field.finSepDegree E L = Field.finSepDegree K L := by
  unfold Field.finSepDegree
  exact Nat.card_congr (AlgHom.extendScalarsOfSurjective hsurj).symm

/-- **The inseparable degree is unchanged by a surjective base change**, by the same tower: a
surjective map of fields is bijective, so the lower step has degree one. -/
theorem _root_.Field.finInsepDegree_of_surjective {E : Type*} [Field E] [Algebra K L]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Algebra.IsAlgebraic K E]
    (hsurj : Function.Surjective (algebraMap K E)) :
    Field.finInsepDegree E L = Field.finInsepDegree K L := by
  have hrank : Module.finrank K E = 1 :=
    finrank_eq_one_iff_of_nonzero' (1 : E) one_ne_zero |>.2 fun w ↦
      ⟨(hsurj w).choose, by simpa [Algebra.smul_def] using (hsurj w).choose_spec⟩
  have h1 : Field.finInsepDegree K E = 1 := by
    have hmul := Field.finSepDegree_mul_finInsepDegree K E
    rw [hrank] at hmul
    exact Nat.eq_one_of_mul_eq_one_left hmul
  have hmul := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic K E L
  rw [h1, one_mul] at hmul
  exact hmul

/-- **The separable degree above the range of a field embedding equals the one above its
source.** The `f.fieldRange` case of `Field.finSepDegree_of_surjective`. -/
theorem finSepDegree_fieldRange (f : K →ₐ[F] L) [Algebra K L] (h : ∀ z, algebraMap K L z = f z) :
    Field.finSepDegree f.fieldRange L = Field.finSepDegree K L := by
  let _ : Algebra K f.fieldRange := (f.equivFieldRange).toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower K f.fieldRange L :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      rw [RingHom.algebraMap_toAlgebra]
      exact (h z).trans (_root_.AlgHom.equivFieldRange_apply_coe f z).symm
  exact Field.finSepDegree_of_surjective fun r ↦
    ⟨f.equivFieldRange.symm r, by
      rw [RingHom.algebraMap_toAlgebra]; exact f.equivFieldRange.apply_symm_apply r⟩

/-- **The inseparable degree above the range of a field embedding equals the one above its
source.** The `f.fieldRange` case of `Field.finInsepDegree_of_surjective`. -/
theorem finInsepDegree_fieldRange (f : K →ₐ[F] L) [Algebra K L] (h : ∀ z, algebraMap K L z = f z) :
    Field.finInsepDegree f.fieldRange L = Field.finInsepDegree K L := by
  let _ : Algebra K f.fieldRange := (f.equivFieldRange).toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower K f.fieldRange L :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      rw [RingHom.algebraMap_toAlgebra]
      exact (h z).trans (_root_.AlgHom.equivFieldRange_apply_coe f z).symm
  have hsurj : Function.Surjective (algebraMap K f.fieldRange) := fun r ↦
    ⟨f.equivFieldRange.symm r, by
      rw [RingHom.algebraMap_toAlgebra]; exact f.equivFieldRange.apply_symm_apply r⟩
  have : FiniteDimensional K f.fieldRange :=
    Module.Finite.of_surjective (Algebra.linearMap K f.fieldRange) hsurj
  exact Field.finInsepDegree_of_surjective hsurj

end TauCeti.AlgHom
