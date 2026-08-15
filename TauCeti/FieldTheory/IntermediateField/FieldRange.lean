/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.FieldTheory.PurelyInseparable.Basic

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

/-- **The separable degree above the range of a field embedding equals the one above its
source.** The separable analogue of `finrank_fieldRange`, for any `K`-algebra structure on `L`
whose structure map is `f`. -/
theorem finSepDegree_fieldRange (f : K →ₐ[F] L) [Algebra K L] (h : ∀ z, algebraMap K L z = f z)
    [Algebra.IsAlgebraic K L] :
    Field.finSepDegree f.fieldRange L = Field.finSepDegree K L := by
  let _ : Algebra K f.fieldRange := (f.equivFieldRange).toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower K f.fieldRange L :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      rw [RingHom.algebraMap_toAlgebra]
      exact (h z).trans (_root_.AlgHom.equivFieldRange_apply_coe f z).symm
  have h1 : Field.finSepDegree K f.fieldRange = 1 := by
    have he : Field.finSepDegree K K = Field.finSepDegree K f.fieldRange :=
      Field.finSepDegree_eq_of_equiv K K f.fieldRange
        (AlgEquiv.ofRingEquiv (f := (f.equivFieldRange).toRingEquiv) fun z ↦ by
          rw [RingHom.algebraMap_toAlgebra]; rfl)
    rw [← he, Field.finSepDegree_self]
  have : Algebra.IsAlgebraic (f.fieldRange) L := Algebra.IsAlgebraic.tower_top (K := K) _
  have hmul := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic K f.fieldRange L
  rw [h1, one_mul] at hmul
  exact hmul

/-- **The inseparable degree above the range of a field embedding equals the one above its
source**, under the same hypotheses as `finSepDegree_fieldRange`. -/
theorem finInsepDegree_fieldRange (f : K →ₐ[F] L) [Algebra K L] (h : ∀ z, algebraMap K L z = f z)
    [FiniteDimensional K L] :
    Field.finInsepDegree f.fieldRange L = Field.finInsepDegree K L := by
  have hsep := finSepDegree_fieldRange f h
  have hrank := finrank_fieldRange f h
  have hL := Field.finSepDegree_mul_finInsepDegree (f.fieldRange) L
  have hK := Field.finSepDegree_mul_finInsepDegree K L
  rw [hsep] at hL
  rw [hrank] at hL
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos (Field.finSepDegree K L)) (hL.trans hK.symm)

end TauCeti.AlgHom
