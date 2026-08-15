/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Tower
import TauCeti.FieldTheory.IntermediateField.FieldRange

/-!
# Separable and inseparable degrees of an isogeny

`TauCeti.Isogeny.degree` is the dimension of `W₁.FunctionField` over the image of `fieldPullback`.
That extension is finite, so it splits the degree into a separable and an inseparable part, and
this file names those two parts and records that they multiply to the degree.

## Main definitions

* `TauCeti.Isogeny.separableDegree`: the separable degree of the function-field extension.
* `TauCeti.Isogeny.inseparableDegree`: its inseparable degree.

## Main results

* `TauCeti.Isogeny.separableDegree_mul_inseparableDegree`: the two multiply to `degree`.
* `TauCeti.Isogeny.separableDegree_pos` and `TauCeti.Isogeny.inseparableDegree_pos`: both are
  positive, so neither factor is degenerate.
* `TauCeti.Isogeny.separableDegree_comp` and `TauCeti.Isogeny.inseparableDegree_comp`: both are
  multiplicative under composition, matching `degree_comp`.
* `TauCeti.Isogeny.separableDegree_eq_degree_of_isSeparable` and
  `TauCeti.Isogeny.inseparableDegree_eq_one_of_isSeparable`: a separable isogeny carries its
  whole degree in the separable part.
* `TauCeti.Isogeny.separableDegree_eq_one_of_isPurelyInseparable` and
  `TauCeti.Isogeny.inseparableDegree_eq_degree_of_isPurelyInseparable`: the purely inseparable
  case. No declaration consumes these yet; they are the shape the roadmap's Frobenius milestone
  ("`π_q`, purely inseparable of degree `q`") will need.

## Design

There is deliberately no `Isogeny.IsSeparable` predicate. Separability of `φ` is
`Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField` — an existing Mathlib class
applied to the extension `degree` already measures — and a wrapper around it would add a second
name for one notion without adding a fact. The same holds for pure inseparability, which is
`IsPurelyInseparable` on the same extension. What is *not* already sayable is the pair of numbers,
so that is what this file adds.

This follows Layer 1 of `TauCetiRoadmap/EllipticCurves/README.md`, which fixes the convention:

> **Degree and separability are field theory.** `deg φ` is `Module.finrank` of `W₁.FunctionField`
> over the fraction field of the pulled-back coordinate ring […]; the separable and inseparable
> degrees, and separability of `φ`, are those of the field extension — Mathlib's existing
> `FieldTheory`, not a flatness theory of morphisms.

Both definitions are unconditional: no separability hypothesis, so purely inseparable isogenies
such as Frobenius are covered, matching `Isogeny.finiteDimensional`.

Multiplicativity under composition is `separableDegree_comp` and `inseparableDegree_comp`,
matching `degree_comp`. Both go through the tower `F(W₃) ⊆ F(W₂) ⊆ F(W₁)`, using the separable
transports off `AlgHom.fieldRange` that sit beside `finrank_fieldRange`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The separable degree of an isogeny**: the separable degree of `W₁.FunctionField` over the
pulled-back copy of the target's function field. -/
noncomputable def separableDegree (φ : Isogeny W₁ W₂) : ℕ :=
  Field.finSepDegree φ.fieldPullback.fieldRange W₁.FunctionField

/-- **The inseparable degree of an isogeny**, of the same extension. -/
noncomputable def inseparableDegree (φ : Isogeny W₁ W₂) : ℕ :=
  Field.finInsepDegree φ.fieldPullback.fieldRange W₁.FunctionField

/-- The defining formula for `separableDegree`. The definition's body is not exposed across the
module boundary, so this is how downstream modules compute with it. -/
theorem separableDegree_def (φ : Isogeny W₁ W₂) :
    φ.separableDegree = Field.finSepDegree φ.fieldPullback.fieldRange W₁.FunctionField := (rfl)

/-- The defining formula for `inseparableDegree`. -/
theorem inseparableDegree_def (φ : Isogeny W₁ W₂) :
    φ.inseparableDegree = Field.finInsepDegree φ.fieldPullback.fieldRange W₁.FunctionField := (rfl)

/-- Finiteness above the pullback's range transfers to the function field itself. Private: it
exists to feed the transports below, and consumers read finiteness off `Isogeny.finiteDimensional`.
-/
private theorem finiteDimensional_of_finiteDimensional_fieldRange (φ : Isogeny W₁ W₂)
    [Algebra W₂.FunctionField W₁.FunctionField]
    (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z) :
    FiniteDimensional W₂.FunctionField W₁.FunctionField := by
  let _ : Algebra W₂.FunctionField φ.fieldPullback.fieldRange :=
    (φ.fieldPullback.equivFieldRange).toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower W₂.FunctionField φ.fieldPullback.fieldRange W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      rw [RingHom.algebraMap_toAlgebra]
      exact (h z).trans (AlgHom.equivFieldRange_apply_coe φ.fieldPullback z).symm
  have : FiniteDimensional W₂.FunctionField φ.fieldPullback.fieldRange :=
    Module.Finite.of_surjective (Algebra.linearMap W₂.FunctionField _) fun y ↦
      ⟨φ.fieldPullback.equivFieldRange.symm y, by
        simp [Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]⟩
  exact FiniteDimensional.trans W₂.FunctionField φ.fieldPullback.fieldRange W₁.FunctionField

/-- **The separable degree read off any algebra structure induced by the pullback**, the
separable analogue of `degree_eq_finrank`. Stated for an arbitrary structure whose map is
`fieldPullback`, since registering one globally would be a diamond. -/
theorem separableDegree_eq_finSepDegree (φ : Isogeny W₁ W₂)
    [Algebra W₂.FunctionField W₁.FunctionField]
    (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z) :
    φ.separableDegree = Field.finSepDegree W₂.FunctionField W₁.FunctionField :=
  have := φ.finiteDimensional_of_finiteDimensional_fieldRange h
  (φ.separableDegree_def).trans (TauCeti.AlgHom.finSepDegree_fieldRange φ.fieldPullback h)

/-- **The inseparable degree read off any algebra structure induced by the pullback.** -/
theorem inseparableDegree_eq_finInsepDegree (φ : Isogeny W₁ W₂)
    [Algebra W₂.FunctionField W₁.FunctionField]
    (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z) :
    φ.inseparableDegree = Field.finInsepDegree W₂.FunctionField W₁.FunctionField :=
  have := φ.finiteDimensional_of_finiteDimensional_fieldRange h
  (φ.inseparableDegree_def).trans (TauCeti.AlgHom.finInsepDegree_fieldRange φ.fieldPullback h)

/-- **The degree factors as separable times inseparable.** This is the field-theoretic
factorisation transported to isogenies; it is what makes "the inseparable part is a Frobenius
power" a statement about `inseparableDegree`. -/
theorem separableDegree_mul_inseparableDegree (φ : Isogeny W₁ W₂) :
    φ.separableDegree * φ.inseparableDegree = φ.degree :=
  (Field.finSepDegree_mul_finInsepDegree _ _).trans φ.degree_def.symm

/-- The separable degree of an isogeny is positive. Mathlib already knows the underlying
field-theoretic degree is nonzero, so this only transports that. -/
theorem separableDegree_pos (φ : Isogeny W₁ W₂) : 0 < φ.separableDegree := by
  simpa [separableDegree_def] using
    NeZero.pos (Field.finSepDegree φ.fieldPullback.fieldRange W₁.FunctionField)

/-- The inseparable degree of an isogeny is positive, likewise. -/
theorem inseparableDegree_pos (φ : Isogeny W₁ W₂) : 0 < φ.inseparableDegree := by
  simpa [inseparableDegree_def] using
    NeZero.pos (Field.finInsepDegree φ.fieldPullback.fieldRange W₁.FunctionField)

/-- The separable degree of an isogeny is nonzero. -/
@[simp]
theorem separableDegree_ne_zero (φ : Isogeny W₁ W₂) : φ.separableDegree ≠ 0 :=
  φ.separableDegree_pos.ne'

/-- The inseparable degree of an isogeny is nonzero. -/
@[simp]
theorem inseparableDegree_ne_zero (φ : Isogeny W₁ W₂) : φ.inseparableDegree ≠ 0 :=
  φ.inseparableDegree_pos.ne'

/-- **The identity isogeny has separable degree one.** -/
@[simp]
theorem separableDegree_id (W : WeierstrassCurve.Affine F) : (id W).separableDegree = 1 := by
  have h : (id W).separableDegree * (id W).inseparableDegree = 1 :=
    ((id W).separableDegree_mul_inseparableDegree.trans (degree_id W))
  exact Nat.eq_one_of_mul_eq_one_right h

/-- **The identity isogeny has inseparable degree one.** -/
@[simp]
theorem inseparableDegree_id (W : WeierstrassCurve.Affine F) : (id W).inseparableDegree = 1 := by
  have h : (id W).separableDegree * (id W).inseparableDegree = 1 :=
    ((id W).separableDegree_mul_inseparableDegree.trans (degree_id W))
  exact Nat.eq_one_of_mul_eq_one_left h

/-- **A separable isogeny has separable degree equal to its degree.** -/
@[simp]
theorem separableDegree_eq_degree_of_isSeparable (φ : Isogeny W₁ W₂)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    φ.separableDegree = φ.degree := by
  rw [separableDegree_def, degree_def, Field.finSepDegree_eq_finrank_of_isSeparable]

/-- **A separable isogeny has inseparable degree one.** -/
@[simp]
theorem inseparableDegree_eq_one_of_isSeparable (φ : Isogeny W₁ W₂)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    φ.inseparableDegree = 1 := by
  rw [inseparableDegree_def, Algebra.IsSeparable.finInsepDegree_eq]

/-- **A purely inseparable isogeny has separable degree one.** -/
@[simp]
theorem separableDegree_eq_one_of_isPurelyInseparable (φ : Isogeny W₁ W₂)
    [IsPurelyInseparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    φ.separableDegree = 1 := by
  rw [separableDegree_def, IsPurelyInseparable.finSepDegree_eq_one]

/-- **A purely inseparable isogeny carries its whole degree in the inseparable part.** -/
@[simp]
theorem inseparableDegree_eq_degree_of_isPurelyInseparable (φ : Isogeny W₁ W₂)
    [IsPurelyInseparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    φ.inseparableDegree = φ.degree := by
  rw [inseparableDegree_def, degree_def, IsPurelyInseparable.finInsepDegree_eq]

/-- The pullback-induced algebra structure has the pullback as its structure map. The composition
laws below each need this three times — for `φ`, for `ψ` and for `ψ.comp φ` — and it is the
hypothesis every `_eq_finSepDegree`-style lemma in this file takes. -/
private theorem algebraMap_fieldPullback_eq (φ : Isogeny W₁ W₂) (z : W₂.FunctionField) :
    @algebraMap W₂.FunctionField W₁.FunctionField _ _ φ.fieldPullback.toRingHom.toAlgebra z =
      φ.fieldPullback z := by
  rw [RingHom.algebraMap_toAlgebra]
  exact congrFun (AlgHom.coe_toRingHom φ.fieldPullback) z

variable {W₃ : WeierstrassCurve.Affine F}

/-- **The separable degree is multiplicative under composition**, by the tower formula for
`F(W₃) ⊆ F(W₂) ⊆ F(W₁)`, exactly as `degree_comp`. -/
@[simp]
theorem separableDegree_comp (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).separableDegree = ψ.separableDegree * φ.separableDegree := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  let _ := ψ.fieldPullback.toRingHom.toAlgebra
  let _ := (ψ.comp φ).fieldPullback.toRingHom.toAlgebra
  have hφ := φ.algebraMap_fieldPullback_eq
  have hψ := ψ.algebraMap_fieldPullback_eq
  have hc := (ψ.comp φ).algebraMap_fieldPullback_eq
  have : IsScalarTower W₃.FunctionField W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      simp [RingHom.algebraMap_toAlgebra, comp_fieldPullback]
  have h₁ := φ.finiteDimensional_of_finiteDimensional_fieldRange hφ
  have h₂ := ψ.finiteDimensional_of_finiteDimensional_fieldRange hψ
  have h₃ := (ψ.comp φ).finiteDimensional_of_finiteDimensional_fieldRange hc
  rw [(ψ.comp φ).separableDegree_eq_finSepDegree hc, ψ.separableDegree_eq_finSepDegree hψ,
    φ.separableDegree_eq_finSepDegree hφ]
  exact (Field.finSepDegree_mul_finSepDegree_of_isAlgebraic W₃.FunctionField W₂.FunctionField
    W₁.FunctionField).symm

/-- **The inseparable degree is multiplicative under composition**, by the same tower as
`separableDegree_comp`. -/
@[simp]
theorem inseparableDegree_comp (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).inseparableDegree = ψ.inseparableDegree * φ.inseparableDegree := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  let _ := ψ.fieldPullback.toRingHom.toAlgebra
  let _ := (ψ.comp φ).fieldPullback.toRingHom.toAlgebra
  have hφ := φ.algebraMap_fieldPullback_eq
  have hψ := ψ.algebraMap_fieldPullback_eq
  have hc := (ψ.comp φ).algebraMap_fieldPullback_eq
  have : IsScalarTower W₃.FunctionField W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      simp [RingHom.algebraMap_toAlgebra, comp_fieldPullback]
  have h₁ := φ.finiteDimensional_of_finiteDimensional_fieldRange hφ
  have h₂ := ψ.finiteDimensional_of_finiteDimensional_fieldRange hψ
  have h₃ := (ψ.comp φ).finiteDimensional_of_finiteDimensional_fieldRange hc
  rw [(ψ.comp φ).inseparableDegree_eq_finInsepDegree hc, ψ.inseparableDegree_eq_finInsepDegree hψ,
    φ.inseparableDegree_eq_finInsepDegree hφ]
  exact (Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic (F := W₃.FunctionField)
    (E := W₂.FunctionField) (K := W₁.FunctionField)).symm

end Isogeny

end TauCeti
