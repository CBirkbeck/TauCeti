/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets

/-!
# Upper-triangular representatives for a diagonal double coset

For a tuple `a` of positive naturals, this file exhibits a family of elements of the double
coset `SL_n(ℤ) · diag(a) · SL_n(ℤ)`, indexed by the bounded entry assignments
`B_{ij} ∈ {0, …, a_j / a_i - 1}` for `i < j`, and shows the family is injective.

The representative attached to `B` is *defined* as `diag(a) · U(B)`, where `U(B)` is the
unipotent upper-triangular integral matrix with off-diagonal entries `B`. Two things follow
from that shape, and are the reason for choosing it over an entrywise definition: `U(B)` is
upper triangular with ones on the diagonal, so `det U(B) = 1` and `U(B) ∈ SL_n(ℤ)`; and hence
the representative lies in the double coset with no further argument.
`upperTriGL_apply_lt` and `upperTriGL_apply_diag` recover the entrywise description
`M_{ij} = a_i · B_{ij}`, which is what the injectivity argument uses.

## Main definitions

* `UpperTriRep` — the bounded entry assignments `B_{ij} ∈ Fin (a j / a i)` for `i < j`.
* `unitriMat`, `unitriSL` — the unipotent upper-triangular matrix `U(B)`, and its packaging as
  an element of `SL_n(ℤ)`.
* `upperTriGL` — the representative `diag(a) · U(B)` in `GL_n(ℚ)`.

## Main results

* `upperTriGL_mem_doubleCoset` — every representative lies in `SL_n(ℤ) · diag(a) · SL_n(ℤ)`.
* `unitriMat_injective`, `upperTriGL_injective` — distinct entry assignments give distinct
  matrices, hence distinct representatives.

## References

The general-`n` statement is Shimura, *Introduction to the Arithmetic Theory of Automorphic
Functions* (1971), Exercise 3.26(A), p. 65: for every `α ∈ Δ` one can choose representatives
`α_j` of `ΓαΓ = ⋃_j Γα_j` with `L_ν α_j ⊆ L_ν` for the standard flag `L_ν = ∑_{i ≤ ν} ℤ e_i`,
i.e. upper-triangular ones. Shimura leaves it as an exercise and works the `n = 2` case
explicitly in Prop. 3.33 (p. 70) and Prop. 3.36 (p. 72).

The definitions follow the AINTLIB [`LeanModularForms`](https://github.com/CBirkbeck/AINTLIB)
file `LeanModularForms/HeckeRIngs/GLn/CosetDecomposition.lean` (Chris Birkbeck), whose module
docstring cites "Shimura, Proposition 3.22" — that number is in fact Lemma 3.22, an Euler
product identity, and is unrelated. The results here are new: the AINTLIB file states the
definitions and the determinant, and advertises the coset results in its docstring without
proving them.
-/

public section

open Matrix Matrix.SpecialLinearGroup DoubleCoset

namespace HeckeRing.GLn

variable (n : ℕ)

/-- Bounded entry assignments for upper-triangular representatives: an integer
`B_{ij} ∈ {0, …, a_j / a_i - 1}` for each pair `i < j`.

Stated for an arbitrary tuple `a`, with no chain or positivity hypothesis: those are needed by
the results, not to name the index type, and `Fin (a j / a i)` is already empty exactly when
`a j < a i`. -/
abbrev UpperTriRep (a : Fin n → ℕ) : Type :=
  (p : {ij : Fin n × Fin n // ij.1 < ij.2}) → Fin (a p.val.2 / a p.val.1)

variable {n}

/-- The unipotent upper-triangular integral matrix `U(B)`: ones on the diagonal, `B_{ij}`
above it, zeros below. -/
def unitriMat {a : Fin n → ℕ} (B : UpperTriRep n a) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ if h : i < j then (B ⟨(i, j), h⟩ : ℕ) else if i = j then 1 else 0

@[simp] lemma unitriMat_apply_lt {a : Fin n → ℕ} (B : UpperTriRep n a) {i j : Fin n}
    (h : i < j) : unitriMat B i j = (B ⟨(i, j), h⟩ : ℕ) := by
  simp [unitriMat, h]

@[simp] lemma unitriMat_apply_diag {a : Fin n → ℕ} (B : UpperTriRep n a) (i : Fin n) :
    unitriMat B i i = 1 := by
  simp [unitriMat]

lemma unitriMat_apply_of_lt {a : Fin n → ℕ} (B : UpperTriRep n a) {i j : Fin n} (h : j < i) :
    unitriMat B i j = 0 := by
  simp [unitriMat, h.asymm, h.ne']

lemma isUpperTriangular_unitriMat {a : Fin n → ℕ} (B : UpperTriRep n a) :
    Matrix.IsUpperTriangular (unitriMat B) :=
  fun _ _ h ↦ unitriMat_apply_of_lt B h

/-- `U(B)` is upper triangular with ones on the diagonal, so its determinant is `1`. -/
@[simp] lemma det_unitriMat {a : Fin n → ℕ} (B : UpperTriRep n a) : (unitriMat B).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (isUpperTriangular_unitriMat B)]
  simp

/-- `U(B)` packaged as an element of `SL_n(ℤ)`. -/
def unitriSL {a : Fin n → ℕ} (B : UpperTriRep n a) : SpecialLinearGroup (Fin n) ℤ :=
  ⟨unitriMat B, det_unitriMat B⟩

@[simp] lemma unitriSL_coe {a : Fin n → ℕ} (B : UpperTriRep n a) :
    (unitriSL B : Matrix (Fin n) (Fin n) ℤ) = unitriMat B := (rfl)

/-- The upper-triangular representative `diag(a) · U(B)` attached to a bounded entry
assignment. -/
noncomputable def upperTriGL {a : Fin n → ℕ} (B : UpperTriRep n a) : GL (Fin n) ℚ :=
  natDiagGL n a * (mapGL ℚ (unitriSL B))

/-- Each upper-triangular representative lies in the double coset of `diag(a)`.

Immediate from the definition: `U(B) ∈ SL_n(ℤ)`, so `diag(a) · U(B)` is already of the form
`h₁ · diag(a) · h₂` with `h₁ = 1`. -/
lemma upperTriGL_mem_doubleCoset {a : Fin n → ℕ} (B : UpperTriRep n a) :
    upperTriGL B ∈ doubleCoset (natDiagGL n a) (SLnZ n) (SLnZ n) :=
  mem_doubleCoset.mpr ⟨1, one_mem _, mapGL ℚ (unitriSL B), coe_mem_SLnZ n _,
    by rw [upperTriGL, one_mul]⟩

/-- The entrywise description of the representative above the diagonal: `M_{ij} = a_i · B_{ij}`.
-/
lemma upperTriGL_apply_lt {a : Fin n → ℕ} (ha : ∀ i, 0 < a i) (B : UpperTriRep n a)
    {i j : Fin n} (h : i < j) :
    (upperTriGL B : Matrix (Fin n) (Fin n) ℚ) i j = (a i : ℚ) * (B ⟨(i, j), h⟩ : ℕ) := by
  rw [upperTriGL]
  simp [natDiagGL_coe n a ha, Matrix.diagonal_mul, unitriMat_apply_lt B h]

/-- The entrywise description on the diagonal: `M_{ii} = a_i`. -/
lemma upperTriGL_apply_diag {a : Fin n → ℕ} (ha : ∀ i, 0 < a i) (B : UpperTriRep n a)
    (i : Fin n) : (upperTriGL B : Matrix (Fin n) (Fin n) ℚ) i i = (a i : ℚ) := by
  rw [upperTriGL]
  simp [natDiagGL_coe n a ha, Matrix.diagonal_mul]

/-- Distinct entry assignments give distinct unipotent matrices. -/
lemma unitriMat_injective {a : Fin n → ℕ} : Function.Injective (unitriMat (a := a)) := by
  intro B₁ B₂ h
  funext p
  obtain ⟨⟨i, j⟩, hij⟩ := p
  have hE := congrFun (congrFun h i) j
  rw [unitriMat_apply_lt B₁ hij, unitriMat_apply_lt B₂ hij] at hE
  exact Fin.ext (by exact_mod_cast hE)

/-- Distinct entry assignments give distinct representatives: the entries `a_i · B_{ij}`
determine `B`, because every `a_i` is nonzero. -/
lemma upperTriGL_injective {a : Fin n → ℕ} (ha : ∀ i, 0 < a i) :
    Function.Injective (upperTriGL (a := a)) := by
  intro B₁ B₂ h
  refine unitriMat_injective (funext fun i ↦ funext fun j ↦ ?_)
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hE : (upperTriGL B₁ : Matrix (Fin n) (Fin n) ℚ) i j =
        (upperTriGL B₂ : Matrix (Fin n) (Fin n) ℚ) i j := by rw [h]
    rw [upperTriGL_apply_lt ha B₁ hij, upperTriGL_apply_lt ha B₂ hij] at hE
    have hai : (a i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ha i).ne'
    rw [unitriMat_apply_lt B₁ hij, unitriMat_apply_lt B₂ hij]
    exact_mod_cast mul_left_cancel₀ hai hE
  · simp
  · rw [unitriMat_apply_of_lt B₁ hij, unitriMat_apply_of_lt B₂ hij]

end HeckeRing.GLn
