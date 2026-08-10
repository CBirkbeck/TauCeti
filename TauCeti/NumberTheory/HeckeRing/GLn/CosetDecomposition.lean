/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.Triangular
public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets

/-!
# Upper-triangular representatives for a diagonal double coset

For a tuple `a` of positive naturals, this file exhibits a family of elements of the double
coset `SL_n(ℤ) · diag(a) · SL_n(ℤ)`, indexed by the bounded entry assignments
`B_{ij} ∈ {0, …, a_j / a_i - 1}` for `i < j`, and shows that they lie in pairwise distinct
left `SL_n(ℤ)`-cosets — so the double coset contains at least `∏_{i < j} (a_j / a_i)` of them.

The representative attached to `B` is *defined* as `diag(a) · U(B)`, where `U(B)` is the
unipotent upper-triangular integral matrix with off-diagonal entries `B`. Two things follow
from that shape, and are the reason for choosing it over an entrywise definition: `U(B)` is
upper triangular with ones on the diagonal, so `det U(B) = 1` and `U(B) ∈ SL_n(ℤ)`; and hence
the representative lies in the double coset with no further argument.
`upperTriGL_apply_lt`, `upperTriGL_apply_diag` and `upperTriGL_apply_eq_zero_of_lt` recover the
entrywise description `M_{ij} = a_i · B_{ij}` for consumers that need it; injectivity itself
does not, since `upperTriGL` is visibly a composition of injective maps.

## Main definitions

* `UpperTriEntries` — the bounded entry assignments `B_{ij} ∈ Fin (a j / a i)` for `i < j`.
* `unitriMat`, `unitriSL` — the unipotent upper-triangular matrix `U(B)`, and its packaging as
  an element of `SL_n(ℤ)`.
* `upperTriGL` — the representative `diag(a) · U(B)` in `GL_n(ℚ)`.

## Main results

* `upperTriGL_mem_doubleCoset` — every representative lies in `SL_n(ℤ) · diag(a) · SL_n(ℤ)`.
* `unitriMat_injective`, `upperTriGL_injective` — distinct entry assignments give distinct
  matrices, hence distinct representatives.
* `upperTriGL_eq_of_dvd` — the representatives lie in *distinct* left `SL_n(ℤ)`-cosets: two of
  them are left-equivalent only when their entry assignments agree. Left equivalence says the
  comparison matrix `C = U(B₁) · U(B₂)⁻¹` satisfies `(a_j / a_i) ∣ C_{ij}`, and the entry bound
  then forces `C = 1` by induction on `j - i`.

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
the results, not to name the index type. The component `Fin (a j / a i)` is empty exactly when
`a j / a i = 0`, which for positive `a i` means `a j < a i`. -/
abbrev UpperTriEntries (a : Fin n → ℕ) : Type :=
  (p : {ij : Fin n × Fin n // ij.1 < ij.2}) → Fin (a p.val.2 / a p.val.1)

variable {n}

/-- The unipotent upper-triangular integral matrix `U(B)`: ones on the diagonal, `B_{ij}`
above it, zeros below. -/
def unitriMat {a : Fin n → ℕ} (B : UpperTriEntries n a) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ if h : i < j then (B ⟨(i, j), h⟩ : ℕ) else if i = j then 1 else 0

@[simp] lemma unitriMat_apply_lt {a : Fin n → ℕ} (B : UpperTriEntries n a) {i j : Fin n}
    (h : i < j) : unitriMat B i j = (B ⟨(i, j), h⟩ : ℕ) := by
  simp [unitriMat, h]

@[simp] lemma unitriMat_apply_diag {a : Fin n → ℕ} (B : UpperTriEntries n a) (i : Fin n) :
    unitriMat B i i = 1 := by
  simp [unitriMat]

@[simp] lemma unitriMat_apply_eq_zero_of_lt {a : Fin n → ℕ} (B : UpperTriEntries n a)
    {i j : Fin n} (h : j < i) : unitriMat B i j = 0 := by
  simp [unitriMat, h.asymm, h.ne']

lemma isUpperTriangular_unitriMat {a : Fin n → ℕ} (B : UpperTriEntries n a) :
    Matrix.IsUpperTriangular (unitriMat B) :=
  fun _ _ h ↦ unitriMat_apply_eq_zero_of_lt B h

/-- `U(B)` is upper triangular with ones on the diagonal, so its determinant is `1`. -/
@[simp] lemma det_unitriMat {a : Fin n → ℕ} (B : UpperTriEntries n a) : (unitriMat B).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (isUpperTriangular_unitriMat B)]
  simp

/-- `U(B)` packaged as an element of `SL_n(ℤ)`. -/
def unitriSL {a : Fin n → ℕ} (B : UpperTriEntries n a) : SpecialLinearGroup (Fin n) ℤ :=
  ⟨unitriMat B, det_unitriMat B⟩

@[simp] lemma unitriSL_coe {a : Fin n → ℕ} (B : UpperTriEntries n a) :
    (unitriSL B : Matrix (Fin n) (Fin n) ℤ) = unitriMat B := (rfl)

/-- The upper-triangular representative `diag(a) · U(B)` attached to a bounded entry
assignment. -/
noncomputable def upperTriGL {a : Fin n → ℕ} (B : UpperTriEntries n a) : GL (Fin n) ℚ :=
  natDiagGL n a * (mapGL ℚ (unitriSL B))

/-- Each upper-triangular representative lies in the double coset of `diag(a)`.

Immediate from the definition: `U(B) ∈ SL_n(ℤ)`, so `diag(a) · U(B)` is already of the form
`h₁ · diag(a) · h₂` with `h₁ = 1`. -/
lemma upperTriGL_mem_doubleCoset {a : Fin n → ℕ} (B : UpperTriEntries n a) :
    upperTriGL B ∈ doubleCoset (natDiagGL n a) (SLnZ n) (SLnZ n) :=
  mem_doubleCoset.mpr ⟨1, one_mem _, mapGL ℚ (unitriSL B), coe_mem_SLnZ n _,
    by rw [upperTriGL, one_mul]⟩

/-- The entrywise description of the representative above the diagonal: `M_{ij} = a_i · B_{ij}`.
-/
@[simp] lemma upperTriGL_apply_lt {a : Fin n → ℕ} (ha : ∀ i, 0 < a i) (B : UpperTriEntries n a)
    {i j : Fin n} (h : i < j) :
    (upperTriGL B : Matrix (Fin n) (Fin n) ℚ) i j = (a i : ℚ) * (B ⟨(i, j), h⟩ : ℕ) := by
  rw [upperTriGL]
  simp [natDiagGL_coe n a ha, Matrix.diagonal_mul, unitriMat_apply_lt B h]

/-- The entrywise description on the diagonal: `M_{ii} = a_i`. -/
@[simp] lemma upperTriGL_apply_diag {a : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (B : UpperTriEntries n a) (i : Fin n) :
    (upperTriGL B : Matrix (Fin n) (Fin n) ℚ) i i = (a i : ℚ) := by
  rw [upperTriGL]
  simp [natDiagGL_coe n a ha, Matrix.diagonal_mul]

/-- The representative is upper triangular: entries below the diagonal vanish. -/
@[simp] lemma upperTriGL_apply_eq_zero_of_lt {a : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (B : UpperTriEntries n a) {i j : Fin n} (h : j < i) :
    (upperTriGL B : Matrix (Fin n) (Fin n) ℚ) i j = 0 := by
  rw [upperTriGL]
  simp [natDiagGL_coe n a ha, Matrix.diagonal_mul, unitriMat_apply_eq_zero_of_lt B h]

/-- Distinct entry assignments give distinct unipotent matrices. -/
lemma unitriMat_injective {a : Fin n → ℕ} : Function.Injective (unitriMat (a := a)) := by
  intro B₁ B₂ h
  funext p
  obtain ⟨⟨i, j⟩, hij⟩ := p
  have hE := congrFun (congrFun h i) j
  rw [unitriMat_apply_lt B₁ hij, unitriMat_apply_lt B₂ hij] at hE
  exact Fin.ext (by exact_mod_cast hE)

/-- Distinct entry assignments give distinct representatives.

`upperTriGL` is a composition of injective maps — left multiplication by the fixed unit
`diag(a)`, then `mapGL ℚ`, then `unitriMat` — so no positivity hypothesis is needed: even at a
tuple where `natDiagGL` takes its junk value `1`, left multiplication is still injective. -/
lemma upperTriGL_injective {a : Fin n → ℕ} : Function.Injective (upperTriGL (a := a)) := by
  intro B₁ B₂ h
  rw [upperTriGL, upperTriGL] at h
  have hSL := mapGL_injective (mul_left_cancel h)
  exact unitriMat_injective (by rw [← unitriSL_coe, ← unitriSL_coe, hSL])

/-! ## Distinctness of the left cosets

Two representatives lie in the same left `SL_n(ℤ)`-coset exactly when the conjugate
`diag(a)⁻¹ · S · diag(a)` of the connecting element `S` is integral, which says
`(a_j / a_i) ∣ C_{ij}` for the comparison matrix `C = U(B₁) · U(B₂)⁻¹`. The entry bound
`B_{ij} < a_j / a_i` then forces `C = 1`. -/

section Triangular

variable {R : Type*} [CommRing R] {M : Matrix (Fin n) (Fin n) R}

/-- The inverse of an upper-triangular matrix with `1` on the diagonal again has `1` on the
diagonal: `M⁻¹ * M = 1` read on the diagonal, through
`Matrix.mul_apply_diag_of_isUpperTriangular`. -/
lemma inv_apply_diag_of_isUpperTriangular [Invertible M] (hM : Matrix.IsUpperTriangular M)
    (hdiag : ∀ i, M i i = 1) (i : Fin n) : M⁻¹ i i = 1 := by
  have hinv : Matrix.IsUpperTriangular M⁻¹ := Matrix.blockTriangular_inv_of_blockTriangular hM
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul M (Matrix.isUnit_det_of_invertible M)) i) i
  rwa [Matrix.mul_apply_diag_of_isUpperTriangular hinv hM i, hdiag i, mul_one,
    Matrix.one_apply_eq] at h

end Triangular

/-- The comparison matrix `C` between two representatives is the identity above the diagonal.

Strong induction on `j - i`. Reading `C · U(B₂) = U(B₁)` at `(i, j)`, every term of the sum
except `k = i` and `k = j` drops: below `i` because `C` is upper triangular, strictly between
because the inductive hypothesis has already killed those entries, and above `j` because
`U(B₂)` is upper triangular. What is left is `(B₂)_{ij} + C_{ij} = (B₁)_{ij}`, so `C_{ij}` is a
difference of two entries each below `a_j / a_i`; being divisible by `a_j / a_i` it vanishes. -/
private lemma comparison_apply_eq_zero {a : Fin n → ℕ} {B₁ B₂ : UpperTriEntries n a}
    {C : Matrix (Fin n) (Fin n) ℤ} (hmul : C * unitriMat B₂ = unitriMat B₁)
    (hup : Matrix.IsUpperTriangular C) (hdiag : ∀ i, C i i = 1)
    (hdvd : ∀ ⦃i j : Fin n⦄, i < j → ((a j / a i : ℕ) : ℤ) ∣ C i j) :
    ∀ ⦃i j : Fin n⦄, i < j → C i j = 0 := by
  suffices H : ∀ d : ℕ, ∀ i j : Fin n, (j : ℕ) - (i : ℕ) = d → i < j → C i j = 0 from
    fun i j hij ↦ H _ i j rfl hij
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i j hd hij
    have hne : i ≠ j := hij.ne
    -- Only `k = i` and `k = j` contribute to `(C * U(B₂)) i j`.
    have hvanish : ∀ k ∈ Finset.univ, k ∉ ({i, j} : Finset (Fin n)) →
        C i k * unitriMat B₂ k j = 0 := by
      intro k _ hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      rcases lt_trichotomy k i with hki | rfl | hik
      · rw [hup hki, zero_mul]
      · exact absurd rfl hk.1
      · rcases lt_trichotomy k j with hkj | rfl | hjk
        · rw [ih ((k : ℕ) - (i : ℕ)) (by omega) i k rfl hik, zero_mul]
        · exact absurd rfl hk.2
        · rw [unitriMat_apply_eq_zero_of_lt B₂ hjk, mul_zero]
    have hkey := congrFun (congrFun hmul i) j
    rw [Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin n)))
      hvanish, Finset.sum_pair hne, hdiag i, one_mul, unitriMat_apply_diag, mul_one,
      unitriMat_apply_lt B₂ hij, unitriMat_apply_lt B₁ hij] at hkey
    -- `C i j` is a difference of two entries, each strictly below `a j / a i`.
    have hb₁ : (B₁ ⟨(i, j), hij⟩ : ℕ) < a j / a i := (B₁ ⟨(i, j), hij⟩).isLt
    have hb₂ : (B₂ ⟨(i, j), hij⟩ : ℕ) < a j / a i := (B₂ ⟨(i, j), hij⟩).isLt
    refine Int.eq_zero_of_abs_lt_dvd (hdvd hij) ?_
    have hCij : C i j = ((B₁ ⟨(i, j), hij⟩ : ℕ) : ℤ) - ((B₂ ⟨(i, j), hij⟩ : ℕ) : ℤ) := by
      linarith
    rw [hCij, abs_lt]
    omega

/-- Two upper-triangular representatives lie in the same left `SL_n(ℤ)`-coset only if their
entry assignments agree.

The connecting element is `S = M₁ M₂⁻¹`; conjugating, `diag(a)⁻¹ S diag(a) = U(B₁) U(B₂)⁻¹`,
whose `(i,j)` entry is `S_{ij} · a_j / a_i`. Integrality of `S` is therefore exactly the
divisibility hypothesis fed to `comparison_apply_eq_zero`. -/
lemma upperTriGL_eq_of_dvd {a : Fin n → ℕ} {B₁ B₂ : UpperTriEntries n a}
    (hdvd : ∀ ⦃i j : Fin n⦄, i < j →
      ((a j / a i : ℕ) : ℤ) ∣ (unitriMat B₁ * (unitriMat B₂)⁻¹) i j) :
    B₁ = B₂ := by
  have : Invertible (unitriMat B₂) :=
    Matrix.invertibleOfIsUnitDet _ (by rw [det_unitriMat]; exact isUnit_one)
  have hup₂ : Matrix.IsUpperTriangular (unitriMat B₂)⁻¹ :=
    Matrix.blockTriangular_inv_of_blockTriangular (isUpperTriangular_unitriMat B₂)
  set C : Matrix (Fin n) (Fin n) ℤ := unitriMat B₁ * (unitriMat B₂)⁻¹ with hC
  have hup : Matrix.IsUpperTriangular C :=
    Matrix.BlockTriangular.mul (isUpperTriangular_unitriMat B₁) hup₂
  have hdiag : ∀ i, C i i = 1 := fun i ↦ by
    rw [hC, Matrix.mul_apply_diag_of_isUpperTriangular (isUpperTriangular_unitriMat B₁) hup₂ i,
      unitriMat_apply_diag,
      inv_apply_diag_of_isUpperTriangular (isUpperTriangular_unitriMat B₂)
        (unitriMat_apply_diag B₂) i, one_mul]
  have hmul : C * unitriMat B₂ = unitriMat B₁ := by
    rw [hC, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_invertible _),
      Matrix.mul_one]
  have hzero := comparison_apply_eq_zero hmul hup hdiag hdvd
  have hC1 : C = 1 := by
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hzero h, Matrix.one_apply_ne h.ne]
    · rw [hdiag, Matrix.one_apply_eq]
    · rw [hup h, Matrix.one_apply_ne h.ne']
  exact unitriMat_injective (by rw [← hmul, hC1, Matrix.one_mul])

end HeckeRing.GLn
