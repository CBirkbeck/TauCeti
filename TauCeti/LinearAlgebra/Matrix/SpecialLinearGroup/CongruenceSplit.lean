/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Tactic.LinearCombination
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# Chinese-remainder splitting of `SL_n(ℤ)`

For coprime moduli `d, d'`, every `τ ∈ SL_n(ℤ)` factors as `τ₁ * τ₂` with `τ₁ ≡ 1 (mod d)`
and `τ₂ ≡ 1 (mod d')`. The proof is by generators: `τ` is a product of transvections
(`exists_list_transvec_prod`), a single transvection splits by Bézout, and splittings
multiply.

## Main results

* `Matrix.SpecialLinearGroup.exists_mul_congMod_of_coprime`: the factorization.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/CoprimeMul.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), where it is the group-theoretic input to the coprime multiplication rule of
the Hecke ring.
-/

public section

open Matrix

namespace Matrix.SpecialLinearGroup

variable (n : ℕ)

/-! ## Chinese-remainder splitting of `SL_n(ℤ)`

Every `τ ∈ SL_n(ℤ)` factors as `τ₁ * τ₂` with `τ₁ ≡ 1 mod d` and `τ₂ ≡ 1 mod d'` for
coprime `d, d'`: transvections split by Bézout, and splittings multiply. -/

/-- `σ ≡ 1 (mod d)`, entrywise. -/
private def congMod (d : ℕ) (σ : SpecialLinearGroup (Fin n) ℤ) : Prop :=
  ∀ i j, (d : ℤ) ∣ (σ.1 i j - if i = j then 1 else 0)

private lemma congMod_transvection (d : ℕ) {i j : Fin n} (hij : i ≠ j) {c : ℤ}
    (hdc : (d : ℤ) ∣ c) : congMod n d (SpecialLinearGroup.transvection hij c) := by
  intro k l
  rw [SpecialLinearGroup.transvection_coe]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single, Matrix.of_apply,
    add_sub_cancel_left]
  split_ifs with h
  · exact hdc
  · exact dvd_zero _

private lemma transvection_CRT (d d' : ℕ) (hcop : Nat.Coprime d d')
    {i j : Fin n} (hij : i ≠ j) (c : ℤ) :
    ∃ τ₁ τ₂ : SpecialLinearGroup (Fin n) ℤ,
      SpecialLinearGroup.transvection hij c = τ₁ * τ₂ ∧
        congMod n d τ₁ ∧ congMod n d' τ₂ := by
  have hbez : ↑(Nat.gcd d d') = (d : ℤ) * Nat.gcdA d d' + ↑d' * Nat.gcdB d d' :=
    Nat.gcd_eq_gcd_ab d d'
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  refine ⟨SpecialLinearGroup.transvection hij (c * d * Nat.gcdA d d'),
    SpecialLinearGroup.transvection hij (c * d' * Nat.gcdB d d'), ?_, ?_, ?_⟩
  · rw [← SpecialLinearGroup.transvection_add]
    congr 1
    linear_combination c * hbez
  · exact congMod_transvection n d hij ⟨c * Nat.gcdA d d', by ring⟩
  · exact congMod_transvection n d' hij ⟨c * Nat.gcdB d d', by ring⟩

private lemma congMod_one (d : ℕ) : congMod n d 1 := fun i j ↦ by
  simp [SpecialLinearGroup.coe_one, Matrix.one_apply]

private lemma congMod_mul (d : ℕ) (a b : SpecialLinearGroup (Fin n) ℤ)
    (ha : congMod n d a) (hb : congMod n d b) : congMod n d (a * b) := by
  intro i j
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  have h2 : ∑ k, (a.1 i k - if i = k then 1 else 0) * b.1 k j =
      (∑ k, a.1 i k * b.1 k j) - b.1 i j := by
    simp [sub_mul, Finset.sum_sub_distrib]
  have h3 : (∑ k, a.1 i k * b.1 k j) - (if i = j then 1 else 0) =
      (∑ k, (a.1 i k - if i = k then 1 else 0) * b.1 k j) +
      (b.1 i j - if i = j then 1 else 0) := by linarith
  rw [h3]
  exact dvd_add (Finset.dvd_sum fun k _ ↦ dvd_mul_of_dvd_left (ha i k) _) (hb i j)

private lemma congMod_conj (d : ℕ) (σ τ : SpecialLinearGroup (Fin n) ℤ)
    (hτ : congMod n d τ) : congMod n d (σ⁻¹ * τ * σ) := by
  intro i j
  have hassoc : σ⁻¹ * τ * σ = σ⁻¹ * (τ * σ) := by group
  simp only [hassoc, SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  have h_inv : ∀ i' j', ∑ k : Fin n, (σ⁻¹).1 i' k * σ.1 k j' =
      if i' = j' then 1 else 0 := by
    intro i' j'
    have hmul : (σ⁻¹).1 * σ.1 = 1 := by rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
    simpa [Matrix.mul_apply, Matrix.one_apply] using congr_fun (congr_fun hmul i') j'
  have h_inner : ∀ k, ∑ l : Fin n, τ.1 k l * σ.1 l j =
      (∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j) + σ.1 k j := by
    intro k
    have h2 : ∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j =
        (∑ l, τ.1 k l * σ.1 l j) - σ.1 k j := by
      simp [sub_mul, Finset.sum_sub_distrib]
    linarith
  have h3 : (∑ k, (σ⁻¹).1 i k * ∑ l, τ.1 k l * σ.1 l j) =
      (∑ k, (σ⁻¹).1 i k * ∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j) +
      (∑ k, (σ⁻¹).1 i k * σ.1 k j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [h_inner k]
    ring
  have h4 : (∑ k, (σ⁻¹).1 i k * ∑ l, τ.1 k l * σ.1 l j) - (if i = j then 1 else 0) =
      ∑ k, (σ⁻¹).1 i k * ∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j := by
    rw [h3, h_inv]
    ring
  rw [h4]
  exact Finset.dvd_sum fun k _ ↦ dvd_mul_of_dvd_right
    (Finset.dvd_sum fun l _ ↦ dvd_mul_of_dvd_left (hτ k l) _) _

/-- Elements admitting a CRT splitting are closed under products: conjugate the second
`d`-part across the first `d'`-part. -/
private lemma crtProd_mul (d d' : ℕ) (a b : SpecialLinearGroup (Fin n) ℤ)
    (ha : ∃ p q, a = p * q ∧ congMod n d p ∧ congMod n d' q)
    (hb : ∃ p q, b = p * q ∧ congMod n d p ∧ congMod n d' q) :
    ∃ p q, a * b = p * q ∧ congMod n d p ∧ congMod n d' q := by
  obtain ⟨p₁, q₁, rfl, hp₁, hq₁⟩ := ha
  obtain ⟨p₂, q₂, rfl, hp₂, hq₂⟩ := hb
  refine ⟨p₁ * (q₁ * p₂ * q₁⁻¹), q₁ * q₂, by group, ?_,
    congMod_mul n d' _ _ hq₁ hq₂⟩
  have h := congMod_conj n d q₁⁻¹ p₂ hp₂
  rw [inv_inv] at h
  exact congMod_mul n d _ _ hp₁ h

/-- **Chinese remainder decomposition of `SL_n(ℤ)`**: for coprime `d, d'`, every element
factors as `τ₁ * τ₂` with `τ₁ ≡ 1 mod d` and `τ₂ ≡ 1 mod d'`. -/
lemma exists_mul_congMod_of_coprime (d d' : ℕ) (hcop : Nat.Coprime d d')
    (τ : SpecialLinearGroup (Fin n) ℤ) :
    ∃ τ₁ τ₂ : SpecialLinearGroup (Fin n) ℤ, τ = τ₁ * τ₂ ∧
      (∀ i j, (d : ℤ) ∣ ((τ₁ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0)) ∧
      (∀ i j, (d' : ℤ) ∣ ((τ₂ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0)) := by
  obtain ⟨T, hT⟩ := SpecialLinearGroup.exists_list_transvec_prod τ
  rw [hT]
  clear hT
  induction T with
  | nil => exact ⟨1, 1, (one_mul 1).symm, congMod_one n d, congMod_one n d'⟩
  | cons t T ihT =>
    simp only [List.map_cons, List.prod_cons]
    refine crtProd_mul n d d' _ _ ?_ ihT
    obtain ⟨i, j, hij, c⟩ := t
    have ht : TransvectionStruct.toSpecialLinearGroup ⟨i, j, hij, c⟩ =
        SpecialLinearGroup.transvection hij c := Subtype.ext (rfl)
    rw [ht]
    exact transvection_CRT n d d' hcop hij c

end Matrix.SpecialLinearGroup
