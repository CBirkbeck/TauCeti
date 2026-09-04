/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimePower

/-!
# Scalar multiplication in the `Γ₀(N)` Hecke ring

The scalar row of the multiplication table at level `N`: `T(c, c) · T(b₁, b₂) = T(cb₁, cb₂)`,
and its consequence for the scalar operator, `S_m · S_n = S_{mn}`.

`diag(c, c)` is central, so its `Γ₀(N)`-double coset is a single right coset
(`degree_diagCosetGamma0_const`) and the convolution has one term with structure constant `1`.
This is the level-`N` analogue of `HeckeRing.GLn.diagElem_const_mul`; the structure-constant
computation itself is the generic `HeckeCosetModule.mul_single_single_of_mulMap_eq`, which is
stated for an arbitrary Hecke triple and so applies to `Δ₀(N)` unchanged. Only the two
hypotheses it takes are level-dependent.

`HeckeCosetModule.single_mul_single_of_mem_normalizer` is the shorter route to `S_m · S_n`
alone, both scalars being central. It does not reach `diagElemGamma0_const_mul`, which is the
statement proved here: `diag(b)` normalizes `Γ₀(N)` only when `b₁ = b₂`, so the general
scalar-times-diagonal product needs the one-sided argument below.

`heckeTScalarGamma0_mul` is unconditional: where a factor shares a factor with the level its
operator vanishes, and so does the operator of the product, so the degenerate branches agree
without a coprimality hypothesis. That is what lets `Composite.lean` identify the assembled
scalar family with this one at every nonzero index.

## Main results

* `HeckeRing.GL2.diagElemGamma0_const_mul`: `T(c, c) · T(b) = T(c·b)` at level `N`.
* `HeckeRing.GL2.heckeTScalarGamma0_mul`: `S_m · S_n = S_{mn}`, for all `m` and `n`.
* `HeckeRing.GL2.heckeTScalarGamma0_pow`: `S_p ^ v = S_{p^v}`, its iterate.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.17.
-/

public section

open Matrix HeckeRing DoubleCoset Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn
open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ) [NeZero N]

/-- Every pair in the coset decomposition of `T(c, c) · T(b)` multiplies into the single double
coset of `diag(c·b)`. One of the two hypotheses of the structure-constant criterion. -/
private lemma mulMap_const_eq (c : ℕ) (hc : 0 < c) (hcN : Nat.Coprime c N) (b : Fin 2 → ℕ)
    (hb : ∀ i, 0 < b i) (hbN : Nat.Coprime (b 0) N)
    (hcb : Nat.Coprime (((fun _ : Fin 2 ↦ c) * b) 0) N)
    (p : DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
        (((diagCosetGamma0 N (fun _ ↦ c) fun _ ↦ hcN).rep : GL (Fin 2) ℚ)) ×
      DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
        (((diagCosetGamma0 N b fun _ ↦ hbN).rep : GL (Fin 2) ℚ))) :
    HeckeCoset.mulMap ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) (diagCosetGamma0 N (fun _ ↦ c) fun _ ↦ hcN).rep
      (diagCosetGamma0 N b fun _ ↦ hbN).rep p =
      diagCosetGamma0 N ((fun _ ↦ c) * b) fun _ ↦ hcb := by
  obtain ⟨L₁, hL₁, R₁, hR₁, hα⟩ :=
    exists_rep_diagCosetGamma0_eq_mul_natDiagGL_mul N (fun _ ↦ c) fun _ ↦ hcN
  obtain ⟨L₂, hL₂, R₂, hR₂, hβ⟩ := exists_rep_diagCosetGamma0_eq_mul_natDiagGL_mul N b fun _ ↦ hbN
  have hprod : (p.1.out : GL (Fin 2) ℚ) *
      ((diagCosetGamma0 N (fun _ ↦ c) fun _ ↦ hcN).rep : GL (Fin 2) ℚ) *
      ((p.2.out : GL (Fin 2) ℚ) * ((diagCosetGamma0 N b fun _ ↦ hbN).rep : GL (Fin 2) ℚ)) =
      ((p.1.out : GL (Fin 2) ℚ) * L₁ * R₁ * p.2.out * L₂) *
        natDiagGL 2 ((fun _ ↦ c) * b) * R₂ := by
    set σ := (p.1.out : GL (Fin 2) ℚ)
    set τ := (p.2.out : GL (Fin 2) ℚ)
    rw [hα, hβ, ← natDiagGL_mul 2 _ b (fun _ ↦ hc) hb]
    calc σ * (L₁ * natDiagGL 2 (fun _ ↦ c) * R₁) * (τ * (L₂ * natDiagGL 2 b * R₂))
        = σ * L₁ * (natDiagGL 2 (fun _ ↦ c) * (R₁ * τ * L₂)) * (natDiagGL 2 b * R₂) := by
          group
      _ = σ * L₁ * ((R₁ * τ * L₂) * natDiagGL 2 (fun _ ↦ c)) * (natDiagGL 2 b * R₂) := by
          rw [natDiagGL_const_comm 2 c]
      _ = σ * L₁ * R₁ * τ * L₂ * (natDiagGL 2 (fun _ ↦ c) * natDiagGL 2 b) * R₂ := by
          group
  rw [HeckeCoset.mulMap_eq_mk]
  exact (HeckeCoset.mk_eq_mk_of_mem (mem_doubleCoset.mpr
    ⟨(p.1.out : GL (Fin 2) ℚ) * L₁ * R₁ * p.2.out * L₂,
      ((Gamma0 N).map (mapGL ℚ)).mul_mem (((Gamma0 N).map (mapGL ℚ)).mul_mem
        (((Gamma0 N).map (mapGL ℚ)).mul_mem
          (((Gamma0 N).map (mapGL ℚ)).mul_mem p.1.out.2 hL₁) hR₁) p.2.out.2) hL₂,
      R₂, hR₂, hprod⟩)).trans (diagCosetGamma0_def N _ _).symm

/-- The scalar double coset occurs at most once in any product it takes part in. The other
hypothesis of the structure-constant criterion. -/
private lemma multiplicity_const_le_one (c : ℕ) (hcN : Nat.Coprime c N) (b : Fin 2 → ℕ)
    (hbN : Nat.Coprime (b 0) N)
    (A : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))) :
    multiplicity ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ))
      (((diagCosetGamma0 N (fun _ ↦ c) fun _ ↦ hcN).rep : GL (Fin 2) ℚ))
      (((diagCosetGamma0 N b fun _ ↦ hbN).rep : GL (Fin 2) ℚ))
      ((A.rep : GL (Fin 2) ℚ)) ≤ 1 := by
  classical
  have hcard : Fintype.card (DecompQuotient ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ))
      (((diagCosetGamma0 N (fun _ ↦ c) fun _ ↦ hcN).rep : GL (Fin 2) ℚ))) = 1 := by
    rw [← HeckeCoset.degree_eq_card_decompQuotient]
    exact degree_diagCosetGamma0_const N c _
  have hsub : Subsingleton (DecompQuotient ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ))
      (((diagCosetGamma0 N (fun _ ↦ c) fun _ ↦ hcN).rep : GL (Fin 2) ℚ))) :=
    Fintype.card_le_one_iff_subsingleton.mp hcard.le
  rw [multiplicity_def, Nat.card_eq_fintype_card]
  refine Fintype.card_le_one_iff_subsingleton.mpr ?_
  constructor
  rintro ⟨⟨i₁, j₁⟩, hp₁⟩ ⟨⟨i₂, j₂⟩, hp₂⟩
  simp only [Set.mem_ofPred_eq] at hp₁ hp₂
  obtain rfl : i₁ = i₂ := Subsingleton.elim i₁ i₂
  obtain rfl : j₁ = j₂ := DoubleCoset.snd_eq_of_fst_eq hp₁ hp₂
  rfl

/-- **Scalar multiplication at level `N`**: `T(c, c) · T(b) = T(c·b)`, the level-`N` analogue of
`HeckeRing.GLn.diagElem_const_mul`. Both factors must be nondegenerate — positive and with head
entry coprime to the level — since otherwise the left side has a vanishing factor. -/
theorem diagElemGamma0_const_mul (c : ℕ) (hc : 0 < c) (hcN : Nat.Coprime c N) (b : Fin 2 → ℕ)
    (hb : ∀ i, 0 < b i) (hbN : Nat.Coprime (b 0) N) :
    diagElemGamma0 N (fun _ ↦ c) * diagElemGamma0 N b = diagElemGamma0 N ((fun _ ↦ c) * b) := by
  have hcb : Nat.Coprime (((fun _ : Fin 2 ↦ c) * b) 0) N := Nat.coprime_mul_iff_left.mpr ⟨hcN, hbN⟩
  have hpos : ∀ i, 0 < ((fun _ : Fin 2 ↦ c) * b) i := fun i ↦ Nat.mul_pos hc (hb i)
  rw [diagElemGamma0_of_pos_of_coprime N (fun _ ↦ hc) hcN,
    diagElemGamma0_of_pos_of_coprime N hb hbN,
    diagElemGamma0_of_pos_of_coprime N hpos hcb, HeckeCosetModule.mul_def]
  exact HeckeCosetModule.mul_single_single_of_mulMap_eq ℤ _ _ _
    (mulMap_const_eq N c hc hcN b hb hbN hcb) (multiplicity_const_le_one N c hcN b hbN _)

/-- **The scalar operator is multiplicative**: `S_m · S_n = S_{mn}`, with no hypothesis on `m`
or `n`. Where either index is zero or shares a factor with the level its operator vanishes, and
so does the operator of the product, so the degenerate branches agree too. -/
@[simp]
theorem heckeTScalarGamma0_mul (m n : ℕ) :
    heckeTScalarGamma0 N m * heckeTScalarGamma0 N n = heckeTScalarGamma0 N (m * n) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  by_cases hmN : Nat.Coprime m N
  · by_cases hnN : Nat.Coprime n N
    · have h : (fun _ : Fin 2 ↦ m) * ![n, n] = ![m * n, m * n] := by
        ext i; fin_cases i <;> simp
      rw [heckeTScalarGamma0_def, heckeTScalarGamma0_def, heckeTScalarGamma0_def,
        show (![m, m] : Fin 2 → ℕ) = fun _ ↦ m from by ext i; fin_cases i <;> rfl,
        diagElemGamma0_const_mul N m hm hmN ![n, n]
          (by intro i; fin_cases i <;> simpa using hn) (by simpa using hnN), h]
    · rw [heckeTScalarGamma0_of_not_coprime N hnN, mul_zero]
      exact (heckeTScalarGamma0_of_not_coprime N fun h ↦
        hnN (Nat.Coprime.coprime_dvd_left (dvd_mul_left n m) h)).symm
  · rw [heckeTScalarGamma0_of_not_coprime N hmN, zero_mul]
    exact (heckeTScalarGamma0_of_not_coprime N fun h ↦
      hmN (Nat.Coprime.coprime_dvd_left (dvd_mul_right m n) h)).symm

/-- **The scalar operator on a prime power**: `S_p ^ v = S_{p^v}`, the iterate of
`heckeTScalarGamma0_mul`. At `v = 0` both sides are the identity. -/
@[simp]
theorem heckeTScalarGamma0_pow (p v : ℕ) :
    heckeTScalarGamma0 N p ^ v = heckeTScalarGamma0 N (p ^ v) := by
  induction v with
  | zero => simp
  | succ v ih => rw [pow_succ, ih, heckeTScalarGamma0_mul, ← pow_succ]

end HeckeRing.GL2

end
