/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.PolynomialRing.Basic

public section

/-!
# `pLocalSubring` is a polynomial ring for `n = 1, 2`

The injectivity half of **Shimura's Theorem 3.20** and the resulting isomorphism
`ℤ[X₁, …, Xₙ] ≃+* pLocalSubring`, for `n = 1` and `n = 2`. The generators and the surjectivity half
are in `PolynomialRing/Basic.lean`.

Injectivity is proved by a determinant/leading-term argument: the determinant of a double
coset representative is multiplicative, so a monomial in the generators has a predictable
leading elementary-divisor vector, and distinct monomials have distinct leading terms.

## Main results

* `HeckeRing.GLn.Inj.evalHom_one_injective`, `HeckeRing.GLn.Inj.evalHom_two_injective`:
  evaluation at the generators is injective for `n = 1` and `n = 2`.
* `HeckeRing.GLn.polynomialRingEquivOne`, `HeckeRing.GLn.polynomialRingEquivTwo`:
  **Shimura, Theorem 3.20** for `n = 1` and `n = 2` — `pLocalSubring ≅ ℤ[X₁, …, Xₙ]`.

## Implementation notes

The source states Theorem 3.20 at general `n`, dispatching on `n = 1` and `n = 2` and
leaving the remaining case as a gap. Here the two proved cases are stated directly, so
nothing rests on an unformalised step.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), the `Inj` section.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2, Theorem 3.20.
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn.Inj

open HeckeRing.GLn HeckeRing.GL2

/-- The `CommSemiring` structure this module needs on `IntegralHeckeRing n`, rebuilt locally
from `HeckeCosetModule.instSemiringHeckeRing` and `HeckeCosetModule.mul_comm_of_antiInvolution`.

`PolynomialRing/Basic.lean` carries the same reconstruction, but as a `local instance`, which
does not cross the module boundary; and `commSemiringIntegralHeckeRing` is a sealed `def`, so
registering it for typeclass search does not make its body reduce to the ambient
`NonAssocSemiring`. Writing the structure here makes it transparent exactly where this file
needs it, leaving the upstream definitions sealed for every other consumer. -/
noncomputable local instance commSemiringIntegralHeckeRingLocal (n : ℕ) [NeZero n] :
    CommSemiring (IntegralHeckeRing n) :=
  { (HeckeCosetModule.instSemiringHeckeRing ℤ : Semiring (IntegralHeckeRing n)) with
    mul_comm := HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution n)
      (transposeAntiInvolution_onHeckeCoset_eq_self n) }

/-- The product of two diagonal basis elements, unfolded: it is the structure-constant family
of their representatives. The `b₁ = b₂ = 1` case of `HeckeCosetModule.single_mul`.

Kept here rather than beside either parent. It needs `diagElem`, from
`GLn/DiagonalCosets.lean`, *and* `HeckeCosetModule.single_mul`, from the abstract Hecke-ring
layer; neither of those files can see the other's contents, and this is the first module
downstream of both. Moving it either way would mean widening a core file's imports for a
single lemma. -/
private lemma diagElem_mul_diagElem (a b : Fin 2 → ℕ) :
    diagElem a * diagElem b =
      HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
        (diagCoset a).rep (diagCoset b).rep := by
  rw [diagElem_def, diagElem_def, HeckeCosetModule.mul_def, HeckeCosetModule.single_mul]
  -- `rw` cannot match a `Finsupp` lemma through the `HeckeCosetModule` wrapper, so the
  -- summation equation is supplied as a term
  have h := HeckeCosetModule.sum_single_index (R := ℤ) (D := diagCoset b) (b := (1 : ℤ))
    (F := fun D₂ b₂ ↦ (1 : ℤ) • b₂ • HeckeCosetModule.structureConstants ℤ (SLnZ 2)
      (SLnZ 2) (SLnZ 2) (diagCoset a).rep D₂.rep) (by simp)
  exact h.trans (by simp)

/-- For n=1, `heckeGen(0)^k = diagElem(fun _ => p^k)`. -/
private lemma heckeGen_pow_one (p : ℕ) (hp : 0 < p) (k : ℕ) :
    heckeGen 1 p (0 : Fin 1) ^ k = diagElem (fun _ : Fin 1 ↦ p ^ k) := by
  rw [show heckeGen 1 p (0 : Fin 1) = diagElem (fun _ : Fin 1 ↦ p) from by
    rw [heckeGen_def]; exact congrArg diagElem (heckeGenDiag_one_eq_const p)]
  exact diagElem_const_pow 1 p hp k

/-- An integer scalar times the basis element `diagElem a` is the single `Finsupp` at
`diagCoset a` with that coefficient. -/
private lemma intCast_mul_diagElem_eq_single {n : ℕ} [NeZero n] (a : Fin n → ℕ) (c : ℤ) :
    (Int.castRingHom (IntegralHeckeRing n)) c * diagElem a =
      HeckeCosetModule.single ℤ (diagCoset a) c := by
  rw [show (Int.castRingHom (IntegralHeckeRing n)) c = c • (1 : IntegralHeckeRing n) from by
      rw [zsmul_eq_mul, mul_one]; rfl, smul_mul_assoc, one_mul, diagElem_def]
  exact HeckeCosetModule.smul_single_one ℤ (diagCoset a) c

/-- For `n = 1` and `p` prime, the cosets `diagCoset (fun _ => p^k)` are injective in `k`:
if they coincide for `b 0` and `s 0`, then `b 0 = s 0`. -/
private lemma T_diag_one_ppow_inj (p : ℕ) (hp : 1 < p) {b s : Fin 1 →₀ ℕ}
    (hb : (diagCoset (n := 1) (fun _ ↦ p ^ b 0) : HeckeCoset (posDetInt 1) (SLnZ 1) (SLnZ 1)) =
      diagCoset (fun _ ↦ p ^ s 0)) : b 0 = s 0 := by
  -- each diagonal here is constant, so the chain condition is `isDvdChain_const`
  have hdiv : ∀ c : Fin 1 →₀ ℕ, IsDvdChain (fun _ : Fin 1 ↦ p ^ c 0) :=
    fun c ↦ isDvdChain_const 1 (p ^ c 0)
  have hpos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one hp.le
  have heq := eq_of_diagCoset_eq (fun _ ↦ Nat.pow_pos hpos)
    (fun _ ↦ Nat.pow_pos hpos) (hdiv b) (hdiv s) hb
  exact Nat.pow_right_injective hp (congr_fun heq 0)

/-- n=1: evalHom is injective. Different monomials map to distinct basis elements,
    so the images are ℤ-linearly independent. -/
theorem evalHom_one_injective (p : ℕ) (hp : 1 < p) : Function.Injective (evalHom 1 p) := by
  intro P Q hPQ
  rw [← sub_eq_zero]
  set R := P - Q
  have hR : evalHom 1 p R = 0 := by simp [R, map_sub, hPQ]
  by_contra hne
  obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hne
  have hcoeff : R.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  set D := diagCoset (n := 1) (fun _ ↦ p ^ (s 0))
  have h0 : (evalHom 1 p R).toFun D = 0 := by rw [hR]; rfl
  apply hcoeff
  suffices h : ((evalHom 1 p) R).toFun D = MvPolynomial.coeff s R from h ▸ h0
  rw [evalHom_def]
  change Finsupp.toFun (MvPolynomial.eval₂Hom (Int.castRingHom (IntegralHeckeRing 1))
    (fun k ↦ heckeGen 1 p k) R) D = _
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', Fin.prod_univ_one]
  have h_sum_eq : (∑ x ∈ R.support,
      (Int.castRingHom (IntegralHeckeRing 1)) (MvPolynomial.coeff x R) * heckeGen 1 p 0 ^ x 0) =
    (∑ x ∈ R.support, HeckeCosetModule.single ℤ
      (diagCoset (n := 1) (fun _ ↦ p ^ x 0)) (MvPolynomial.coeff x R)) :=
    Finset.sum_congr rfl (fun x _ ↦ by
      rw [heckeGen_pow_one p (Nat.lt_of_lt_of_le Nat.zero_lt_one hp.le)]
      exact intCast_mul_diagElem_eq_single (n := 1) (fun _ ↦ p ^ x 0) (R.coeff x))
  change (∑ x ∈ R.support,
      (Int.castRingHom (IntegralHeckeRing 1)) (MvPolynomial.coeff x R) * heckeGen 1 p 0 ^ x 0)
        D = MvPolynomial.coeff s R
  rw [h_sum_eq]
  -- `HeckeCosetModule` is a `Finsupp` by definition, so evaluation commutes with the sum;
  -- `rw` cannot match through the definition, but the lemma applies by defeq
  have happ : (∑ x ∈ R.support, HeckeCosetModule.single ℤ
        (diagCoset (n := 1) (fun _ ↦ p ^ x 0)) (MvPolynomial.coeff x R)) D =
      ∑ x ∈ R.support, HeckeCosetModule.single ℤ
        (diagCoset (n := 1) (fun _ ↦ p ^ x 0)) (MvPolynomial.coeff x R) D :=
    Finsupp.finsetSum_apply _ _ _
  rw [happ]
  classical
  simp only [HeckeCosetModule.single_apply, D]
  rw [Finset.sum_eq_single s (fun b _ hbs ↦ if_neg (fun hb ↦ hbs
    (Finsupp.ext (fun j ↦ by rw [Fin.fin_one_eq_zero j]; exact T_diag_one_ppow_inj p hp hb))))
    (fun hns ↦ absurd hs hns)]
  simp

/-- A two-entry diagonal `![a, b]` is a divisibility chain iff `a ∣ b`. -/
private lemma divChain_two_of_dvd {a b : ℕ} (hab : a ∣ b) :
    IsDvdChain (![a, b] : Fin 2 → ℕ) :=
  isDvdChain_iff.mpr fun i j hij ↦ by
    fin_cases i <;> fin_cases j <;> simp_all

/-- Determinant of an SL_n(ℤ) element embedded in GL_n(ℚ) is 1. -/
private lemma det_SLnZ_eq_one {g : GL (Fin 2) ℚ} (hg : g ∈ SLnZ 2) :
    (↑g : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
  obtain ⟨σ, rfl⟩ := (mem_SLnZ_iff 2).mp hg
  -- the entries are integers cast into ℚ, so the determinant is the cast of `det σ = 1`
  have h : (mapGL ℚ σ : Matrix (Fin 2) (Fin 2) ℚ) = (Int.castRingHom ℚ).mapMatrix σ.val := by
    simp [mapGL_coe_matrix]
  rw [h, ← RingHom.map_det]
  simp

/-- Elements in the same SL_n double coset have the same determinant. -/
private lemma det_doubleCoset_eq {g₁ g₂ : posDetInt 2}
    (h : HeckeCoset.mk (SLnZ 2) (SLnZ 2) g₁ = HeckeCoset.mk (SLnZ 2) (SLnZ 2) g₂) :
    (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (↑(↑g₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [HeckeCoset.eq_iff] at h
  have hg₁_mem : (g₁ : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (g₂ : GL (Fin 2) ℚ) (SLnZ 2) (SLnZ 2) := by
    rw [← h]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := DoubleCoset.mem_doubleCoset.mp hg₁_mem
  have : (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (h₁ * (↑g₂ : GL (Fin 2) ℚ) * h₂).1.det := by rw [heq]
  simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul, det_SLnZ_eq_one hh₁,
    det_SLnZ_eq_one hh₂, one_mul, mul_one] at this
  exact this

/-- The diagonal product of rep(diagCoset a) equals ∏ a. -/
private lemma prod_rep_T_diag (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(↑(HeckeCoset.rep (diagCoset a)) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      ∏ i, (a i : ℚ) := by
  -- the representative and the explicit diagonal matrix lie in the same double coset
  have h_eq : HeckeCoset.mk (SLnZ 2) (SLnZ 2) (HeckeCoset.rep (diagCoset a)) =
      HeckeCoset.mk (SLnZ 2) (SLnZ 2) ⟨natDiagGL 2 a, natDiagGL_mem_posDetInt 2 a⟩ := by
    rw [HeckeCoset.mk_rep, diagCoset_def]
  exact (det_doubleCoset_eq h_eq).trans (natDiagGL_det 2 a ha)

/-- Every coset in the support of a mulMap output has determinant = det(g₁) * det(g₂). -/
private lemma det_mulMap_eq (g₁ g₂ : posDetInt 2)
    (p : DecompQuotient (SLnZ 2) (SLnZ 2) (g₁ : GL (Fin 2) ℚ) ×
      DecompQuotient (SLnZ 2) (SLnZ 2) (g₂ : GL (Fin 2) ℚ)) :
    (↑(↑(HeckeCoset.rep (HeckeCoset.mulMap (SLnZ 2) (SLnZ 2) (SLnZ 2) g₁ g₂ p)) : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ).det =
      (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det *
        (↑(↑g₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  -- `mulMap` names the double coset of the explicit product `σ g₁ τ g₂`
  have h_eq := (HeckeCoset.mk_rep
      (HeckeCoset.mulMap (SLnZ 2) (SLnZ 2) (SLnZ 2) g₁ g₂ p)).trans
    (HeckeCoset.mulMap_eq_mk (SLnZ 2) (SLnZ 2) (SLnZ 2) g₁ g₂ p)
  rw [det_doubleCoset_eq h_eq]
  simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul]
  have h1 := det_SLnZ_eq_one (p.1.out.2)
  have h2 := det_SLnZ_eq_one (p.2.out.2)
  rw [h1, h2]; ring

/-- If `D'` appears in the support of `m(rep D₁, rep D₂)`, then the determinant of its
representative is the product of the determinants of `rep D₁` and `rep D₂`. -/
private lemma det_rep_eq_mul_of_m_ne_zero (D₁ D₂ D' : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    (hm : (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
      (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D' ≠ 0) :
    (↑(↑(HeckeCoset.rep D') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (↑(↑(HeckeCoset.rep D₁) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det *
        (↑(↑(HeckeCoset.rep D₂) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  classical
  rw [HeckeCosetModule.structureConstants_apply] at hm
  -- a nonzero structure constant means `D'` is hit by `mulMap`
  have hD'_mem : D' ∈ Finset.univ.image
      (HeckeCoset.mulMap (SLnZ 2) (SLnZ 2) (SLnZ 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) :=
    (HeckeCoset.mem_image_mulMap_iff _ _ _).mpr (Nat.cast_ne_zero.mp hm)
  rw [Finset.mem_image] at hD'_mem
  obtain ⟨p, _, hD'_eq⟩ := hD'_mem
  rw [← hD'_eq]; exact det_mulMap_eq (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) p

/-- Determinant tracking: if `f` is supported on cosets of determinant `q^{a₀}`, then
`heckeGen(q,0)^{b₀} · f` is supported on cosets of determinant `q^{b₀ + a₀}`. -/
private lemma det_rep_T_gen_zero_pow_mul (q : {p : ℕ // p.Prime}) (a₀ b₀ : ℕ)
    (f : IntegralHeckeRing 2) (D' : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    (hf_det : ∀ D'', f D'' ≠ 0 →
      (↑(↑(HeckeCoset.rep D'') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = ↑(q.1 ^ a₀ : ℕ))
    (hD' : (heckeGen 2 q.1 0 ^ b₀ * f) D' ≠ 0) :
    (↑(↑(HeckeCoset.rep D') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      ↑(q.1 ^ (b₀ + a₀) : ℕ) := by
  induction b₀ generalizing f D' with
  | zero =>
    rw [pow_zero, one_mul] at hD'
    simpa only [Nat.zero_add] using hf_det D' hD'
  | succ n ih =>
    rw [pow_succ', mul_assoc] at hD'
    set g' := heckeGen 2 q.1 0 ^ n * f
    rw [show heckeGen 2 q.1 0 = HeckeCosetModule.single ℤ (diagCoset (![1, q.1])) 1 from by
        rw [heckeGen_def, diagElem_def]
        exact congrArg (fun a ↦ HeckeCosetModule.single ℤ (diagCoset a) 1)
          (funext fun i ↦ by fin_cases i <;> simp [heckeGenDiag_apply])] at hD'
    obtain ⟨D₂, hD₂_mem, hD₂_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by
      rw [show (HeckeCosetModule.single ℤ (diagCoset (![1, q.1])) 1 * g') D' =
          ∑ D₂ ∈ g'.support, g' D₂ *
            (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (HeckeCoset.rep (diagCoset (![1, q.1]))) (HeckeCoset.rep D₂)) D' from by
          rw [HeckeCosetModule.mul_def, HeckeCosetModule.single_mul,
            HeckeCosetModule.sum_apply, HeckeCosetModule.sum_def]
          simp only [HeckeCosetModule.smul_apply, one_mul]] at hD'
      exact hD')
    have hm_ne : (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
        (HeckeCoset.rep (diagCoset (![1, q.1])))
        (HeckeCoset.rep D₂)) D' ≠ 0 := fun h ↦ hD₂_ne (by rw [h, mul_zero])
    rw [det_rep_eq_mul_of_m_ne_zero _ _ _ hm_ne,
      show (↑(↑(HeckeCoset.rep (diagCoset (![1, q.1]))) : GL (Fin 2) ℚ) :
          Matrix (Fin 2) (Fin 2) ℚ).det = (q.1 : ℚ) from by
        rw [prod_rep_T_diag (![1, q.1]) (fun i ↦ by fin_cases i <;> simp [q.2.pos])]
        simp [Fin.prod_univ_two],
      ih f D₂ hf_det (Finsupp.mem_support_iff.mp hD₂_mem)]
    push_cast; ring

/-- Every double coset in the support of `T(1,q)^{e₀} · T(q,q)^{e₁}` is a diagonal coset
`T(a)` for a positive divisibility chain `a`, whose entry product — the determinant of any
representative — is `q^(e₀ + 2·e₁)`.

This is what makes the exponent pair recoverable: the determinant pins `e₀ + 2·e₁`, and the
elementary-divisor order then separates the individual exponents. -/
private lemma T_gen_pow_support_qpower (q : {p : ℕ // p.Prime}) (e : Fin 2 → ℕ)
    (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    (hD : (heckeGen 2 q.1 0 ^ (e 0) * heckeGen 2 q.1 1 ^ (e 1)) D ≠ 0) :
    ∃ a : Fin 2 → ℕ, D = diagCoset a ∧ (∀ i, 0 < a i) ∧ IsDvdChain a ∧
      (∏ i, a i) = q.1 ^ (e 0 + 2 * e 1) := by
  obtain ⟨a, ha_pos, ha_div, hD_eq⟩ := exists_diagonal_representative D
  refine ⟨a, hD_eq, ha_pos, ha_div, ?_⟩
  have hf_det : ∀ D'', (heckeGen 2 q.1 1 ^ (e 1)) D'' ≠ 0 →
      (↑(↑(HeckeCoset.rep D'') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
        ↑(q.1 ^ (2 * e 1) : ℕ) := by
    classical
    intro D'' hD''
    rw [heckeGen_one_eq_heckeTScalar q.1 q.2.pos,
      HeckeRing.GL2.heckeTScalar_pow q.1 q.2.pos (e 1)] at hD''
    have h_eq : diagCoset (fun _ : Fin 2 ↦ q.1 ^ (e 1)) = D'' := by
      by_contra h
      exact hD'' (by rw [diagElem_def, HeckeCosetModule.single_apply, if_neg h])
    rw [← h_eq, prod_rep_T_diag _ (fun i ↦ by fin_cases i <;> simp [pow_pos q.2.pos])]
    push_cast [Fin.prod_univ_two, ← pow_add]; ring_nf
  have h_result := det_rep_T_gen_zero_pow_mul q (2 * e 1) (e 0) _ D hf_det hD
  rw [hD_eq, prod_rep_T_diag a ha_pos] at h_result
  exact mod_cast h_result

/-- Every coset in the support of `heckeGen(q,0)^a * heckeGen(q,1)^b` has entries
that are powers of `q` (immediate from `T_gen_pow_support_qpower`). -/
private lemma T_gen_pow_entries_qpower (q : {p : ℕ // p.Prime})
    (e : Fin 2 → ℕ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    (hD : (heckeGen 2 q.1 0 ^ (e 0) * heckeGen 2 q.1 1 ^ (e 1)) D ≠ 0)
    (a : Fin 2 → ℕ) (ha : D = diagCoset a) (ha_pos : ∀ i, 0 < a i)
    (ha_div : IsDvdChain a) :
    ∀ p : ℕ, p.Prime → p ≠ q.1 → ∀ i, ¬(p ∣ a i) := by
  obtain ⟨a', rfl, ha'_pos, ha'_div, ha'_det⟩ := T_gen_pow_support_qpower q e D hD
  have ha_eq := eq_of_diagCoset_eq ha_pos ha'_pos ha_div ha'_div ha.symm
  subst ha_eq
  intro p hp hpq i h_dvd
  have : p ∣ ∏ j, a j := dvd_trans h_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  rw [ha'_det] at this
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.2).mp (hp.dvd_of_dvd_pow this))

/-- `T_single(diagCoset a, α) * diagElem(c,c) = T_single(diagCoset(a * c), α)`. -/
private lemma T_single_diag_mul_T_scalar (c : ℕ) (hc : 0 < c)
    (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i) (α : ℤ) :
    HeckeCosetModule.single ℤ (diagCoset a) α * diagElem (fun _ : Fin 2 ↦ c) =
    HeckeCosetModule.single ℤ (diagCoset (a * (fun _ : Fin 2 ↦ c))) α := by
  have h_single : HeckeCosetModule.single ℤ (diagCoset a) α =
      α • diagElem a := by
    -- `diagElem` is sealed, so `show` cannot see through it; `diagElem_def` is the bridge.
    rw [diagElem_def]
    exact (HeckeCosetModule.smul_single_one ℤ (diagCoset a) α).symm
  rw [h_single, smul_mul_assoc, diagElem_mul_const 2 a ha_pos c hc, diagElem_def]
  exact HeckeCosetModule.smul_single_one ℤ (diagCoset (a * fun _ ↦ c)) α

/-- Scalar shift identity: for any `f : IntegralHeckeRing 2`, scalar `c > 0`, and positive
divisibility-chain `b`, evaluating `f * diagElem(c,c)` at `diagCoset(b * c)` equals
`f(diagCoset b)`. -/
private lemma T_mul_T_scalar_eval_shifted (c : ℕ) (hc : 0 < c) (f : IntegralHeckeRing 2)
    (b : Fin 2 → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb_div : IsDvdChain b) :
    (f * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset (b * (fun _ : Fin 2 ↦ c))) = f (diagCoset b) := by
  classical
  induction f using HeckeCosetModule.induction_linear with
  | h0 =>
    change ((0 : IntegralHeckeRing 2) * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset (b * fun _ ↦ c)) =
      (0 : IntegralHeckeRing 2) (diagCoset b)
    rw [zero_mul]; rfl
  | hadd g h ihg ihh =>
    set g' : IntegralHeckeRing 2 := g
    set h' : IntegralHeckeRing 2 := h
    change ((g' + h') * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset (b * fun _ ↦ c)) =
      (g' + h') (diagCoset b)
    rw [add_mul,
      show (g' * diagElem (fun _ : Fin 2 ↦ c) + h' * diagElem (fun _ : Fin 2 ↦ c))
            (diagCoset (b * fun _ ↦ c)) =
            (g' * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset (b * fun _ ↦ c)) +
            (h' * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset (b * fun _ ↦ c)) from
        Finsupp.add_apply _ _ _,
      show (g' + h') (diagCoset b) = g' (diagCoset b) + h' (diagCoset b) from
        Finsupp.add_apply _ _ _,
      ihg, ihh]
  | hsingle D α =>
    obtain ⟨a, ha_pos, ha_div, hD_eq⟩ := exists_diagonal_representative D
    rw [hD_eq, T_single_diag_mul_T_scalar c hc a ha_pos α]
    rw [HeckeCosetModule.single_apply, HeckeCosetModule.single_apply]
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, if_pos rfl]
    · have h_ne_1 : diagCoset (a * fun _ : Fin 2 ↦ c) ≠ diagCoset (b * fun _ : Fin 2 ↦ c) := by
        intro heq
        have h1_eq : a * (fun _ : Fin 2 ↦ c) = b * (fun _ : Fin 2 ↦ c) :=
          eq_of_diagCoset_eq (fun i ↦ Nat.mul_pos (ha_pos i) hc)
            (fun i ↦ Nat.mul_pos (hb_pos i) hc) (isDvdChain_mul_const 2 ha_div c)
            (isDvdChain_mul_const 2 hb_div c) heq
        apply hab
        funext i
        have := congr_fun h1_eq i
        simp only [Pi.mul_apply] at this
        exact Nat.eq_of_mul_eq_mul_right hc this
      have h_ne_2 : diagCoset a ≠ diagCoset b := fun heq ↦ hab
        (eq_of_diagCoset_eq ha_pos hb_pos ha_div hb_div heq)
      rw [if_neg h_ne_1, if_neg h_ne_2]

/-- If `c ∤ d i` for some `i`, the evaluation of `f * diagElem(c,c)` at `diagCoset d` is zero. -/
private lemma T_mul_T_scalar_eval_zero_of_not_dvd (c : ℕ) (hc : 0 < c) (f : IntegralHeckeRing 2)
    (d : Fin 2 → ℕ)
    (hd_pos : ∀ i, 0 < d i) (hd_div : IsDvdChain d) (i₀ : Fin 2) (hi₀ : ¬ c ∣ d i₀) :
    (f * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset d) = 0 := by
  classical
  induction f using HeckeCosetModule.induction_linear with
  | h0 =>
    change ((0 : IntegralHeckeRing 2) * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset d) = 0
    rw [zero_mul]; rfl
  | hadd g h ihg ihh =>
    set g' : IntegralHeckeRing 2 := g
    set h' : IntegralHeckeRing 2 := h
    change ((g' + h') * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset d) = 0
    rw [add_mul,
      show (g' * diagElem (fun _ : Fin 2 ↦ c) + h' * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset d) =
            (g' * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset d) +
            (h' * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset d) from Finsupp.add_apply _ _ _,
      ihg, ihh, add_zero]
  | hsingle D α =>
    obtain ⟨a, ha_pos, ha_div, hD_eq⟩ := exists_diagonal_representative D
    rw [hD_eq, T_single_diag_mul_T_scalar c hc a ha_pos α]
    rw [HeckeCosetModule.single_apply]
    have h_ne : diagCoset (a * fun _ : Fin 2 ↦ c) ≠ diagCoset d := by
      intro heq
      have h_eq : a * (fun _ : Fin 2 ↦ c) = d :=
        eq_of_diagCoset_eq (fun i ↦ Nat.mul_pos (ha_pos i) hc) hd_pos
          (isDvdChain_mul_const 2 ha_div c) hd_div heq
      apply hi₀
      have := congr_fun h_eq i₀
      simp only [Pi.mul_apply] at this
      exact ⟨a i₀, by linarith [this.symm]⟩
    rw [if_neg h_ne]

/-- For `i ≥ 1`, evaluation of `f * heckeTScalar(p)^i` at `diagCoset ![1, k]` is zero
(since `p^i ∤ 1`). -/
private lemma T_mul_T_pp_pow_eval_at_one_zero (p : ℕ) (hp : p.Prime) (i k : ℕ) (hi : 1 ≤ i)
    (hk : 0 < k) (f : IntegralHeckeRing 2) :
    (f * heckeTScalar p ^ i) (diagCoset (![1, k] : Fin 2 → ℕ)) = 0 := by
  rw [HeckeRing.GL2.heckeTScalar_pow p hp.pos i]
  apply T_mul_T_scalar_eval_zero_of_not_dvd (p^i) (pow_pos hp.pos i) f
    (![1, k] : Fin 2 → ℕ) (fun idx ↦ by fin_cases idx <;> simp [hk])
    (divChain_two_of_dvd (one_dvd k)) 0
  simp only [Matrix.cons_val_zero]
  intro hdvd
  have hle : p ^ i ≤ 1 := Nat.le_of_dvd Nat.one_pos hdvd
  have hge : p ≤ p ^ i := Nat.le_self_pow (by omega) p
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- `diagElem ![p^i, p^j] = heckeTDiag(1, p^{j-i}) * heckeTScalar(p)^i` for `i ≤ j` with `p`
prime. -/
private lemma T_elem_ppow_factor (p : ℕ) (hp : p.Prime) (i j : ℕ) (hij : i ≤ j) :
    diagElem (![p^i, p^j] : Fin 2 → ℕ) = heckeTDiag 1 (p ^ (j - i)) * heckeTScalar p ^ i := by
  rw [heckeTDiag_eq_diagElem Nat.one_pos (pow_pos hp.pos _) (one_dvd _),
      HeckeRing.GL2.heckeTScalar_pow p hp.pos i]
  have h_ji_pos : ∀ idx : Fin 2, 0 < (![1, p^(j-i)] : Fin 2 → ℕ) idx := by
    intro idx; fin_cases idx
    · simp
    · simp [pow_pos hp.pos]
  rw [diagElem_mul_const 2 (![1, p^(j-i)] : Fin 2 → ℕ) h_ji_pos (p^i) (pow_pos hp.pos _)]
  apply congrArg diagElem
  funext idx; fin_cases idx
  · simp [Pi.mul_apply]
  · simp [Pi.mul_apply, ← pow_add]; congr 1; omega

/-- The element `T(p, pⁿ)` does not contribute at `T(1, p^{n+1})` (for `n ≥ 1`). -/
private lemma T_elem_p_ppow_eval_at_one_ppow_succ_zero (p : ℕ) (hp : p.Prime) {n : ℕ}
    (hn : n ≠ 0) :
    (diagElem (![p, p ^ n] : Fin 2 → ℕ)) (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 0 := by
  classical
  rw [diagElem_def, HeckeCosetModule.single_apply]
  refine if_neg (fun heq ↦ ?_)
  have h_eq : (![p, p ^ n] : Fin 2 → ℕ) = (![1, p ^ (n + 1)] : Fin 2 → ℕ) :=
    eq_of_diagCoset_eq (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
      (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
      (divChain_two_of_dvd (dvd_pow_self p hn)) (divChain_two_of_dvd (one_dvd _)) heq
  have := congr_fun h_eq 0
  simp only [Matrix.cons_val_zero] at this
  have := hp.one_lt; omega

/-- `(T(1,p) · T(1, pⁿ))` evaluated at the leading coset `T(1, p^{n+1})` equals `1`. -/
private lemma T_ad_one_p_mul_T_ad_one_ppow_eval_leading (p : ℕ) (hp : p.Prime) (n : ℕ) :
    (heckeTDiag 1 p * heckeTDiag 1 (p ^ n)) (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 1 := by
  classical
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [pow_zero, heckeTDiag_one_one, mul_one,
      heckeTDiag_eq_diagElem Nat.one_pos hp.pos (one_dvd _), diagElem_def,
      show (![1, p ^ (0 + 1)] : Fin 2 → ℕ) = (![1, p] : Fin 2 → ℕ) from by
        funext i; fin_cases i <;> simp,
      HeckeCosetModule.single_apply, if_pos rfl]
  · rw [show heckeTDiag 1 p = heckeT ⟨p, hp.pos⟩ from (heckeT_prime p hp).symm,
      heckeT_prime_mul_heckeTDiag_one_prime_pow p hp n]
    rw [show (heckeTDiag 1 (p ^ (n + 1)) + (if n = 1 then ((p : ℤ) + 1) else (p : ℤ)) •
              heckeTDiag p (p ^ n)) (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) =
          heckeTDiag 1 (p ^ (n + 1)) (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) +
            ((if n = 1 then ((p : ℤ) + 1) else (p : ℤ)) • heckeTDiag p (p ^ n))
              (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) from Finsupp.add_apply _ _ _,
      heckeTDiag_eq_diagElem Nat.one_pos (pow_pos hp.pos _) (one_dvd _),
      heckeTDiag_eq_diagElem hp.pos (pow_pos hp.pos _) (dvd_pow_self p hn)]
    rw [show (diagElem (![1, p ^ (n + 1)] : Fin 2 → ℕ))
          (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 1 from
        by rw [diagElem_def, HeckeCosetModule.single_apply, if_pos rfl]]
    rw [show ((if n = 1 then ((p : ℤ) + 1) else (p : ℤ)) • diagElem (![p, p ^ n] : Fin 2 → ℕ))
          (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) =
        (if n = 1 then ((p : ℤ) + 1) else (p : ℤ)) •
          diagElem (![p, p ^ n] : Fin 2 → ℕ) (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) from
        Finsupp.smul_apply _ _ _,
      T_elem_p_ppow_eval_at_one_ppow_succ_zero p hp hn,
      smul_zero, add_zero]

/-- A non-leading support element `D₂` of `(T(1,p))ⁿ` contributes `0` to the product
`T(1,p) · (T(1,p))ⁿ` at the leading coset `T(1, p^{n+1})`. -/
private lemma T_ad_one_p_mul_supp_ne_leading_eval_zero (p : ℕ) (hp : p.Prime) (n : ℕ)
    (D₂ : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)) (hD₂_ne_zero : ((heckeTDiag 1 p) ^ n) D₂ ≠ 0)
    (hD₂_ne : D₂ ≠ diagCoset (![1, p ^ n] : Fin 2 → ℕ)) :
    (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
      (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ)))
      (HeckeCoset.rep D₂)) (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 0 := by
  have hg_eq : (heckeTDiag 1 p) ^ n = (heckeGen 2 p 0) ^ n * (heckeGen 2 p 1) ^ 0 := by
    simp only [pow_zero, mul_one, heckeGen_zero_eq_heckeTDiag p hp.pos]
  obtain ⟨a, hDa, ha_pos, ha_div, ha_det⟩ := T_gen_pow_support_qpower ⟨p, hp⟩
      ![n, 0] D₂ (hg_eq ▸ hD₂_ne_zero)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero] at ha_det
  have ha_prod : a 0 * a 1 = p ^ n := Fin.prod_univ_two a ▸ ha_det
  obtain ⟨i, hi_le, hi_eq⟩ := (Nat.dvd_prime_pow hp).mp (ha_prod ▸ dvd_mul_right _ _)
  have ha1_eq : a 1 = p ^ (n - i) := by
    have h : p ^ i * a 1 = p ^ i * p ^ (n - i) := by
      rw [← pow_add, show i + (n - i) = n from by omega, ← ha_prod, hi_eq]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i) h
  have ha_form : a = (![p ^ i, p ^ (n - i)] : Fin 2 → ℕ) := by
    funext k; fin_cases k
    · exact hi_eq
    · exact ha1_eq
  have hi_ge : 1 ≤ i := by
    by_contra h_not
    obtain rfl : i = 0 := by omega
    exact hD₂_ne (by rw [hDa, ha_form]; simp [pow_zero])
  have hi_le_sub : i ≤ n - i := by
    have h_div := ha_form ▸ isDvdChain_iff.mp ha_div (by decide : (0 : Fin 2) ≤ 1)
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h_div
  rw [hDa, ha_form, ← diagElem_mul_diagElem]
  change (diagElem (![1, p] : Fin 2 → ℕ) * diagElem (![p^i, p^(n-i)] : Fin 2 → ℕ)) _ = 0
  rw [T_elem_ppow_factor p hp i (n - i) hi_le_sub, ← mul_assoc]
  exact T_mul_T_pp_pow_eval_at_one_zero p hp i (p ^ (n + 1)) hi_ge (pow_pos hp.pos _) _

/-- Leading coefficient of `T(1,p)^a`: `(heckeTDiag 1 p)^a` evaluated at the leading coset
`diagCoset ![1, p^a]` equals 1. -/
private lemma T_ad_one_p_pow_eval_leading (p : ℕ) (hp : p.Prime) (a : ℕ) :
    ((heckeTDiag 1 p) ^ a) (diagCoset (![1, p ^ a] : Fin 2 → ℕ)) = 1 := by
  classical
  induction a with
  | zero =>
    rw [pow_zero, pow_zero, show (![1, 1] : Fin 2 → ℕ) = (fun _ : Fin 2 ↦ 1) from by
        funext i; fin_cases i <;> rfl, ← diagElem_one]
    rw [diagElem_def, HeckeCosetModule.single_apply, if_pos rfl]
  | succ n ih =>
    rw [pow_succ']
    set g := (heckeTDiag 1 p) ^ n
    set D_target : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2) :=
      diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)
    set D_leading : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2) :=
      diagCoset (![1, p ^ n] : Fin 2 → ℕ)
    rw [show heckeTDiag 1 p = HeckeCosetModule.single ℤ (diagCoset (![1, p] : Fin 2 → ℕ)) 1 from
        (heckeTDiag_eq_diagElem Nat.one_pos hp.pos (one_dvd _)).trans (diagElem_def _),
      HeckeCosetModule.mul_def, HeckeCosetModule.single_mul]
    -- Evaluate the convolution at `D_target` in the wrapper's own vocabulary: push the
    -- evaluation in with `sum_apply` first, then let `sum_def` expose the `Finset.sum`.
    rw [HeckeCosetModule.sum_apply, HeckeCosetModule.sum_def]
    simp only [HeckeCosetModule.smul_apply, one_mul]
    have h_leading_in_supp : D_leading ∈ g.support :=
      HeckeCosetModule.mem_support_iff.mpr (ih ▸ one_ne_zero)
    rw [← Finset.sum_erase_add _ _ h_leading_in_supp]
    have h_erased : ∀ D₂ ∈ g.support.erase D_leading,
        (g D₂ • HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
          (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D₂)) D_target = 0 := by
      intro D₂ hD₂
      rw [Finset.mem_erase] at hD₂
      -- The `•` here and the one in `smul_apply` print alike but sit on different instance
      -- paths, so `rw`/`simp` cannot match it. Writing the equation out lets it elaborate
      -- with the goal's instances, and `smul_apply` then checks against it up to defeq.
      have hs : (g D₂ • HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (diagCoset (![1, p] : Fin 2 → ℕ)).rep D₂.rep) D_target =
          g D₂ * (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (diagCoset (![1, p] : Fin 2 → ℕ)).rep D₂.rep) D_target :=
        HeckeCosetModule.smul_apply _ _ _
      rw [hs]
      rw [T_ad_one_p_mul_supp_ne_leading_eval_zero p hp n D₂
        (HeckeCosetModule.mem_support_iff.mp hD₂.2) hD₂.1, mul_zero]
    have h_sum_zero :
        ∑ x ∈ g.support.erase D_leading, (g x •
          HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
          (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep x)) D_target = 0 :=
      Finset.sum_eq_zero h_erased
    -- Goal: ∑ + (g D_leading • m ...) D_target = 1
    -- Strategy: prove the leading term equals 1, then linarith with h_sum_zero
    have h_leading_eq : (g D_leading •
        HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
          (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading))
          D_target = 1 := by
      have hs : (g D_leading • HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (diagCoset (![1, p] : Fin 2 → ℕ)).rep D_leading.rep) D_target =
          g D_leading * (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (diagCoset (![1, p] : Fin 2 → ℕ)).rep D_leading.rep) D_target :=
        HeckeCosetModule.smul_apply _ _ _
      rw [hs, ih, one_mul, ← diagElem_mul_diagElem]
      rw [show diagElem (![1, p] : Fin 2 → ℕ) = heckeTDiag 1 p from
          (heckeTDiag_eq_diagElem Nat.one_pos hp.pos (one_dvd _)).symm,
        show diagElem (![1, p ^ n] : Fin 2 → ℕ) = heckeTDiag 1 (p ^ n) from
          (heckeTDiag_eq_diagElem Nat.one_pos (pow_pos hp.pos n) (one_dvd _)).symm]
      exact T_ad_one_p_mul_T_ad_one_ppow_eval_leading p hp n
    calc ∑ x ∈ g.support.erase D_leading, (g x •
          HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep x)) D_target +
          (g D_leading • HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading)) D_target
        = 0 + (g D_leading • HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
              (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading))
              D_target :=
          by rw [h_sum_zero]
      _ = (g D_leading • HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading))
            D_target :=
          zero_add _
      _ = 1 := h_leading_eq

/-- For `a₁ ≠ a₂`, evaluating `(heckeTDiag 1 p)^a₁` at the coset `T(1, p^{a₂})` gives `0`. -/
private lemma T_ad_one_p_pow_eval_at_one_ppow_of_ne (p : ℕ) (hp : p.Prime) {a₁ a₂ : ℕ}
    (ha_ne : a₁ ≠ a₂) :
    ((heckeTDiag 1 p) ^ a₁) (diagCoset (![1, p ^ a₂] : Fin 2 → ℕ)) = 0 := by
  by_contra h_ne_zero
  have hg_eq : (heckeTDiag 1 p) ^ a₁ = (heckeGen 2 p 0) ^ a₁ * (heckeGen 2 p 1) ^ 0 := by
    simp only [pow_zero, mul_one, heckeGen_zero_eq_heckeTDiag p hp.pos]
  obtain ⟨a, hDa, ha_pos, ha_div, ha_det⟩ := T_gen_pow_support_qpower ⟨p, hp⟩
      ![a₁, 0] (diagCoset (![1, p ^ a₂] : Fin 2 → ℕ)) (hg_eq ▸ h_ne_zero)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero] at ha_det
  have h_a_eq : a = (![1, p ^ a₂] : Fin 2 → ℕ) :=
    eq_of_diagCoset_eq ha_pos
      (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) ha_div
      (divChain_two_of_dvd (one_dvd _)) hDa.symm
  rw [h_a_eq, Fin.prod_univ_two] at ha_det
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at ha_det
  exact ha_ne (Nat.pow_right_injective hp.two_le ha_det.symm)

/-- `(heckeTDiag 1 p)^a₁` times the scalar `T(p^b, p^b)`, evaluated at the shifted leading coset
`T(p^b, p^{a₂+b})`, equals `(heckeTDiag 1 p)^a₁` evaluated at `T(1, p^{a₂})`. -/
private lemma T_ad_one_p_pow_mul_scalar_eval_at_one_ppow (p : ℕ) (hp : p.Prime) (a₁ a₂ b : ℕ) :
    ((heckeTDiag 1 p) ^ a₁ * diagElem (fun _ : Fin 2 ↦ p ^ b))
        (diagCoset (![p ^ b, p ^ (a₂ + b)] : Fin 2 → ℕ)) =
    ((heckeTDiag 1 p) ^ a₁) (diagCoset (![1, p ^ a₂] : Fin 2 → ℕ)) := by
  rw [show (![p ^ b, p ^ (a₂ + b)] : Fin 2 → ℕ) =
      (![1, p ^ a₂] : Fin 2 → ℕ) * (fun _ : Fin 2 ↦ p ^ b) from by
        funext i; fin_cases i
        · simp [Pi.mul_apply]
        · simp [Pi.mul_apply, pow_add]]
  exact T_mul_T_scalar_eval_shifted (p ^ b) (pow_pos hp.pos _) _ _
    (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (divChain_two_of_dvd (one_dvd _))

/-- Kronecker delta lemma: evaluating the monomial `heckeGen(p,0)^a₁ * heckeGen(p,1)^b₁` at the
diagonal coset `T(p^b₂, p^(a₂+b₂))` gives 1 iff `(a₁, b₁) = (a₂, b₂)`, and 0 otherwise,
under the hypothesis `b₂ ≤ b₁`. -/
private lemma monomial_eval_kronecker (p : ℕ) (hp : p.Prime)
    (a₁ b₁ a₂ b₂ : ℕ) (h : b₂ ≤ b₁) :
    (heckeGen 2 p 0 ^ a₁ * heckeGen 2 p 1 ^ b₁)
        (diagCoset (primePowDiag 2 p ![b₂, a₂ + b₂])) =
    if a₁ = a₂ ∧ b₁ = b₂ then 1 else 0 := by
  rw [show (primePowDiag 2 p ![b₂, a₂ + b₂] : Fin 2 → ℕ) = (![p ^ b₂, p ^ (a₂ + b₂)] : Fin 2 → ℕ)
      from by funext i; fin_cases i <;> simp [primePowDiag_apply],
    heckeGen_zero_eq_heckeTDiag p hp.pos,
    heckeGen_one_eq_heckeTScalar p hp.pos,
    HeckeRing.GL2.heckeTScalar_pow p hp.pos b₁]
  by_cases hmatch : a₁ = a₂ ∧ b₁ = b₂
  · obtain ⟨ha, hb⟩ := hmatch
    rw [if_pos ⟨ha, hb⟩, ha, ← hb, T_ad_one_p_pow_mul_scalar_eval_at_one_ppow p hp,
      T_ad_one_p_pow_eval_leading p hp a₂]
  · rw [if_neg hmatch]
    by_cases hbeq : b₁ = b₂
    · subst hbeq
      rw [T_ad_one_p_pow_mul_scalar_eval_at_one_ppow p hp,
        T_ad_one_p_pow_eval_at_one_ppow_of_ne p hp (fun heq ↦ hmatch ⟨heq, rfl⟩)]
    · have h_not_dvd : ¬ p ^ b₁ ∣ (![p ^ b₂, p ^ (a₂ + b₂)] : Fin 2 → ℕ) 0 := by
        simp only [Matrix.cons_val_zero, Nat.pow_dvd_pow_iff_le_right hp.one_lt]
        omega
      exact T_mul_T_scalar_eval_zero_of_not_dvd (p ^ b₁) (pow_pos hp.pos _) _ _
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (divChain_two_of_dvd (pow_dvd_pow p (by omega))) 0 h_not_dvd

/-- For `n = 2`, the monomial `∏ₖ heckeGen(p,k)^{d k}` over the support of `d` equals
`heckeGen(p,0)^{d 0} · heckeGen(p,1)^{d 1}` (missing factors contribute `heckeGen^0 = 1`). -/
private lemma prod_T_gen_pow_eq_two (p : ℕ) (d : Fin 2 →₀ ℕ) :
    (∏ k ∈ d.support, heckeGen 2 p k ^ d k) = heckeGen 2 p 0 ^ (d 0) * heckeGen 2 p 1 ^ (d 1) := by
  rw [Finset.prod_subset (Finset.subset_univ d.support) (fun k _ hk ↦ by
    rw [Finsupp.notMem_support_iff.mp hk, pow_zero])]
  rw [Fin.prod_univ_two]

/-- Evaluating `evalHom 2 p R` at the coset `D` expands as
`∑_{d ∈ supp R} (R.coeff d) · (heckeGen(p,0)^{d 0} · heckeGen(p,1)^{d 1}) D`. -/
private lemma evalHom_apply_eq_sum_monomial (p : ℕ) (R : MvPolynomial (Fin 2) ℤ)
    (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)) :
    (evalHom 2 p R) D =
    ∑ d ∈ R.support, R.coeff d * (heckeGen 2 p 0 ^ (d 0) * heckeGen 2 p 1 ^ (d 1)) D := by
  rw [evalHom_def]
  change (MvPolynomial.eval₂ (Int.castRingHom (IntegralHeckeRing 2))
    (fun k : Fin 2 ↦ heckeGen 2 p k) R) D = _
  rw [MvPolynomial.eval₂_eq]
  change (∑ d ∈ R.support, (Int.castRingHom (IntegralHeckeRing 2)) (MvPolynomial.coeff d R) *
    ∏ i ∈ d.support, heckeGen 2 p i ^ d i) D = _
  rw [show (∑ d ∈ R.support, (Int.castRingHom (IntegralHeckeRing 2)) (MvPolynomial.coeff d R) *
        ∏ i ∈ d.support, heckeGen 2 p i ^ d i) D =
      ∑ d ∈ R.support, ((Int.castRingHom (IntegralHeckeRing 2)) (MvPolynomial.coeff d R) *
        ∏ i ∈ d.support, heckeGen 2 p i ^ d i) D from Finset.sum_apply' _]
  refine Finset.sum_congr rfl (fun d _ ↦ ?_)
  change (((R.coeff d : ℤ) : IntegralHeckeRing 2) * (∏ k ∈ d.support, heckeGen 2 p k ^ d k)) D = _
  rw [show ((R.coeff d : ℤ) : IntegralHeckeRing 2) = (R.coeff d) • (1 : IntegralHeckeRing 2) from
    (zsmul_one _).symm, smul_mul_assoc, one_mul]
  rw [show ((R.coeff d) • (∏ k ∈ d.support, heckeGen 2 p k ^ d k : IntegralHeckeRing 2)) D =
    R.coeff d • (∏ k ∈ d.support, heckeGen 2 p k ^ d k : IntegralHeckeRing 2) D from
    Finsupp.smul_apply _ _ _, smul_eq_mul, prod_T_gen_pow_eq_two]

/-- n=2: evalHom is injective. -/
theorem evalHom_two_injective (p : ℕ) (hp : p.Prime) :
    Function.Injective (evalHom 2 p) := by
  intro P Q hPQ
  rw [← sub_eq_zero]; set R := P - Q
  have hR : evalHom 2 p R = 0 := by simp [R, map_sub, hPQ]
  by_contra hR_ne
  obtain ⟨s, hs_mem, hs_min⟩ := Finset.exists_min_image R.support
    (fun d : Fin 2 →₀ ℕ ↦ d 1) (MvPolynomial.support_nonempty.mpr hR_ne)
  have hs_coeff : R.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs_mem
  have h_zero : (evalHom 2 p R) (diagCoset (primePowDiag 2 p ![s 1, s 0 + s 1])) = 0 := by
    rw [hR]; rfl
  rw [evalHom_apply_eq_sum_monomial] at h_zero
  have h_delta : ∀ d ∈ R.support,
      R.coeff d * (heckeGen 2 p 0 ^ (d 0) * heckeGen 2 p 1 ^ (d 1))
          (diagCoset (primePowDiag 2 p ![s 1, s 0 + s 1])) =
      if d = s then R.coeff d else 0 := by
    intro d hd_mem
    rw [monomial_eval_kronecker p hp (d 0) (d 1) (s 0) (s 1) (hs_min d hd_mem)]
    by_cases hds : d = s
    · subst hds; simp
    · rw [if_neg hds, if_neg (fun ⟨h0, h1⟩ ↦ hds (by ext i; fin_cases i; exacts [h0, h1])),
        mul_zero]
  rw [Finset.sum_congr rfl h_delta, Finset.sum_ite_eq_of_mem' R.support s _ hs_mem] at h_zero
  exact hs_coeff h_zero

/-- Injectivity of `evalHomLocal` follows from injectivity of `evalHom`. -/
lemma evalHomLocal_injective (n : ℕ) [NeZero n] (p : ℕ)
    (h_inj : Function.Injective (evalHom n p)) :
    Function.Injective (evalHomLocal n p) := by
  intro P Q hPQ
  -- `evalHomLocal` is sealed upstream, so the coercion is read off `evalHomLocal_coe`
  -- rather than by unfolding.
  refine h_inj ?_
  rw [← evalHomLocal_coe n p P, ← evalHomLocal_coe n p Q, hPQ]

end HeckeRing.GLn.Inj

namespace HeckeRing.GLn

variable (p : ℕ) (hp : p.Prime)

/-- **Shimura, Theorem 3.20 for `n = 1`**: the `p`-local Hecke ring of `GL₁` is the
polynomial ring `ℤ[X]` on the single generator `T(p)`. -/
noncomputable def polynomialRingEquivOne :
    MvPolynomial (Fin 1) ℤ ≃+* pLocalSubring 1 p :=
  RingEquiv.ofBijective (evalHomLocal 1 p)
    ⟨Inj.evalHomLocal_injective 1 p (Inj.evalHom_one_injective p hp.one_lt),
     evalHomLocal_one_surjective p hp.pos⟩

/-- **Shimura, Theorem 3.20 for `n = 2`**: the `p`-local Hecke ring of `GL₂` is the
polynomial ring `ℤ[X₁, X₂]` on the generators `T(1, p)` and `T(p, p)`. This is the case the
classical theory of modular forms uses. -/
noncomputable def polynomialRingEquivTwo :
    MvPolynomial (Fin 2) ℤ ≃+* pLocalSubring 2 p :=
  RingEquiv.ofBijective (evalHomLocal 2 p)
    ⟨Inj.evalHomLocal_injective 2 p (Inj.evalHom_two_injective p hp),
     evalHomLocal_two_surjective p hp⟩

/-- The rank-one presentation isomorphism is the evaluation map. -/
@[simp] lemma polynomialRingEquivOne_apply (f : MvPolynomial (Fin 1) ℤ) :
    polynomialRingEquivOne p hp f = evalHomLocal 1 p f := (rfl)

/-- The rank-two presentation isomorphism is the evaluation map. -/
@[simp] lemma polynomialRingEquivTwo_apply (f : MvPolynomial (Fin 2) ℤ) :
    polynomialRingEquivTwo p hp f = evalHomLocal 2 p f := (rfl)

end HeckeRing.GLn
