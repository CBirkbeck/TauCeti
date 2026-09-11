/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Infinite
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimePower
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Scalar
public import TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# The eigenvalue system of a good Hecke eigenform

The eigenvalues of a good Hecke eigenform `f` (`EigenformAwayFromLevel`) inherit the
multiplication table of the `Γ₀(N)` Hecke ring: they are multiplicative on coprime indices, and
along the powers of a good prime `p` they satisfy the Diamond–Shurman recurrence
`λ_{p^{r+2}} = λ_p λ_{p^{r+1}} − χ(p) p^{k−1} λ_{p^r}`, because the scalar coset `T(p, p)` acts on
the character space by `χ(p) p^{k−2}`. Nothing here touches Fourier coefficients: every identity
is the image of a relation in the ring under `heckeRingHomCuspCharSpace`, evaluated on the
(nonzero) form.

The payoff is the **finite-exceptional-set upgrade** behind strong multiplicity one: if two good
Hecke eigenforms have the same eigenvalue at every good index outside a finite set, they have the
same eigenvalue at every good prime. Given a good prime `p`, pick a prime `q` beyond the
exceptional set and beyond `N` and `p`; then `λ_{pq} = λ_p λ_q` on both sides, so the eigenvalues
at `p` agree once `λ_q(f) ≠ 0`. If instead `λ_q(f) = 0`, the recurrence gives
`λ_{q²}(f) = −χ(q) q^{k−1} ≠ 0`, and the same cancellation runs at `p q²`.

## Main results

* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_one`: `λ₁ = 1`.
* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_mul`: `λ_{mn} = λ_m λ_n` for coprime good
  indices.
* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_prime_pow_add_two`: the recurrence along the
  powers of a good prime, and its first instance
  `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_prime_sq`.
* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_prime_eq_of_forall_notMem`: agreement outside
  a finite set of good indices forces agreement at every good prime.

The coprimality proofs guarding `eigenvalue` are implicit arguments of these statements, so that
they apply to whichever proof a consumer holds.

## Provenance

The cancellation argument is that of `eigenvalue_cross_agree_of_cofactor_ne_zero` and
`eigenvalue_at_prime_sq_of_coeff_one_ne_zero` in the AINTLIB `LeanModularForms` project
(`LeanModularForms/StrongMultiplicityOne/ConstantMultiple.lean`, Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), which derives the
multiplicativity and the prime-square identity from the Fourier coefficients of a normalised
eigenform. Here both are read off the Hecke ring instead, so no normalisation and no coefficient
formula is needed.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.8.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public section


namespace HeckeRing.GL2.EigenformAwayFromLevel

variable {N : ℕ} [NeZero N] {k : ℤ} (f : EigenformAwayFromLevel N k)

/-- The form, as a nonzero vector of its character space. -/
private theorem mk_ne_zero :
    (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) ≠ 0 :=
  fun h ↦ f.ne_zero (congrArg Subtype.val h)

/-- Two scalars acting alike on the form are equal. -/
private theorem eq_of_smul_eq {a b : ℂ}
    (h : a • (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) =
      b • (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ)) : a = b :=
  smul_left_injective ℂ f.mk_ne_zero h

/-- The eigenvalue depends only on the index, not on the coprimality proof or on how the index
is spelled. -/
theorem eigenvalue_congr {m n : ℕ+} (hmn : m = n) {hm : Nat.Coprime m N} {hn : Nat.Coprime n N} :
    f.eigenvalue m hm = f.eigenvalue n hn := by
  subst hmn
  rfl

/-- The eigenvalue at `1` is `1`: the ring element at index `1` is the identity. -/
theorem eigenvalue_one {h : Nat.Coprime ((1 : ℕ+) : ℕ) N} : f.eigenvalue 1 h = 1 := by
  refine f.eq_of_smul_eq ?_
  rw [← f.isEigen 1 h, PNat.one_coe, heckeTCompositeGamma0_one, map_one, Module.End.one_apply,
    one_smul]

/-- The eigenvalue at `p ^ 0`, in the form the prime-power recurrence produces. -/
theorem eigenvalue_pow_zero {p : ℕ+} {h : Nat.Coprime ((p ^ 0 : ℕ+) : ℕ) N} :
    f.eigenvalue (p ^ 0) h = 1 :=
  (f.eigenvalue_congr (pow_zero p) (hn := Nat.coprime_one_left N)).trans f.eigenvalue_one

/-- The eigenvalue at `p ^ 1`, in the form the prime-power recurrence produces. -/
theorem eigenvalue_pow_one {p : ℕ+} {h : Nat.Coprime ((p ^ 1 : ℕ+) : ℕ) N}
    {h' : Nat.Coprime p N} : f.eigenvalue (p ^ 1) h = f.eigenvalue p h' :=
  f.eigenvalue_congr (pow_one p)

/-- **Multiplicativity on coprime good indices**: `λ_{mn} = λ_m λ_n`, the image of the coprime
multiplication rule `heckeTCompositeGamma0_mul_of_coprime` of the Hecke ring. -/
theorem eigenvalue_mul {m n : ℕ+} (hmn : Nat.Coprime m n) {hm : Nat.Coprime m N}
    {hn : Nat.Coprime n N} {h : Nat.Coprime ((m * n : ℕ+) : ℕ) N} :
    f.eigenvalue (m * n) h = f.eigenvalue m hm * f.eigenvalue n hn := by
  refine f.eq_of_smul_eq ?_
  rw [← f.isEigen (m * n) h, PNat.mul_coe, heckeTCompositeGamma0_mul_of_coprime N hmn, map_mul,
    Module.End.mul_apply, f.isEigen n hn, map_smul, f.isEigen m hm, smul_smul, mul_comm]

/-- The recurrence block `heckeTGeneratorRecGamma0 N p v` acts by `λ_{p^v}` at a good prime. -/
private theorem heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 {p : ℕ+}
    (hp : (p : ℕ).Prime) {v : ℕ} (hv : Nat.Coprime ((p ^ v : ℕ+) : ℕ) N) :
    heckeRingHomCuspCharSpace k f.χ (heckeTGeneratorRecGamma0 N p v)
        ⟨f.toCuspForm, f.mem_charSpace⟩ =
      f.eigenvalue (p ^ v) hv • (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) := by
  have h := f.isEigen (p ^ v) hv
  rwa [PNat.pow_coe, heckeTCompositeGamma0_prime_pow N hp] at h

/-- **The recurrence along the powers of a good prime**:
`λ_{p^{r+2}} = λ_p λ_{p^{r+1}} − χ(p) p^{k−1} λ_{p^r}`. This is the image of the defining
recurrence `heckeTGeneratorRecGamma0_succ_succ` of the ring, with the scalar coset acting by
`χ(p) p^{k−2}` (`heckeRingHomCuspCharSpace_heckeTScalarGamma0`). -/
theorem eigenvalue_prime_pow_add_two {p : ℕ+} (hp : (p : ℕ).Prime) (hpN : Nat.Coprime p N)
    {r : ℕ} {h₀ : Nat.Coprime ((p ^ r : ℕ+) : ℕ) N} {h₁ : Nat.Coprime ((p ^ (r + 1) : ℕ+) : ℕ) N}
    {h₂ : Nat.Coprime ((p ^ (r + 2) : ℕ+) : ℕ) N} :
    f.eigenvalue (p ^ (r + 2)) h₂ = f.eigenvalue p hpN * f.eigenvalue (p ^ (r + 1)) h₁ -
      (f.χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) * f.eigenvalue (p ^ r) h₀ := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpow : (p : ℂ) ^ (k - 1) = (p : ℂ) ^ (k - 2) * p := by
    rw [show k - 1 = k - 2 + 1 by ring, zpow_add_one₀ hp0]
  have hp1 : Nat.Coprime ((p ^ 1 : ℕ+) : ℕ) N := by rwa [pow_one]
  have h := f.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp h₂
  rw [heckeTGeneratorRecGamma0_succ_succ, map_sub, map_mul, map_mul, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply,
    f.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp h₀,
    f.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp h₁, map_smul, map_smul,
    ← heckeTGeneratorRecGamma0_one, f.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp hp1,
    map_zsmul, heckeRingHomCuspCharSpace_heckeTScalarGamma0 k f.χ p hp.pos hpN,
    LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
    ← Int.cast_smul_eq_zsmul ℂ, smul_smul, smul_smul, smul_smul, ← sub_smul] at h
  rw [f.eq_of_smul_eq h.symm, hpow, f.eigenvalue_pow_one (h' := hpN)]
  push_cast
  ring

/-- **The prime-square identity**: `λ_{p²} = λ_p² − χ(p) p^{k−1}` at a good prime. -/
theorem eigenvalue_prime_sq {p : ℕ+} (hp : (p : ℕ).Prime) (hpN : Nat.Coprime p N)
    {h : Nat.Coprime ((p ^ 2 : ℕ+) : ℕ) N} :
    f.eigenvalue (p ^ 2) h =
      f.eigenvalue p hpN ^ 2 - (f.χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) := by
  rw [f.eigenvalue_prime_pow_add_two hp hpN (r := 0) (h₀ := by simp) (h₁ := by rwa [pow_one]),
    f.eigenvalue_pow_zero, f.eigenvalue_pow_one (h' := hpN), mul_one, sq]

/-- At a good prime `p` with `λ_p = 0`, the eigenvalue at `p²` is `−χ(p) p^{k−1}`, which is
nonzero. -/
private theorem eigenvalue_prime_sq_ne_zero_of_eq_zero {p : ℕ+} (hp : (p : ℕ).Prime)
    (hpN : Nat.Coprime p N) {h : Nat.Coprime ((p ^ 2 : ℕ+) : ℕ) N}
    (h0 : f.eigenvalue p hpN = 0) : f.eigenvalue (p ^ 2) h ≠ 0 := by
  rw [f.eigenvalue_prime_sq hp hpN, h0, sq, zero_mul, zero_sub, neg_ne_zero]
  exact mul_ne_zero (Units.ne_zero _) (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))

/-- **Agreement outside a finite set forces agreement at every good prime.** If two good Hecke
eigenforms have the same eigenvalue at every index coprime to `N` outside a finite set `S`, they
have the same eigenvalue at every prime `p` coprime to `N`: compare at `p q` or at `p q²` for a
prime `q` beyond `S`, `N` and `p`, whichever of `λ_q(f)`, `λ_{q²}(f)` is nonzero. -/
theorem eigenvalue_prime_eq_of_forall_notMem {f g : EigenformAwayFromLevel N k} {S : Finset ℕ}
    (h : ∀ (n : ℕ+) (hn : Nat.Coprime n N), (n : ℕ) ∉ S → f.eigenvalue n hn = g.eigenvalue n hn)
    {p : ℕ+} (hp : (p : ℕ).Prime) (hpN : Nat.Coprime p N) :
    f.eigenvalue p hpN = g.eigenvalue p hpN := by
  obtain ⟨q, hqB, hq⟩ := Nat.exists_infinite_primes (max (S.sup id) (max N p) + 1)
  have hqS : ∀ m : ℕ, q ≤ m → m ∉ S := fun m hm hmS ↦ by
    have := Finset.le_sup (f := id) hmS
    simp only [id] at this
    omega
  have hqN : Nat.Coprime q N := (Nat.Prime.coprime_iff_not_dvd hq).mpr fun hd ↦ by
    have := Nat.le_of_dvd (NeZero.pos N) hd
    omega
  have hqp : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (by omega)
  set Q : ℕ+ := ⟨q, hq.pos⟩
  have hQN : ∀ v : ℕ, Nat.Coprime ((Q ^ v : ℕ+) : ℕ) N := fun v ↦ by
    rw [PNat.pow_coe]
    exact Nat.Coprime.pow_left v hqN
  have hpQ : ∀ v : ℕ, Nat.Coprime p ((Q ^ v : ℕ+) : ℕ) := fun v ↦ by
    rw [PNat.pow_coe]
    exact Nat.Coprime.pow_right v hqp
  have key : ∀ v : ℕ, v ≠ 0 → f.eigenvalue (Q ^ v) (hQN v) ≠ 0 →
      f.eigenvalue p hpN = g.eigenvalue p hpN := fun v hv0 hv ↦ by
    have hle : q ≤ ((Q ^ v : ℕ+) : ℕ) := by
      rw [PNat.pow_coe]
      exact Nat.le_self_pow hv0 q
    have hpQv : Nat.Coprime ((p * Q ^ v : ℕ+) : ℕ) N := by
      rw [PNat.mul_coe]
      exact Nat.Coprime.mul_left hpN (hQN v)
    have e1 := h (p * Q ^ v) hpQv
      (hqS _ (by rw [PNat.mul_coe]; exact hle.trans (Nat.le_mul_of_pos_left _ p.pos)))
    have e2 := h (Q ^ v) (hQN v) (hqS _ hle)
    rw [f.eigenvalue_mul (hpQ v) (hm := hpN) (hn := hQN v),
      g.eigenvalue_mul (hpQ v) (hm := hpN) (hn := hQN v), ← e2] at e1
    exact mul_right_cancel₀ hv e1
  by_cases h0 : f.eigenvalue Q hqN = 0
  · exact key 2 two_ne_zero (f.eigenvalue_prime_sq_ne_zero_of_eq_zero (p := Q) hq hqN h0)
  · exact key 1 one_ne_zero (by rwa [f.eigenvalue_pow_one (p := Q) (h' := hqN)])

end HeckeRing.GL2.EigenformAwayFromLevel
