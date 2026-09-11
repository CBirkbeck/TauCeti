/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.RingEigenvalue

/-!
# Eigenvalues agreeing outside a finite set agree at every good prime

Strong multiplicity one (Miyake, Theorem 4.6.12) assumes that two eigenforms have the same
eigenvalue at every index coprime to the level outside a finite exceptional set. The first step
of its proof removes the exceptional set at the primes: for a good prime `p`, pick a prime `q`
beyond the exceptional set, the level and `p`; the two forms agree at `p q` and at `q`, or at
`p q²` and at `q²`, and multiplicativity cancels the factor at `q` or `q²` — one of
`λ_q`, `λ_{q²}` is nonzero, since `λ_q = 0` forces `λ_{q²} = −χ(q) q^{k−1} ≠ 0`.

## Main results

* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_prime_eq_of_forall_notMem`: two good Hecke
  eigenforms whose eigenvalues agree at every index coprime to `N` outside a finite set agree at
  every prime coprime to `N`.

## Provenance

The argument is the opening step of `strongMultiplicityOne` in the AINTLIB `LeanModularForms`
project (`LeanModularForms/StrongMultiplicityOne/ConstantMultiple.lean`, Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), stated there on
Fourier coefficients of normalised eigenforms; here it is read off the eigenvalue system of
`Newforms/RingEigenvalue.lean`, so no normalisation is needed.

## References

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.12.
-/

public section

namespace HeckeRing.GL2.EigenformAwayFromLevel

variable {N : ℕ} [NeZero N] {k : ℤ} (f : EigenformAwayFromLevel N k)

/-- At a good prime `p` with `λ_p = 0`, the eigenvalue at `p²` is `−χ(p) p^{k−1}`, which is
nonzero. -/
private theorem eigenvalue_prime_sq_ne_zero_of_eq_zero {p : ℕ+} (hp : (p : ℕ).Prime)
    (hpN : Nat.Coprime p N) (h0 : f.eigenvalue p hpN = 0) :
    f.eigenvalue (p ^ 2) (PNat.pow_coe p 2 ▸ hpN.pow_left 2) ≠ 0 := by
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
  have hQN (v : ℕ) : Nat.Coprime ((Q ^ v : ℕ+) : ℕ) N := PNat.pow_coe Q v ▸ hqN.pow_left v
  have hpQ (v : ℕ) : Nat.Coprime p ((Q ^ v : ℕ+) : ℕ) := PNat.pow_coe Q v ▸ hqp.pow_right v
  have key : ∀ v : ℕ, v ≠ 0 → f.eigenvalue (Q ^ v) (hQN v) ≠ 0 →
      f.eigenvalue p hpN = g.eigenvalue p hpN := fun v hv0 hv ↦ by
    have hle : q ≤ ((Q ^ v : ℕ+) : ℕ) := by
      rw [PNat.pow_coe]
      exact Nat.le_self_pow hv0 q
    have hpQv : Nat.Coprime ((p * Q ^ v : ℕ+) : ℕ) N :=
      PNat.mul_coe p (Q ^ v) ▸ Nat.Coprime.mul_left hpN (hQN v)
    have e1 := h (p * Q ^ v) hpQv
      (hqS _ (by rw [PNat.mul_coe]; exact hle.trans (Nat.le_mul_of_pos_left _ p.pos)))
    have e2 := h (Q ^ v) (hQN v) (hqS _ hle)
    rw [f.eigenvalue_mul (hpQ v) hpN (hQN v), g.eigenvalue_mul (hpQ v) hpN (hQN v), ← e2] at e1
    exact mul_right_cancel₀ hv e1
  by_cases h0 : f.eigenvalue Q hqN = 0
  · exact key 2 two_ne_zero (f.eigenvalue_prime_sq_ne_zero_of_eq_zero (p := Q) hq hqN h0)
  · exact key 1 one_ne_zero (by rwa [f.eigenvalue_congr (pow_one Q) (hn := hqN)])

end HeckeRing.GL2.EigenformAwayFromLevel
