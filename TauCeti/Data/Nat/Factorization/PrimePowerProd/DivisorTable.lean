/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Factorization.PrimePowerProd
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# The divisor multiplication table of a prime-power-multiplicative family

Fix a commutative ring `R` and two block maps `D S : ℕ → ℕ → R`, and assemble each over a prime
factorisation with `TauCeti.Nat.primePowerProd`. Suppose the assembled `D` obeys the *per-prime*
table: for a prime `p` and `r ≤ s`,

`D_{p^r} · D_{p^s} = ∑_{i ≤ r} pⁱ • (S_{pⁱ} · D_{p^{r+s−2i}})`.

Then it obeys the *global* one, over every pair of nonzero arguments at once:

`D_m · D_n = ∑_{d ∣ gcd m n} d • (S_d · D_{mn/d²})`.

## Main results

* `TauCeti.Nat.primePowerProd_mul_eq_sum_divisors_gcd`: the global table, deduced from the
  per-prime one.

The deduction is a strong induction on `gcd m n`. When the gcd is `1` the divisor sum collapses to
its `d = 1` term and the statement is coprime multiplicativity. Otherwise split off the least prime
`p` of the gcd: `m = p^a·m'` and `n = p^b·n'` with `p` dividing neither `m'` nor `n'`, so both
products factor, the prime-power halves meet the hypothesis, and the coprime halves meet the
induction hypothesis at the strictly smaller gcd `gcd m' n'`. Multiplying the two resulting sums
gives a sum over `range (min a b + 1) ×ˢ (gcd m' n').divisors`, and

`(i, d') ↦ pⁱ · d'`

is a bijection from that onto `(gcd m n).divisors` — its inverse splits a divisor into its `p`-part
and its `p`-free part. Under it the two summands agree.

## Relation to Mathlib

Mathlib's `ArithmeticFunction.IsMultiplicative` describes families multiplicative on *coprime*
arguments, and `ArithmeticFunction.mul` gives them a Dirichlet convolution. Neither expresses this
table: the right-hand side is not a convolution of two arithmetic functions — the index `mn/d²` is
quadratic in the divisor, and the `S`-factor is evaluated at `d` while the `D`-factor is evaluated
at `mn/d²`. The statement is also not about a function `ℕ → R` but about the *assembled* family, so
the per-prime table is the input rather than multiplicativity.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3 — Theorem 3.24, whose Hecke-ring instance is the intended consumer.
* Ported from [AINTLIB](https://github.com/CBirkbeck/AINTLIB), Apache-2.0, Chris Birkbeck, commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
  `projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Unified/Gamma0RingDn.lean`,
  section `FormalTable` (lines 186-438). The source states the table over `Finset.attach` of the
  divisors and keeps its whole section `private` inside a Hecke namespace; both are dropped here.
  The summand never inspects a membership proof, so the sum is taken over `Nat.divisors` itself and
  the reindexing is a `Finset.sum_nbij'` between plain finsets rather than between subtypes — which
  also removes the source's four `Subtype.ext` obligations. The source's two factorization helpers
  are one lemma here, their `0 < d` hypotheses being consequences of `¬p ∣ d`. The source's
  `peelProd` is this repository's `TauCeti.Nat.primePowerProd`, and the statement is over `d ^ 2`
  rather than the source's `d * d`.
-/

public section

open Finset

namespace TauCeti

namespace Nat

/-! ### Splitting a natural number at a prime -/

/-- The `p`-adic valuation of `p ^ k * d` is `k` when `p` does not divide `d`.

No positivity is asked of `d`: `¬p ∣ d` already forces `d ≠ 0`, since every prime divides `0`. -/
private theorem factorization_pow_mul_self {p d : ℕ} (hp : p.Prime) (hpd : ¬p ∣ d) (k : ℕ) :
    (p ^ k * d).factorization p = k := by
  have hd : d ≠ 0 := fun h ↦ hpd (h ▸ dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero k hp.pos.ne') hd, Finsupp.add_apply,
    hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hpd]
  simp

/-- The greatest common divisor splits at a prime: if `p` divides neither `m'` nor `n'`, then the
`p`-free part of `gcd (p^a·m') (p^b·n')` is `gcd m' n'` and its `p`-part is `p ^ min a b`. -/
private theorem gcd_pow_mul_pow_mul {p a b m' n' : ℕ} (hp : p.Prime) (hm' : ¬p ∣ m')
    (hn' : ¬p ∣ n') :
    Nat.gcd (p ^ a * m') (p ^ b * n') = Nat.gcd m' n' * p ^ min a b := by
  have hpa_m' : Nat.Coprime (p ^ a) m' := (hp.coprime_iff_not_dvd.2 hm').pow_left a
  have hpa_n' : Nat.Coprime (p ^ a) n' := (hp.coprime_iff_not_dvd.2 hn').pow_left a
  have hm'_pb : Nat.Coprime m' (p ^ b) := ((hp.coprime_iff_not_dvd.2 hm').pow_left b).symm
  have hgcd_pp : Nat.gcd (p ^ a) (p ^ b) = p ^ min a b := by
    rcases le_total a b with h | h
    · rw [Nat.gcd_eq_left (pow_dvd_pow p h), min_eq_left h]
    · rw [Nat.gcd_eq_right (pow_dvd_pow p h), min_eq_right h]
  rw [hpa_m'.mul_gcd, Nat.Coprime.gcd_mul_right_cancel_right _ hpa_n'.symm,
    Nat.Coprime.gcd_mul_left_cancel_right _ hm'_pb.symm, hgcd_pp, mul_comm]

/-- The index appearing on the right of the table, after a divisor `p^j·d'` of `gcd m n` has been
split at `p`: the quotient `mn/(p^j·d')²` factors as a power of `p` times the corresponding
quotient for the `p`-free parts, and the two factors are coprime. -/
private theorem mul_div_mul_self {p a b m' n' m n d' j : ℕ} (hp : p.Prime)
    (hm_eq : m = p ^ a * m') (hn_eq : n = p ^ b * n') (hm' : ¬p ∣ m') (hn' : ¬p ∣ n')
    (hd'm : d' ∣ m') (hd'n : d' ∣ n') (hj : j ≤ min a b) :
    m * n / (p ^ j * d' * (p ^ j * d')) =
        p ^ (min a b + max a b - 2 * j) * (m' * n' / (d' * d')) ∧
      Nat.Coprime (p ^ (min a b + max a b - 2 * j)) (m' * n' / (d' * d')) := by
  have hdd : d' * d' ∣ m' * n' := Nat.mul_dvd_mul hd'm hd'n
  have hr : min a b + max a b - 2 * j = a + b - 2 * j := by rw [min_add_max]
  have hquot : ¬p ∣ m' * n' / (d' * d') := fun h ↦
    hp.not_dvd_mul hm' hn' (h.trans (Nat.div_dvd_of_dvd hdd))
  set r := a + b - 2 * j with hr_def
  refine ⟨hr ▸ ?_, hr ▸ (hp.coprime_iff_not_dvd.2 hquot).pow_left _⟩
  have hab : a + b = 2 * j + r := by omega
  have h1 : m * n = p ^ (a + b) * (m' * n') := by rw [hm_eq, hn_eq, pow_add]; ring
  have h2 : p ^ j * d' * (p ^ j * d') = p ^ (2 * j) * (d' * d') := by rw [two_mul, pow_add]; ring
  rw [h1, h2, hab, pow_add, mul_assoc, Nat.mul_div_mul_left _ _ (pow_pos hp.pos (2 * j)),
    Nat.mul_div_assoc _ hdd]

/-- The forward half of the reindexing bijection lands where it should: a `p`-power times a
divisor of `g` divides `g * p ^ k`, as soon as the exponent is at most `k`. -/
private theorem pow_mul_dvd_mul_pow {p g j d k : ℕ} (hj : j ≤ k) (hd : d ∣ g) :
    p ^ j * d ∣ g * p ^ k :=
  mul_comm (p ^ j) d ▸ Nat.mul_dvd_mul hd (pow_dvd_pow p hj)

/-- The backward half of the reindexing bijection: when `g` is prime to `p`, a divisor of
`g * p ^ k` splits into a `p`-part of exponent at most `k` and a `p`-free part dividing `g`.
Stated as the membership the bijection has to produce. -/
private theorem mem_range_product_divisors {p g k d : ℕ} (hp : p.Prime) (hg0 : g ≠ 0)
    (hpg : ¬p ∣ g) (hd : d ∣ g * p ^ k) :
    (d.factorization p, ordCompl[p] d) ∈ Finset.range (k + 1) ×ˢ g.divisors := by
  have hprod0 : g * p ^ k ≠ 0 := Nat.mul_ne_zero hg0 (pow_ne_zero _ hp.pos.ne')
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hprod0 hd
  simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]
  refine ⟨?_, Nat.mem_divisors.2 ⟨?_, hg0⟩⟩
  · calc d.factorization p ≤ (g * p ^ k).factorization p :=
          (Nat.factorization_le_iff_dvd hd0 hprod0).2 hd p
      _ = k := by rw [mul_comm]; exact factorization_pow_mul_self hp hpg _
  · have hord : ordCompl[p] (g * p ^ k) = g := by
      rw [mul_comm, Nat.ordCompl_pow_mul_of_not_dvd _ hp hpg]
    exact hord ▸ Nat.ordCompl_dvd_ordCompl_of_dvd hd p

/-- **The gcd splits at a prime**: the gcd of the `p`-free parts, times `p` to the smaller of the
two valuations. This is the shape both the induction and the reindexing consume. -/
private theorem gcd_eq_gcd_ordCompl_mul_pow_min {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hn : n ≠ 0) :
    Nat.gcd m n = Nat.gcd (ordCompl[p] m) (ordCompl[p] n) *
      p ^ min (m.factorization p) (n.factorization p) := by
  have hm_eq : m = p ^ m.factorization p * ordCompl[p] m :=
    (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  have hn_eq : n = p ^ n.factorization p * ordCompl[p] n :=
    (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  conv_lhs => rw [hm_eq, hn_eq]
  exact gcd_pow_mul_pow_mul hp (Nat.not_dvd_ordCompl hp hm) (Nat.not_dvd_ordCompl hp hn)

/-- Splitting `p ^ j * d` at `p` returns `(j, d)` when `p` does not divide `d`: the two halves of
the reindexing bijection are mutually inverse. -/
private theorem factorization_ordCompl_pow_mul {p j d : ℕ} (hp : p.Prime) (hd : ¬p ∣ d) :
    ((p ^ j * d).factorization p, ordCompl[p] (p ^ j * d)) = (j, d) := by
  have hfact : (p ^ j * d).factorization p = j := factorization_pow_mul_self hp hd j
  simp [hfact, Nat.mul_div_cancel_left d (pow_pos hp.pos j)]

/-- Removing the `p`-part strictly shrinks the gcd, when `p` divides both arguments. This is what
makes the induction in `primePowerProd_mul_eq_sum_divisors_gcd` terminate. -/
private theorem gcd_ordCompl_lt {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0)
    (hpm : p ∣ m) (hpn : p ∣ n)
    (hgcd : Nat.gcd m n = Nat.gcd (ordCompl[p] m) (ordCompl[p] n) *
      p ^ min (m.factorization p) (n.factorization p)) :
    Nat.gcd (ordCompl[p] m) (ordCompl[p] n) < Nat.gcd m n := by
  rw [hgcd]
  refine lt_mul_of_one_lt_right (Nat.pos_of_ne_zero fun h ↦
    (Nat.ordCompl_pos p hm).ne' (Nat.eq_zero_of_gcd_eq_zero_left h)) (Nat.one_lt_pow ?_ hp.one_lt)
  have ha : 0 < m.factorization p := hp.factorization_pos_of_dvd hm hpm
  have hb : 0 < n.factorization p := hp.factorization_pos_of_dvd hn hpn
  omega

/-! ### The table -/

section CommRing

variable {R : Type*} [CommRing R] (D S : ℕ → ℕ → R)

/-- Coprime multiplicativity of the assembled family, in a commutative ring: the commutation
obligations of `primePowerProd_mul_of_coprime` are all discharged by `Commute.all`. -/
private theorem primePowerProd_mul_coprime (f : ℕ → ℕ → R) {a b : ℕ} (hab : Nat.Coprime a b) :
    primePowerProd f (a * b) = primePowerProd f a * primePowerProd f b :=
  primePowerProd_mul_of_coprime f hab fun _ _ _ _ _ ↦ Commute.all _ _

/-- Splitting the assembly at a prime: `f m` is its `p`-block times the assembly over the `p`-free
part of `m`. Applied at both arguments of the table. -/
private theorem primePowerProd_eq_ordProj_mul_ordCompl (f : ℕ → ℕ → R) {p m : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) :
    primePowerProd f m =
      primePowerProd f (p ^ m.factorization p) * primePowerProd f (ordCompl[p] m) := by
  have hm_eq : m = p ^ m.factorization p * ordCompl[p] m :=
    (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  conv_lhs => rw [hm_eq]
  exact primePowerProd_mul_coprime f
    ((hp.coprime_iff_not_dvd.2 (Nat.not_dvd_ordCompl hp hm)).pow_left _)

/-- The two prime-power blocks may be put in `min`/`max` order, which is the shape the per-prime
table is stated in. -/
private theorem primePowerProd_prime_pow_mul_min_max (f : ℕ → ℕ → R) (p a b : ℕ) :
    primePowerProd f (p ^ a) * primePowerProd f (p ^ b) =
      primePowerProd f (p ^ min a b) * primePowerProd f (p ^ max a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, mul_comm]

/-- The summand of the product of the two sums agrees with the summand of the target sum at the
divisor `p ^ j * d'`. This is the pointwise half of the reindexing. -/
private theorem smul_mul_smul_of_split {p a b m' n' m n d' j : ℕ} (hp : p.Prime)
    (hm_eq : m = p ^ a * m') (hn_eq : n = p ^ b * n') (hm' : ¬p ∣ m') (hn' : ¬p ∣ n')
    (hd'g : d' ∣ Nat.gcd m' n') (hpg : ¬p ∣ Nat.gcd m' n') (hj : j ≤ min a b) :
    ((p : ℤ) ^ j • (primePowerProd S (p ^ j) *
        primePowerProd D (p ^ (min a b + max a b - 2 * j)))) *
      ((d' : ℤ) • (primePowerProd S d' * primePowerProd D (m' * n' / (d' * d')))) =
    ((p ^ j * d' : ℕ) : ℤ) • (primePowerProd S (p ^ j * d') *
      primePowerProd D (m * n / (p ^ j * d' * (p ^ j * d')))) := by
  obtain ⟨hidx, hcopD⟩ := mul_div_mul_self hp hm_eq hn_eq hm' hn'
    (hd'g.trans (Nat.gcd_dvd_left m' n')) (hd'g.trans (Nat.gcd_dvd_right m' n')) hj
  have hcopS : Nat.Coprime (p ^ j) d' :=
    (hp.coprime_iff_not_dvd.2 fun h ↦ hpg (h.trans hd'g)).pow_left j
  rw [smul_mul_smul_comm, hidx, primePowerProd_mul_coprime D hcopD,
    primePowerProd_mul_coprime S hcopS, Nat.cast_mul, Nat.cast_pow]
  ring_nf

/-- The reindexing step: the product of the prime-power sum with the sum over the divisors of
`gcd m' n'` is the sum over the divisors of `gcd m n`, via `(j, d') ↦ p ^ j * d'`. -/
private theorem sum_mul_sum_eq_sum_divisors {p a b m' n' m n : ℕ} (hp : p.Prime) (hm'0 : m' ≠ 0)
    (hm' : ¬p ∣ m') (hn' : ¬p ∣ n') (hm_eq : m = p ^ a * m')
    (hn_eq : n = p ^ b * n') (hgcd : Nat.gcd m n = Nat.gcd m' n' * p ^ min a b) :
    (∑ j ∈ range (min a b + 1), (p : ℤ) ^ j • (primePowerProd S (p ^ j) *
        primePowerProd D (p ^ (min a b + max a b - 2 * j)))) *
      (∑ d ∈ (Nat.gcd m' n').divisors,
        (d : ℤ) • (primePowerProd S d * primePowerProd D (m' * n' / (d * d)))) =
    ∑ d ∈ (Nat.gcd m n).divisors,
      (d : ℤ) • (primePowerProd S d * primePowerProd D (m * n / (d * d))) := by
  have hg'0 : Nat.gcd m' n' ≠ 0 := fun h ↦ hm'0 (Nat.eq_zero_of_gcd_eq_zero_left h)
  have hpg' : ¬p ∣ Nat.gcd m' n' := fun h ↦ hm' (h.trans (Nat.gcd_dvd_left m' n'))
  have hprod0 : Nat.gcd m' n' * p ^ min a b ≠ 0 :=
    Nat.mul_ne_zero hg'0 (pow_ne_zero _ hp.pos.ne')
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun x ↦ p ^ x.1 * x.2)
    (fun d ↦ (d.factorization p, ordCompl[p] d)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, d'⟩ hx
    simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hx
    rw [hgcd, Nat.mem_divisors]
    exact ⟨pow_mul_dvd_mul_pow hx.1 (Nat.dvd_of_mem_divisors hx.2), hprod0⟩
  · intro d hd
    exact mem_range_product_divisors hp hg'0 hpg' (hgcd ▸ Nat.dvd_of_mem_divisors hd)
  · rintro ⟨j, d'⟩ hx
    simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hx
    exact factorization_ordCompl_pow_mul hp fun h ↦ hpg' (h.trans (Nat.dvd_of_mem_divisors hx.2))
  · intro d _
    exact Nat.ordProj_mul_ordCompl_eq_self d p
  · rintro ⟨j, d'⟩ hx
    simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hx
    exact smul_mul_smul_of_split D S hp hm_eq hn_eq hm' hn'
      (Nat.dvd_of_mem_divisors hx.2) hpg' hx.1

/-- **The divisor multiplication table.** A family assembled over prime factorisations obeying the
per-prime table `D_{p^r}·D_{p^s} = ∑_{i ≤ r} pⁱ • (S_{pⁱ}·D_{p^{r+s−2i}})` obeys the global one

`D_m · D_n = ∑_{d ∣ gcd m n} d • (S_d · D_{mn/d²})`.

Both arguments must be nonzero: `primePowerProd` sends `0` to the empty product, and `gcd 0 0 = 0`
has no divisors, so at `m = n = 0` the left side is `1` and the right an empty sum. -/
theorem primePowerProd_mul_eq_sum_divisors_gcd
    (hppow : ∀ p : ℕ, p.Prime → ∀ r s : ℕ, r ≤ s →
      primePowerProd D (p ^ r) * primePowerProd D (p ^ s) =
        ∑ i ∈ range (r + 1), (p : ℤ) ^ i • (primePowerProd S (p ^ i) *
          primePowerProd D (p ^ (r + s - 2 * i))))
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    primePowerProd D m * primePowerProd D n =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (d : ℤ) • (primePowerProd S d * primePowerProd D (m * n / d ^ 2)) := by
  simp only [sq]
  induction hg : Nat.gcd m n using Nat.strong_induction_on generalizing m n with
  | _ g ih =>
  rcases eq_or_ne g 1 with rfl | hg1
  · rw [Nat.divisors_one, Finset.sum_singleton, Nat.cast_one, one_smul, Nat.one_mul,
      Nat.div_one, primePowerProd_one, one_mul, ← primePowerProd_mul_coprime D hg]
  -- Split both arguments at the least prime `p` of the gcd.
  have hg0 : g ≠ 0 := fun h ↦ hm (Nat.eq_zero_of_gcd_eq_zero_left (hg.trans h))
  set p := g.minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime hg1
  have hpm : p ∣ m := (Nat.minFac_dvd g).trans (hg ▸ Nat.gcd_dvd_left m n)
  have hpn : p ∣ n := (Nat.minFac_dvd g).trans (hg ▸ Nat.gcd_dvd_right m n)
  have hm'0 : ordCompl[p] m ≠ 0 := (Nat.ordCompl_pos p hm).ne'
  have hn'0 : ordCompl[p] n ≠ 0 := (Nat.ordCompl_pos p hn).ne'
  have hm' : ¬p ∣ ordCompl[p] m := Nat.not_dvd_ordCompl hp hm
  have hn' : ¬p ∣ ordCompl[p] n := Nat.not_dvd_ordCompl hp hn
  have hm_eq : m = p ^ m.factorization p * ordCompl[p] m :=
    (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  have hn_eq : n = p ^ n.factorization p * ordCompl[p] n :=
    (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hgcd := gcd_eq_gcd_ordCompl_mul_pow_min (p := p) hp hm hn
  -- The `p`-free gcd is strictly smaller, so the induction hypothesis applies to it.
  have hlt : Nat.gcd (ordCompl[p] m) (ordCompl[p] n) < g := by
    rw [← hg]; exact gcd_ordCompl_lt hp hm hn hpm hpn hgcd
  rw [← hg, primePowerProd_eq_ordProj_mul_ordCompl D hp hm,
    primePowerProd_eq_ordProj_mul_ordCompl D hp hn, mul_mul_mul_comm,
    primePowerProd_prime_pow_mul_min_max D p _ _, hppow p hp _ _ min_le_max,
    ih _ hlt hm'0 hn'0 rfl]
  exact sum_mul_sum_eq_sum_divisors D S hp hm'0 hm' hn' hm_eq hn_eq hgcd

end CommRing

end Nat

end TauCeti
