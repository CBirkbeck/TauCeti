/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.PolynomialRing.Basic

/-!
# The leading elementary-divisor vector of a Hecke monomial

Towards **Shimura's Theorem 3.20** at general `n`: the `p`-local Hecke ring `pLocalSubring` is
the polynomial ring `ℤ[X₁, …, Xₙ]` on the diagonal prime cosets `heckeGen k = T(1, …, 1, p, …, p)`.
The injectivity half is a leading-term argument. Multiplying double cosets multiplies their
elementary divisors "up to lower terms", so the monomial `∏ k, heckeGen k ^ e k` has a
distinguished term, the diagonal coset whose elementary divisors are the products of those of the
factors, and the argument is that this leading term determines the exponent vector `e`.

This file is the combinatorial half of that argument: the exponent vector `leadingExponent e` of
that distinguished diagonal — entry `i` counts, with multiplicity `e k`, the generators whose
diagonal carries `p` in position `i`, which are the `k` with `n - 1 - i ≤ k` — together with the
properties the leading-term argument consumes, above all that the exponents are recovered from it.

## Main definitions

* `HeckeRing.GLn.leadingExponent`: the exponent vector of the leading elementary-divisor diagonal
  of the Hecke monomial with exponents `e`, as the suffix sums `i ↦ ∑ k ≥ n - 1 - i, e k`.

## Main results

* `HeckeRing.GLn.leadingExponent_injective`: **the exponents of a Hecke monomial are recovered
  from its leading elementary-divisor vector.** Position `n - 1 - k` is the suffix sum
  `∑ k' ≥ k, e k'` (`HeckeRing.GLn.leadingExponent_rev`), so consecutive entries differ by one
  exponent.
* `HeckeRing.GLn.isDvdChain_primePowDiag_leadingExponent`: the vector is monotone
  (`HeckeRing.GLn.monotone_leadingExponent`), so the leading diagonal `T(p ^ leadingExponent e)`
  is a divisibility chain — for `0 < p` a canonical diagonal, by `primePowDiag_pos`.
* `HeckeRing.GLn.primePowDiag_leadingExponent_single`: on the generator `X k` the leading
  diagonal is `heckeGenDiag k` itself; `HeckeRing.GLn.leadingExponent_add` and `primePowDiag_add`
  then give the leading diagonal of a product of monomials as the product of theirs.
* `HeckeRing.GLn.sum_leadingExponent`: the weight `∑ k, (k + 1) * e k` of the leading diagonal,
  the `p`-adic valuation of its determinant.

## Implementation notes

The other half of the leading-term argument — that the leading coset occurs in the monomial with
coefficient `1` and every other coset of its support lies below it — is the triangular expansion,
and is not proved here. At `n = 1, 2` Theorem 3.20 is `PolynomialRing/Injective.lean`, by direct
computation; `leadingExponent_fin_two` is the sanity check that at `n = 2` this vector is
`![e 1, e 0 + e 1]`, the exponent pattern of the leading coset `T(p ^ e 1, p ^ (e 0 + e 1))` of
that computation (which is not rerouted through it).

This is original work filling the general-`n` gap the roadmap records: the AINTLIB source
(`LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean`) proves Theorem 3.20 at `n = 1, 2` only and
has no general-`n` leading-term device.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2, Theorem 3.20.
-/

public section

open Finset

namespace HeckeRing.GLn

variable {n : ℕ}

/-- The exponent vector of the leading elementary-divisor diagonal of the Hecke monomial
`∏ k, heckeGen k ^ e k`: entry `i` counts, with multiplicity `e k`, the generators `heckeGen k`
whose diagonal `heckeGenDiag k` carries `p` in position `i` — those with `n - 1 - i ≤ k`, i.e.
`Fin.rev i ≤ k` — so it is the suffix sum of `e` from `Fin.rev i`. -/
def leadingExponent (e : Fin n → ℕ) : Fin n → ℕ :=
  fun i ↦ ∑ k ∈ Ici (Fin.rev i), e k

/-- Defining equation for the sealed definition `leadingExponent`. -/
lemma leadingExponent_apply (e : Fin n → ℕ) (i : Fin n) :
    leadingExponent e i = ∑ k ∈ Ici (Fin.rev i), e k :=
  (rfl)

/-- The empty monomial has the trivial leading diagonal. -/
@[simp]
lemma leadingExponent_zero : leadingExponent (0 : Fin n → ℕ) = 0 := by
  ext i
  simp [leadingExponent_apply]

/-- The leading exponent vector is additive; with `primePowDiag_add` this says the leading
diagonal of a product of monomials is the entrywise product of their leading diagonals. -/
lemma leadingExponent_add (e f : Fin n → ℕ) :
    leadingExponent (e + f) = leadingExponent e + leadingExponent f := by
  ext i
  simp [leadingExponent_apply, Finset.sum_add_distrib]

/-- Read from the last position backwards, the leading exponent vector is the suffix sums of the
exponents: position `n - 1 - k` sees exactly the generators `k' ≥ k`. -/
lemma leadingExponent_rev (e : Fin n → ℕ) (k : Fin n) :
    leadingExponent e (Fin.rev k) = ∑ k' ∈ Ici k, e k' := by
  rw [leadingExponent_apply, Fin.rev_rev]

/-- On a single generator, the leading exponent vector is that generator's own `p`-exponent
pattern: `0` on the first `n - 1 - k` positions and `1` on the last `k + 1`. -/
lemma leadingExponent_single (k : Fin n) : leadingExponent (Pi.single k 1) =
    fun i : Fin n ↦ if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1 := by
  ext i
  rw [leadingExponent_apply, Finset.sum_pi_single']
  simp only [Finset.mem_Ici, Fin.le_iff_val_le_val, Fin.val_rev]
  split_ifs <;> omega

/-- The leading diagonal of the generator `heckeGen k` is its defining diagonal `heckeGenDiag k`. -/
lemma primePowDiag_leadingExponent_single (p : ℕ) (k : Fin n) :
    primePowDiag n p (leadingExponent (Pi.single k 1)) = heckeGenDiag n p k := by
  rw [leadingExponent_single, heckeGenDiag_eq_primePowDiag]

/-- The leading exponent vector is monotone: a later position sees every generator an earlier one
does. -/
lemma monotone_leadingExponent (e : Fin n → ℕ) : Monotone (leadingExponent e) := fun _ _ hij ↦
  Finset.sum_le_sum_of_subset (Finset.Ici_subset_Ici.2 (Fin.rev_le_rev.2 hij))

/-- The leading diagonal `T(p ^ leadingExponent e)` is a divisibility chain; together with
`primePowDiag_pos`, for `0 < p` it is a canonical diagonal coset. -/
lemma isDvdChain_primePowDiag_leadingExponent (p : ℕ) (e : Fin n → ℕ) :
    IsDvdChain (primePowDiag n p (leadingExponent e)) :=
  isDvdChain_primePowDiag n p _ (monotone_leadingExponent e)

/-- A vector on `Fin n` is determined by its suffix sums: each entry is the difference of two
consecutive ones, the last suffix sum being the last entry itself. -/
private lemma sum_Ici_injective :
    Function.Injective fun (e : Fin n → ℕ) (k : Fin n) ↦ ∑ k' ∈ Ici k, e k' := by
  intro e f h
  funext k
  have hk := congr_fun h k
  simp only at hk
  rw [← Finset.add_sum_Ioi_eq_sum_Ici, ← Finset.add_sum_Ioi_eq_sum_Ici] at hk
  cases n with
  | zero => exact k.elim0
  | succ m =>
    cases k using Fin.lastCases with
    | last =>
      have hIoi : Ioi (Fin.last m) = ∅ := Finset.Ioi_eq_empty.2 fun x _ ↦ Fin.le_last x
      simpa [hIoi] using hk
    | cast j =>
      have hIoi : Ioi (Fin.castSucc j) = Ici j.succ := by
        ext x
        simp [Fin.castSucc_lt_iff_succ_le]
      have hs := congr_fun h j.succ
      simp only at hs
      rw [hIoi, hs] at hk
      omega

/-- **The exponents are recovered from the leading elementary-divisor vector.** Its entries are
the suffix sums of the exponents, and suffix sums determine a vector. -/
lemma leadingExponent_injective : Function.Injective (leadingExponent (n := n)) := by
  intro e f h
  refine sum_Ici_injective (funext fun k ↦ ?_)
  simpa only [leadingExponent_rev] using congr_fun h (Fin.rev k)

/-- The weight of the leading diagonal: the total of the leading exponent vector is
`∑ k, (k + 1) * e k`, the generator `heckeGen k` contributing `k + 1` for each of its `e k`
factors. This is the `p`-adic valuation of the determinant of the leading diagonal. -/
lemma sum_leadingExponent (e : Fin n → ℕ) :
    ∑ i, leadingExponent e i = ∑ k : Fin n, ((k : ℕ) + 1) * e k := by
  rw [← Equiv.sum_comp Fin.revPerm (leadingExponent e)]
  simp only [Fin.revPerm_apply, leadingExponent_rev]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun k ↦ Iic k) (by simp)]
  simp [Fin.card_Iic]

/-- Sanity check at `n = 2`: the leading diagonal of `X₀ ^ e 0 * X₁ ^ e 1 = T(1,p) ^ e 0 *
T(p,p) ^ e 1` is `T(p ^ e 1, p ^ (e 0 + e 1))`, as in `PolynomialRing/Injective.lean`. -/
lemma leadingExponent_fin_two (e : Fin 2 → ℕ) : leadingExponent e = ![e 1, e 0 + e 1] := by
  ext i
  fin_cases i <;>
    simp [leadingExponent_apply, ← Finset.filter_le_eq_Ici, Finset.sum_filter, Fin.sum_univ_two]

end HeckeRing.GLn
