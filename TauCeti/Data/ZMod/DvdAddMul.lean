/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Tactic.LinearCombination
public import TauCeti.Data.ZMod.FinEquiv

/-!
# Exactly one residue index divides a linear form

For a nonzero modulus `n` and integers `a c` with `c` a unit mod `n`, exactly one `i : Fin n`
satisfies

```text
(n : ℤ) ∣ a + i * c
```

namely the index whose natural value is `ZMod.val (-a * c⁻¹)`, where `c⁻¹` is the inverse of the
unit. The statements are divisibilities over `ℤ`, which is the form the downstream Hecke sums are
phrased in, and they are arithmetic in `ZMod n`: no matrix, determinant or group action occurs.

Invertibility of `c` is the only thing the argument uses, so nothing here asks for a prime
modulus. Over a prime `p` the hypothesis is implied by `((c : ℤ) : ZMod p) ≠ 0`, since `ZMod p` is
then a field.

## Main results

* `TauCeti.dvd_add_mul_iff_eq_of_dvd`: given one such index, an index satisfies the divisibility
  exactly when it equals that one.
* `TauCeti.dvd_add_mul_val_neg_mul_inv`: such an index exists, with natural value
  `ZMod.val (-a * c⁻¹)`.
* `TauCeti.existsUnique_dvd_add_mul`: the two combined — existence and uniqueness.

## Provenance

The two halves are AINTLIB's, in
[`LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean`](https://github.com/CBirkbeck/AINTLIB) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck:
`dvd_add_mul_iff_eq_of_dvd` is `dvd_topLeft_add_iff_eq_canonicalIndex` (lines 301-310) and
`dvd_add_mul_val_neg_mul_inv` is `dvd_topLeft_add_canonicalIndex` (lines 263-276).

Both are generalised here. The source states them for a matrix `M` with `M.det = 1`, in the entries
`M 0 0` and `M 1 0`, over a prime modulus; these take arbitrary coefficients `a c : ℤ` over an
arbitrary nonzero modulus, and assume only `IsUnit ((c : ℤ) : ZMod n)`, since invertibility of that
one coefficient is all the argument uses. `b₀` is implicit, and the section supplies the binders the
source passes explicitly.

**Neither proof is the source's.** AINTLIB proves uniqueness by rewriting through the `if`-split in
its own `moebiusFin`; here it is arithmetic in `ZMod n` — two indices satisfying the divisibility
differ by something the unit `c` kills — and no group action appears. `existsUnique_dvd_add_mul`
combines the two and has no counterpart in the source, which never states existence and uniqueness
together.
-/

public section

namespace TauCeti

variable {n : ℕ} [NeZero n]

/-- **At most one index.** If `b₀` satisfies the divisibility then an index `i` satisfies it
exactly when `i = b₀`.

The hypothesis is only that the coefficient `c` is a unit mod `n` — the statement is arithmetic in
`ZMod n` and does not need the determinant, nor the Möbius action it conditions. Stated as a
divisibility over `ℤ`, which is the form the downstream Hecke sums are phrased in.

`existsUnique_dvd_add_mul` is the form to reach for when no solution is already in hand. -/
lemma dvd_add_mul_iff_eq_of_dvd (a c : ℤ) (hc : IsUnit ((c : ℤ) : ZMod n)) {b₀ : Fin n}
    (hb₀ : (n : ℤ) ∣ (a + (b₀ : ℕ) * c)) (i : Fin n) :
    (n : ℤ) ∣ (a + (i : ℕ) * c) ↔ i = b₀ := by
  refine ⟨fun hi ↦ ?_, fun hji ↦ hji ▸ hb₀⟩
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hi
  have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hb₀
  push_cast at h1 h2
  refine (ZMod.finEquiv n).injective ?_
  rw [ZMod.finEquiv_apply, ZMod.finEquiv_apply]
  have hsub : (((i : ℕ) : ZMod n) - ((b₀ : ℕ) : ZMod n)) * ((c : ℤ) : ZMod n) = 0 := by
    linear_combination h1 - h2
  exact sub_eq_zero.mp (hc.mul_left_eq_zero.mp hsub)

/-- **A solution exists.** When the coefficient `c` is a unit mod `n` the divisibility holds at
the natural number `ZMod.val (-a * c⁻¹)`, the canonical representative of the residue solving
`a + i * c ≡ 0`. The index is a natural number here, not an element of `Fin n`; the `Fin n` form
is `existsUnique_dvd_add_mul`, which combines this with `dvd_add_mul_iff_eq_of_dvd` to get
uniqueness as well. -/
lemma dvd_add_mul_val_neg_mul_inv (a c : ℤ) (hc : IsUnit ((c : ℤ) : ZMod n)) :
    (n : ℤ) ∣ (a +
      (((-((a : ℤ) : ZMod n) * ((c : ℤ) : ZMod n)⁻¹).val : ℕ)) * c) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]
  have hcancel : (-((a : ℤ) : ZMod n) * ((c : ℤ) : ZMod n)⁻¹) * ((c : ℤ) : ZMod n) =
      -((a : ℤ) : ZMod n) := by
    rw [mul_assoc, ZMod.inv_mul_of_unit _ hc, mul_one]
  rw [hcancel, add_neg_cancel]

/-- **Exactly one index solves the divisibility.** When `c` is a unit mod `n` there is a unique
`i : Fin n` with `n ∣ a + i * c`. This is what `dvd_add_mul_val_neg_mul_inv` and
`dvd_add_mul_iff_eq_of_dvd` combine to, and the form a consumer indexing by `Fin n` wants. -/
theorem existsUnique_dvd_add_mul (a c : ℤ) (hc : IsUnit ((c : ℤ) : ZMod n)) :
    ∃! i : Fin n, (n : ℤ) ∣ (a + (i : ℕ) * c) := by
  have hb : (n : ℤ) ∣ (a + (((ZMod.finEquiv n).symm
      (-((a : ℤ) : ZMod n) * ((c : ℤ) : ZMod n)⁻¹) : Fin n) : ℕ) * c) := by
    simp only [ZMod.finEquiv_symm_apply_val]
    exact dvd_add_mul_val_neg_mul_inv a c hc
  exact ⟨_, hb, fun y hy ↦ (dvd_add_mul_iff_eq_of_dvd a c hc hb y).mp hy⟩

end TauCeti

end
