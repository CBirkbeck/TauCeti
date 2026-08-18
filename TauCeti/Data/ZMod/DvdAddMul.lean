/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.LinearCombination
public import TauCeti.Data.ZMod.FinEquiv

/-!
# Exactly one residue index divides a linear form

For a prime `p` and integers `a c` with `c` invertible mod `p`, exactly one `i : Fin p` satisfies

```text
(p : ℤ) ∣ a + i * c
```

namely the one whose `ZMod.val` is `-a * c⁻¹`. The statements are divisibilities over `ℤ`, which
is the form the downstream Hecke sums are phrased in, and they are arithmetic in `ZMod p`: no
matrix, determinant or group action occurs.

## Main results

* `TauCeti.dvd_add_mul_iff_eq_of_dvd`: given one such index, an index satisfies the divisibility
  exactly when it equals that one.
* `TauCeti.dvd_add_mul_val_neg_mul_inv`: such an index exists, at `ZMod.val (-a * c⁻¹)`.
* `TauCeti.existsUnique_dvd_add_mul`: the two combined — existence and uniqueness.

## Provenance

The two halves are AINTLIB's, in
[`LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean`](https://github.com/CBirkbeck/AINTLIB) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck:
`dvd_add_mul_iff_eq_of_dvd` is `dvd_topLeft_add_iff_eq_canonicalIndex` (lines 301-310) and
`dvd_add_mul_val_neg_mul_inv` is `dvd_topLeft_add_canonicalIndex` (lines 263-276).

Both are generalised here. The source states them for a matrix `M` with `M.det = 1`, in the entries
`M 0 0` and `M 1 0`; these take arbitrary coefficients `a c : ℤ` and assume only
`((c : ℤ) : ZMod p) ≠ 0`, since invertibility of that one coefficient is all the argument uses.
`b₀` is implicit, and the section supplies the binders the source passes explicitly.

**Neither proof is the source's.** AINTLIB proves uniqueness by rewriting through the `if`-split in
its own `moebiusFin`; here it is arithmetic in `ZMod p` — two indices satisfying the divisibility
differ by something `c` kills — and no group action appears. `existsUnique_dvd_add_mul` combines
the two and has no counterpart in the source, which never states existence and uniqueness together.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- **At most one index.** If `b₀` satisfies the divisibility then an index `i` satisfies it
exactly when `i = b₀`.

The hypothesis is only that the coefficient `c` is invertible mod `p` — the statement is
arithmetic in `ZMod p` and does not need the determinant, nor the Möbius action it conditions.
Stated as a divisibility over `ℤ`, which is the form the downstream Hecke sums are phrased in.

`existsUnique_dvd_add_mul` is the form to reach for when the pole index is not already in hand. -/
lemma dvd_add_mul_iff_eq_of_dvd (a c : ℤ) (hc : ((c : ℤ) : ZMod p) ≠ 0) {b₀ : Fin p}
    (hb₀ : (p : ℤ) ∣ (a + (b₀ : ℕ) * c)) (i : Fin p) :
    (p : ℤ) ∣ (a + (i : ℕ) * c) ↔ i = b₀ := by
  refine ⟨fun hi ↦ ?_, fun hji ↦ hji ▸ hb₀⟩
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hi
  have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hb₀
  push_cast at h1 h2
  refine (ZMod.finEquiv p).injective ?_
  rw [ZMod.finEquiv_apply, ZMod.finEquiv_apply]
  have hsub : (((i : ℕ) : ZMod p) - ((b₀ : ℕ) : ZMod p)) * ((c : ℤ) : ZMod p) = 0 := by
    linear_combination h1 - h2
  rcases mul_eq_zero.mp hsub with hz | hz
  · exact sub_eq_zero.mp hz
  · exact absurd hz hc

/-- **The pole index exists.** When the coefficient `c` is invertible mod `p` the denominator
does vanish somewhere, at the index `-a / c` read back into `Fin p`. With
`dvd_add_mul_iff_eq_of_dvd` this says the reindexing has *exactly one* pole index. -/
lemma dvd_add_mul_val_neg_mul_inv (a c : ℤ) (hc : ((c : ℤ) : ZMod p) ≠ 0) :
    (p : ℤ) ∣ (a +
      (((-((a : ℤ) : ZMod p) * ((c : ℤ) : ZMod p)⁻¹).val : ℕ)) * c) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]
  have hcancel : (-((a : ℤ) : ZMod p) * ((c : ℤ) : ZMod p)⁻¹) * ((c : ℤ) : ZMod p) =
      -((a : ℤ) : ZMod p) := by
    rw [mul_assoc, mul_comm ((c : ℤ) : ZMod p)⁻¹ _, mul_inv_cancel₀ hc, mul_one]
  rw [hcancel, add_neg_cancel]

/-- **Exactly one pole index.** When `c` is invertible mod `p` there is a unique index whose
denominator vanishes — the statement `dvd_add_mul_val_neg_mul_inv` and `dvd_add_mul_iff_eq_of_dvd`
combine to, and the one a consumer indexing by `Fin p` wants. -/
theorem existsUnique_dvd_add_mul (a c : ℤ) (hc : ((c : ℤ) : ZMod p) ≠ 0) :
    ∃! i : Fin p, (p : ℤ) ∣ (a + (i : ℕ) * c) := by
  refine ⟨(ZMod.finEquiv p).symm (-((a : ℤ) : ZMod p) * ((c : ℤ) : ZMod p)⁻¹), ?_, ?_⟩
  · simp only [ZMod.val_finEquiv_symm]
    exact dvd_add_mul_val_neg_mul_inv a c hc
  · intro y hy
    refine (dvd_add_mul_iff_eq_of_dvd a c hc ?_ y).mp hy
    simp only [ZMod.val_finEquiv_symm]
    exact dvd_add_mul_val_neg_mul_inv a c hc

end TauCeti

end
