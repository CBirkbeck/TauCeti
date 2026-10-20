/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Preorder.Finite

/-!
# Bounds on root exponents in a free group

The cyclically reduced part of a nonidentity word has positive length. Consequently,
the exponent of any positive power representing a nonidentity element is bounded by
the length of that element's reduced word. This gives a root with greatest exponent,
the first step in constructing the intrinsic maximal root of a free-group element.

The length calculation follows the cyclic-reduction formula in Mathlib's
`FreeGroup.reduceCyclically.reduce_flatten_replicate`.
-/

public section

namespace FreeGroup

variable {α : Type*}

section

variable [DecidableEq α]

/-- A nonidentity free-group element has a nonempty cyclically reduced word. -/
theorem reduceCyclically_toWord_ne_nil {x : FreeGroup α} (hx : x ≠ 1) :
    reduceCyclically x.toWord ≠ [] := by
  intro h
  apply hx
  have hw := reduceCyclically.conj_conjugator_reduceCyclically x.toWord
  rw [h, List.append_nil] at hw
  have hm := congrArg mk hw
  simpa [← mul_mk, ← inv_mk, mk_toWord] using hm.symm

/-- The reduced-word length of a positive power is the length of the conjugating
prefix twice, plus the exponent times the cyclically reduced length. -/
theorem norm_pow_eq (x : FreeGroup α) {n : ℕ} (hn : 0 < n) :
    norm (x ^ n) = 2 * (reduceCyclically.conjugator x.toWord).length +
      n * (reduceCyclically x.toWord).length := by
  have hn0 : n ≠ 0 := by omega
  simp [norm, toWord_pow,
    reduceCyclically.reduce_flatten_replicate isReduced_toWord, hn0,
    List.length_flatten, List.map_replicate]
  omega

/-- The exponent of a nontrivial positive power cannot exceed its reduced-word length. -/
theorem pow_exponent_le_norm {x y : FreeGroup α} {n : ℕ}
    (hx : x ≠ 1) (hn : 0 < n) (hpow : y ^ n = x) : n ≤ norm x := by
  have hy : y ≠ 1 := by
    intro h
    rw [h, one_pow] at hpow
    exact hx hpow.symm
  have hl : 0 < (reduceCyclically y.toWord).length :=
    List.length_pos_iff_ne_nil.mpr (reduceCyclically_toWord_ne_nil hy)
  rw [← hpow, norm_pow_eq y hn]
  calc
    n = n * 1 := by omega
    _ ≤ n * (reduceCyclically y.toWord).length := Nat.mul_le_mul_left n hl
    _ ≤ 2 * (reduceCyclically.conjugator y.toWord).length +
      n * (reduceCyclically y.toWord).length := Nat.le_add_left _ _

end

/-- A nonidentity free-group element has a root whose exponent is greatest among
all of its positive root exponents. This root is not a positive proper power. -/
theorem exists_root_of_maximal_exponent {x : FreeGroup α} (hx : x ≠ 1) :
    ∃ r k, 0 < k ∧ r ^ k = x ∧
      (∀ (y : FreeGroup α) (n : ℕ), 0 < n → y ^ n = x → n ≤ k) ∧
      ∀ (y : FreeGroup α) (m : ℕ), 1 < m → y ^ m ≠ r := by
  classical
  let s : Set ℕ := {n | 0 < n ∧ ∃ y : FreeGroup α, y ^ n = x}
  have hs : s.Finite := (Set.finite_le_nat (norm x)).subset (by
    intro n hn
    obtain ⟨hn0, y, hy⟩ := hn
    exact pow_exponent_le_norm hx hn0 hy)
  have hne : s.Nonempty := ⟨1, by simp [s]⟩
  obtain ⟨k, hk⟩ := hs.exists_maximal hne
  obtain ⟨hk0, r, hr⟩ := hk.1
  have hmax : ∀ (y : FreeGroup α) (n : ℕ), 0 < n → y ^ n = x → n ≤ k := by
    intro y n hn hy
    exact le_of_not_gt (fun h ↦ (hk.2 ⟨hn, y, hy⟩ h.le).not_gt h)
  refine ⟨r, k, hk0, hr, hmax, ?_⟩
  intro y m hm hpower
  have hroot : y ^ (m * k) = x := by
    rw [pow_mul, hpower, hr]
  have hlt : k < m * k := by
    simpa using Nat.mul_lt_mul_of_pos_right hm hk0
  exact (hmax y (m * k) (by omega) hroot).not_gt hlt

end FreeGroup
