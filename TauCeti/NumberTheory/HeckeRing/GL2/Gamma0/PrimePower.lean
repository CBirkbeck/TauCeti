/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.Associativity
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DiagonalCoset

/-!
# The prime and prime-power generators of the `Γ₀(N)` Hecke ring

This file introduces the diagonal elements of the Hecke ring `R(Γ₀(N), Δ₀(N))`, the two
generating classes built from them, and the prime-power elements assembled by the
Diamond–Shurman recurrence.

`diagElemGamma0 a` is the class of `Γ₀(N)·diag(a)·Γ₀(N)` when the head entry `a 0` is coprime
to the level, and `0` otherwise — the level-`N` analogue of `diagElem`, carrying the
coprimality guard that `Δ₀(N)`-membership needs. The two generators specialise it:
`heckeTPrimeGamma0 p` at `![1, p]` and `heckeTScalarGamma0 p` at `![p, p]`. The prime-power
element `heckeTPrimePowGamma0 p r` satisfies `T_{p^0} = 1`, `T_{p^1} = T_p` and

`T_{p^{r+2}} = T_p · T_{p^{r+1}} − (p · S_p) · T_{p^r}`,

which for a bad prime degenerates to `T_{p^r} = T_p^r` because the scalar term vanishes.

Neither the per-prime product formula nor the composite element assembled over a prime
factorisation is proved here; this file supplies the generators those need.

## Main definitions

* `HeckeRing.GL2.diagElemGamma0`: the level-`N` diagonal Hecke ring element, or `0`.
* `HeckeRing.GL2.heckeTPrimeGamma0`: the prime generator `Γ₀(N)·diag(1, p)·Γ₀(N)`.
* `HeckeRing.GL2.heckeTScalarGamma0`: the scalar generator `Γ₀(N)·diag(p, p)·Γ₀(N)`, or `0`.
* `HeckeRing.GL2.heckeTPrimePowGamma0`: the prime-power element.

## Main results

* `HeckeRing.GL2.diagElemGamma0_of_coprime`/`_of_not_coprime`: the two branches.
* `HeckeRing.GL2.heckeTPrimePowGamma0_succ_succ`: the recurrence, as a rewriting rule.
* `HeckeRing.GL2.heckeTPrimePowGamma0_eq_pow_of_not_coprime`: at a bad prime the recurrence
  degenerates to a power.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3.
* Diamond–Shurman, *A first course in modular forms*, §5.3 — the prime-power recurrence
  `T_{p^{r+1}} = T_p T_{p^r} − p^{k−1}⟨p⟩ T_{p^{r−1}}` this file's `heckeTPrimePowGamma0`
  transcribes to the ring.
* Ported from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck,
  `LeanModularForms/HeckeRIngs/GL2/Unified/Gamma0RingDn.lean`, declarations `heckeRingDp`,
  `heckeRingSpp`, `heckeRingSpp_of_not_coprime`, `heckeRingDppow`, `heckeRingDppow_zero`,
  `heckeRingDppow_one`, `heckeRingDppow_succ_succ` and
  `heckeRingDppow_eq_pow_of_not_coprime`. Three hypotheses of the source are dropped here: the
  prime generator no longer asks `0 < p`, and neither the scalar generator nor the prime-power
  element asks `Nat.Prime p` — none is needed to define the elements or to prove the
  recurrence, and carrying them would force every consumer to supply a primality proof for a
  statement that does not use it. The names follow this namespace's `heckeT*` family rather
  than the source's `heckeRing*`.
-/

public section

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups HeckeCosetModule

namespace HeckeRing.GL2

variable (N : ℕ) [NeZero N]

/-- The level-`N` diagonal element of the Hecke ring: the class of `Γ₀(N)·diag(a)·Γ₀(N)` when
the head entry `a 0` is coprime to the level, and `0` otherwise.

The guard is what `Δ₀(N)`-membership needs, and putting it here rather than at each generator
means the vanishing case is stated once. This is the level-`N` analogue of `diagElem`; it
cannot live beside `diagCosetGamma0` in `DiagonalCoset.lean` because the ring structure needs
`[NeZero N]`. -/
noncomputable def diagElemGamma0 (a : Fin 2 → ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  if h : Nat.Coprime (a 0) N then
    HeckeCosetModule.single ℤ (diagCosetGamma0 N a fun _ ↦ h) 1
  else 0

/-- Defining equation in the coprime branch: the element is the class of the double coset. -/
lemma diagElemGamma0_of_coprime {a : Fin 2 → ℕ} (h : Nat.Coprime (a 0) N) :
    diagElemGamma0 N a = HeckeCosetModule.single ℤ (diagCosetGamma0 N a fun _ ↦ h) 1 := by
  rw [diagElemGamma0, dite_eq_left_of_eq_true (eq_true h)]

/-- The diagonal element vanishes when the head entry shares a factor with the level. -/
@[simp]
theorem diagElemGamma0_of_not_coprime {a : Fin 2 → ℕ} (h : ¬ Nat.Coprime (a 0) N) :
    diagElemGamma0 N a = 0 := by
  rw [diagElemGamma0, dite_eq_right_of_eq_false (eq_false h)]

/-- The identity normal form: a tuple that is not everywhere positive gives `1`, since the
underlying `natDiagGL` degenerates to the identity matrix. -/
lemma diagElemGamma0_of_not_pos {a : Fin 2 → ℕ} (hcop : Nat.Coprime (a 0) N)
    (ha : ¬ ∀ i, 0 < a i) : diagElemGamma0 N a = 1 := by
  rw [diagElemGamma0_of_coprime N hcop, diagCosetGamma0_of_not_pos N _ ha]
  exact (HeckeCosetModule.one_def ℤ).symm

/-- The prime generator of the `Γ₀(N)` Hecke ring: the class of `Γ₀(N)·diag(1, p)·Γ₀(N)`,
including at a bad prime `p ∣ N`.

No coprimality is asked of `p`: the head entry of `![1, p]` is `1`, which is coprime to every
level, so `diagElemGamma0` always takes its nonzero branch here. Only `p > 0` makes the
definition interesting — at `p = 0` the underlying `natDiagGL` degenerates to the identity and
the element is `1` — but no consumer needs that as a hypothesis, so it is not imposed. -/
noncomputable def heckeTPrimeGamma0 (p : ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  diagElemGamma0 N ![1, p]

/-- The scalar generator of the `Γ₀(N)` Hecke ring: the class of `Γ₀(N)·diag(p, p)·Γ₀(N)` when
`p` is coprime to the level, and `0` otherwise.

Unlike `heckeTPrimeGamma0` the coprimality here has content, because the head entry of
`![p, p]` is `p`. For `0 < p` sharing a factor with `N` the vanishing is a membership fact —
`diag(p, p) ∉ Δ₀(N)` — and mirrors `⟨p⟩ = 0`. At `p = 0` it is instead a junk-value
convention: `natDiagGL 2 ![0, 0]` is the identity and so *does* lie in `Δ₀(N)`, but `0` is not
coprime to `N > 1`, so the guard still sends the element to `0`. -/
noncomputable def heckeTScalarGamma0 (p : ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  diagElemGamma0 N ![p, p]

/-- Defining equation for the prime generator: the guard is discharged by
`Nat.coprime_one_left`, so it is always the class of the double coset. -/
lemma heckeTPrimeGamma0_def (p : ℕ) :
    heckeTPrimeGamma0 N p =
      HeckeCosetModule.single ℤ
        (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N) 1 :=
  diagElemGamma0_of_coprime N (Nat.coprime_one_left N)

/-- The scalar generator in the coprime branch, where it is nonzero. -/
lemma heckeTScalarGamma0_of_coprime {p : ℕ} (hpN : Nat.Coprime p N) :
    heckeTScalarGamma0 N p =
      HeckeCosetModule.single ℤ (diagCosetGamma0 N ![p, p] fun _ ↦ hpN) 1 :=
  diagElemGamma0_of_coprime N hpN

/-- The scalar generator vanishes at a bad prime. This is the case that lets the prime-power
recurrence below be stated without splitting on whether `p` divides the level. -/
@[simp]
theorem heckeTScalarGamma0_of_not_coprime {p : ℕ} (hpN : ¬ Nat.Coprime p N) :
    heckeTScalarGamma0 N p = 0 :=
  diagElemGamma0_of_not_coprime N hpN

/-- At `p = 0` the prime generator is the identity: `![1, 0]` is not everywhere positive. -/
@[simp]
theorem heckeTPrimeGamma0_zero : heckeTPrimeGamma0 N 0 = 1 :=
  diagElemGamma0_of_not_pos N (Nat.coprime_one_left N) fun h ↦ absurd (h 1) (by simp)

/-- The prime-power element, defined by the Diamond–Shurman recurrence `T_{p^0} = 1`,
`T_{p^1} = T_p` and `T_{p^{r+2}} = T_p · T_{p^{r+1}} − (p · S_p) · T_{p^r}`.

The recurrence is the one that makes `T_{p^r}` match the classical `T_{p^r}`; it is stated for
every `p`, and is intended at primes. -/
noncomputable def heckeTPrimePowGamma0 (p : ℕ) : ℕ → 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ
  | 0 => 1
  | 1 => heckeTPrimeGamma0 N p
  | r + 2 =>
    heckeTPrimeGamma0 N p * heckeTPrimePowGamma0 p (r + 1) -
      ((p : ℤ) • heckeTScalarGamma0 N p) * heckeTPrimePowGamma0 p r

-- The three equations below hold by `rfl`, but a bare `rfl` proof would export the
-- definitional equality of `heckeTPrimePowGamma0`, whose body is sealed (`public section`, no
-- `@[expose]`). Unfolding through the equation lemmas with `rw` states them without doing so.
-- Inside this module a public proof may still *use* a sealed body — see
-- `heckeTScalarGamma0_of_not_coprime` above — it is only the exported defeq that is refused.
/-- The empty product: `T_{p^0} = 1`. -/
@[simp]
theorem heckeTPrimePowGamma0_zero (p : ℕ) : heckeTPrimePowGamma0 N p 0 = 1 := by
  rw [heckeTPrimePowGamma0]

/-- The first power is the prime generator itself: `T_{p^1} = T_p`. -/
@[simp]
theorem heckeTPrimePowGamma0_one (p : ℕ) :
    heckeTPrimePowGamma0 N p 1 = heckeTPrimeGamma0 N p := by
  rw [heckeTPrimePowGamma0]

/-- The `r + 2` case of the recurrence, as a rewriting rule. Not a `simp` lemma: the right-hand
side mentions `heckeTPrimePowGamma0` at two smaller arguments, so it is a recursion to unfold
deliberately rather than a normal form to rewrite towards. -/
theorem heckeTPrimePowGamma0_succ_succ (p r : ℕ) :
    heckeTPrimePowGamma0 N p (r + 2) = heckeTPrimeGamma0 N p *
      heckeTPrimePowGamma0 N p (r + 1) -
        ((p : ℤ) • heckeTScalarGamma0 N p) * heckeTPrimePowGamma0 N p r := by
  rw [heckeTPrimePowGamma0]

/-- At a bad prime the scalar term vanishes and the recurrence degenerates to a power:
`T_{p^r} = T_p^r`. -/
theorem heckeTPrimePowGamma0_eq_pow_of_not_coprime {p : ℕ} (hpN : ¬ Nat.Coprime p N) (r : ℕ) :
    heckeTPrimePowGamma0 N p r = heckeTPrimeGamma0 N p ^ r := by
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more r _ih0 ih1 =>
    simp [heckeTPrimePowGamma0_succ_succ, heckeTScalarGamma0_of_not_coprime N hpN, ih1,
      ← pow_succ']

end HeckeRing.GL2
