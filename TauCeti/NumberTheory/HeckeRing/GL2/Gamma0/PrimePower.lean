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

This file introduces the two generating double cosets of the Hecke ring
`R(Γ₀(N), Δ₀(N))` and the prime-power elements built from them by the Diamond–Shurman
recurrence.

`heckeRingDp p` is the class of `diag(1, p)` and `heckeRingSpp p` the class of the scalar
matrix `diag(p, p)`, the latter vanishing when `p` is not coprime to the level — where
`diag(p, p) ∉ Δ₀(N)`, mirroring `⟨p⟩ = 0`. The prime-power element `heckeRingDppow p r`
satisfies `D_{p^0} = 1`, `D_{p^1} = D_p` and

`D_{p^{r+2}} = D_p · D_{p^{r+1}} − (p · S_p) · D_{p^r}`,

which for a bad prime degenerates to `D_{p^r} = D_p^r` because the scalar term vanishes.

Neither the per-prime product formula nor the composite element `D_n` assembled over a prime
factorisation is proved here; this file supplies the generators those need.

## Main definitions

* `HeckeRing.GL2.heckeRingDp`: the prime generator `Γ₀(N)·diag(1, p)·Γ₀(N)`.
* `HeckeRing.GL2.heckeRingSpp`: the scalar generator `Γ₀(N)·diag(p, p)·Γ₀(N)`, or `0`.
* `HeckeRing.GL2.heckeRingDppow`: the prime-power element.

## Main results

* `HeckeRing.GL2.heckeRingDppow_succ_succ`: the recurrence, as a rewriting rule.
* `HeckeRing.GL2.heckeRingDppow_eq_pow_of_not_coprime`: at a bad prime the recurrence
  degenerates to a power.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3.
* Ported from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck,
  `LeanModularForms/HeckeRIngs/GL2/Unified/Gamma0RingDn.lean`, declarations `heckeRingDp`,
  `heckeRingSpp`, `heckeRingSpp_of_not_coprime`, `heckeRingDppow`, `heckeRingDppow_zero`,
  `heckeRingDppow_one`, `heckeRingDppow_succ_succ` and `heckeRingDppow_eq_pow_of_not_coprime`.
  Three hypotheses of the source are dropped here: `heckeRingDp` no longer asks `0 < p`, and
  neither `heckeRingSpp` nor `heckeRingDppow` asks `Nat.Prime p` — none is needed to define the
  elements or to prove the recurrence, and carrying them would force every consumer to supply a
  primality proof for a statement that does not use it.
-/

public section

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups HeckeCosetModule

namespace HeckeRing.GL2

variable (N : ℕ) [NeZero N]

/-- The prime generator of the `Γ₀(N)` Hecke ring: the class of the double coset
`Γ₀(N)·diag(1, p)·Γ₀(N)`, including at a bad prime `p ∣ N`.

No coprimality is asked of `p`: the head entry of `![1, p]` is `1`, which is coprime to every
level. Only `p > 0` makes the definition meaningful — at `p = 0` the underlying `natDiagGL`
degenerates to the identity — but no consumer needs that as a hypothesis, so it is not
imposed. -/
noncomputable def heckeRingDp (p : ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  HeckeCosetModule.single ℤ (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N) 1

/-- The scalar generator of the `Γ₀(N)` Hecke ring: the class of `Γ₀(N)·diag(p, p)·Γ₀(N)` when
`p` is coprime to the level, and `0` otherwise — for `p` sharing a factor with `N` the matrix
`diag(p, p)` does not lie in `Δ₀(N)`, and the vanishing mirrors `⟨p⟩ = 0`.

Unlike `heckeRingDp` the coprimality here has content, because the head entry of `![p, p]`
is `p`. -/
noncomputable def heckeRingSpp (p : ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  if hpN : Nat.Coprime p N then
    HeckeCosetModule.single ℤ (diagCosetGamma0 N ![p, p] fun _ ↦ hpN) 1
  else 0

/-- The scalar generator vanishes at a bad prime. This is the case that lets the prime-power
recurrence below be stated without splitting on whether `p` divides the level. -/
@[simp]
theorem heckeRingSpp_of_not_coprime {p : ℕ} (hpN : ¬ Nat.Coprime p N) : heckeRingSpp N p = 0 :=
  dite_eq_right_of_eq_false (by simpa using hpN)

/-- The prime-power element, defined by the Diamond–Shurman recurrence `D_{p^0} = 1`,
`D_{p^1} = D_p` and `D_{p^{r+2}} = D_p · D_{p^{r+1}} − (p · S_p) · D_{p^r}`.

The recurrence is the one that makes `D_{p^r}` match the classical `T_{p^r}`; it is stated for
every `p`, and is intended at primes. -/
noncomputable def heckeRingDppow (p : ℕ) : ℕ → 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ
  | 0 => 1
  | 1 => heckeRingDp N p
  | r + 2 =>
    heckeRingDp N p * heckeRingDppow p (r + 1) - ((p : ℤ) • heckeRingSpp N p) * heckeRingDppow p r

-- The three equations below are `rfl` at the definition, but a `public` proof may not depend on
-- an unexposed body, so they are proved by unfolding rather than by `rfl`.
/-- The empty product: `D_{p^0} = 1`. -/
@[simp]
theorem heckeRingDppow_zero (p : ℕ) : heckeRingDppow N p 0 = 1 := by rw [heckeRingDppow]

/-- The first power is the prime generator itself: `D_{p^1} = D_p`. -/
@[simp]
theorem heckeRingDppow_one (p : ℕ) : heckeRingDppow N p 1 = heckeRingDp N p := by
  rw [heckeRingDppow]

/-- The `r + 2` case of the recurrence, as a rewriting rule. Not a `simp` lemma: the right-hand
side mentions `heckeRingDppow` at two smaller arguments, so it is a recursion to unfold
deliberately rather than a normal form to rewrite towards. -/
theorem heckeRingDppow_succ_succ (p r : ℕ) : heckeRingDppow N p (r + 2) = heckeRingDp N p *
    heckeRingDppow N p (r + 1) - ((p : ℤ) • heckeRingSpp N p) * heckeRingDppow N p r := by
  rw [heckeRingDppow]

/-- At a bad prime the scalar term vanishes and the recurrence degenerates to a power:
`D_{p^r} = D_p^r`. -/
theorem heckeRingDppow_eq_pow_of_not_coprime {p : ℕ} (hpN : ¬ Nat.Coprime p N) (r : ℕ) :
    heckeRingDppow N p r = heckeRingDp N p ^ r := by
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more r _ih0 ih1 =>
    simp [heckeRingDppow_succ_succ, heckeRingSpp_of_not_coprime N hpN, ih1, ← pow_succ']

end HeckeRing.GL2
