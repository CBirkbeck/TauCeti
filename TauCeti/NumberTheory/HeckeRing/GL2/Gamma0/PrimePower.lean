/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.Associativity
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DiagonalCoset

/-!
# The diagonal generators of the `Γ₀(N)` Hecke ring

This file introduces the diagonal elements of the Hecke ring `R(Γ₀(N), Δ₀(N))`, the two
generating classes built from them, and the family the Diamond–Shurman recurrence assembles.

`diagElemGamma0 a` takes three values, according to the tuple. It is `0` unless the head entry
`a 0` is coprime to the level — the guard `Δ₀(N)`-membership needs. Past that guard it is the
class of `Γ₀(N)·diag(a)·Γ₀(N)` when every entry is positive, and `1` when positivity fails,
since `natDiagGL` degenerates to the identity there. It is the level-`N` analogue of
`diagElem`. The two generators specialise it:
`heckeTGeneratorGamma0 p` at `![1, p]` and `heckeTScalarGamma0 p` at `![p, p]`. The iterated
family `heckeTGeneratorPowGamma0 p r` satisfies `T₀ = 1`, `T₁ = T_p` and

`T_{r+2} = T_p · T_{r+1} − (p · S_p) · T_r`,

which when `p` shares a factor with the level degenerates to `T_r = T_p^r`, the scalar term
having vanished.

Every declaration here is stated for an arbitrary natural `p`, and the names say so: they
follow `heckeTDiag`/`heckeTScalar`/`heckeT` at level one (`GL2/Basic.lean`), none of which
asks `Nat.Prime` either. The elements *are* the classical `T_p` and `T_{p^r}` of `Γ₀(N)`
exactly when `p` is prime — that is the intended reading, and the recurrence is chosen to
match it — but nothing below assumes it, so nothing below is named for it.

Neither the per-prime product formula nor the composite element assembled over a prime
factorisation is proved here; this file supplies the generators those need.

## Main definitions

* `HeckeRing.GL2.diagElemGamma0`: the level-`N` diagonal Hecke ring element, or `0`.
* `HeckeRing.GL2.heckeTGeneratorGamma0`: the generator `Γ₀(N)·diag(1, p)·Γ₀(N)`.
* `HeckeRing.GL2.heckeTScalarGamma0`: the scalar generator `Γ₀(N)·diag(p, p)·Γ₀(N)`, or `0`.
* `HeckeRing.GL2.heckeTGeneratorPowGamma0`: the family the recurrence generates.

## Main results

* `HeckeRing.GL2.diagElemGamma0_of_coprime`/`_of_not_coprime`: the two branches.
* `HeckeRing.GL2.heckeTGeneratorPowGamma0_succ_succ`: the recurrence, as a rewriting rule.
* `HeckeRing.GL2.heckeTGeneratorPowGamma0_eq_generator_pow_of_not_coprime`: when `p` shares a
  factor with the level, the recurrence degenerates to a power of the generator.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3.
* Diamond–Shurman, *A first course in modular forms*, §5.3 — the prime-power recurrence
  `T_{p^{r+1}} = T_p T_{p^r} − p^{k−1}⟨p⟩ T_{p^{r−1}}` this file's `heckeTGeneratorPowGamma0`
  transcribes to the ring.
* Ported from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck,
  `LeanModularForms/HeckeRIngs/GL2/Unified/Gamma0RingDn.lean`, declarations `heckeRingDp`,
  `heckeRingSpp`, `heckeRingSpp_of_not_coprime`, `heckeRingDppow`, `heckeRingDppow_zero`,
  `heckeRingDppow_one`, `heckeRingDppow_succ_succ` and
  `heckeRingDppow_eq_pow_of_not_coprime`. Three hypotheses of the source are dropped here: the
  generator no longer asks `0 < p`, and neither the scalar generator nor the iterated family
  asks `Nat.Prime p` — none is needed to define the elements or to prove the
  recurrence, and carrying them would force every consumer to supply a primality proof for a
  statement that does not use it. The names follow this namespace's `heckeT*` family rather
  than the source's `heckeRing*`, and drop the source's `p`/`prime` vocabulary along with the
  hypothesis it stood for.
-/

public section

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups HeckeCosetModule

namespace HeckeRing.GL2

variable (N : ℕ) [NeZero N]

/-- The level-`N` diagonal element of the Hecke ring, `0` unless the head entry `a 0` is
coprime to the level.

Inside the coprime branch the value still depends on the tuple, and the three cases are worth
keeping straight:

* `¬ Nat.Coprime (a 0) N` — the element is `0` (`diagElemGamma0_of_not_coprime`);
* coprime head, every entry positive — the class of `Γ₀(N)·diag(a)·Γ₀(N)`, the intended case;
* coprime head, positivity failing — the element is `1` (`diagElemGamma0_of_not_pos`), because
  the underlying `natDiagGL` degenerates to the identity matrix rather than being undefined.

The coprimality guard is what `Δ₀(N)`-membership needs, and putting it here rather than at each
generator means the vanishing case is stated once. This is the level-`N` analogue of
`diagElem`; it cannot live beside `diagCosetGamma0` in `DiagonalCoset.lean` because the ring
structure needs `[NeZero N]`. -/
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

-- Deliberately not `@[simp]`, unlike the `diagCosetGamma0_of_not_pos` this is built on. That one
-- takes its coprimality *conditionally*, as `(∀ i, 0 < a i) → Nat.Coprime (a 0) N`, so the
-- hypothesis is vacuous in this branch and is carried inside the term. `diagElemGamma0` instead
-- guards with a `dite`, so this lemma needs `Nat.Coprime (a 0) N` outright — a side condition
-- `simp` cannot discharge for a variable `a`, and one on which the `@[simp]`
-- `diagElemGamma0_of_not_coprime` takes the *same* left-hand side to `0`. Tagging it makes
-- `simpNF` report that the left-hand side never simplifies and the rule would never fire;
-- restating the positivity hypothesis in its simp-normal form `0 < a 0 → a 1 = 0` does not change
-- that. Both were measured.
/-- The identity normal form: a coprime-headed tuple that is not everywhere positive gives `1`,
since the underlying `natDiagGL` degenerates to the identity matrix. -/
lemma diagElemGamma0_of_not_pos {a : Fin 2 → ℕ} (hcop : Nat.Coprime (a 0) N)
    (ha : ¬ ∀ i, 0 < a i) : diagElemGamma0 N a = 1 := by
  rw [diagElemGamma0_of_coprime N hcop, diagCosetGamma0_of_not_pos N _ ha]
  exact (HeckeCosetModule.one_def ℤ).symm

/-- The diagonal generator of the `Γ₀(N)` Hecke ring: the class of `Γ₀(N)·diag(1, p)·Γ₀(N)`,
for any natural `p`, including one sharing a factor with the level. At a prime `p` this is the
classical `T_p`.

No coprimality is asked of `p`: the head entry of `![1, p]` is `1`, which is coprime to every
level, so `diagElemGamma0` always takes its nonzero branch here. Only `p > 0` makes the
definition interesting — at `p = 0` the underlying `natDiagGL` degenerates to the identity and
the element is `1` — but no consumer needs that as a hypothesis, so it is not imposed. -/
noncomputable def heckeTGeneratorGamma0 (p : ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  diagElemGamma0 N ![1, p]

/-- The scalar generator of the `Γ₀(N)` Hecke ring: the class of `Γ₀(N)·diag(p, p)·Γ₀(N)` when
`p` is coprime to the level, and `0` otherwise.

Unlike `heckeTGeneratorGamma0` the coprimality here has content, because the head entry of
`![p, p]` is `p`. For `0 < p` sharing a factor with `N` the vanishing is a membership fact —
`diag(p, p) ∉ Δ₀(N)` — and mirrors `⟨p⟩ = 0`. At `p = 0` it is instead a junk-value
convention: `natDiagGL 2 ![0, 0]` is the identity and so *does* lie in `Δ₀(N)`, but `0` is not
coprime to `N > 1`, so the guard still sends the element to `0`. -/
noncomputable def heckeTScalarGamma0 (p : ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  diagElemGamma0 N ![p, p]

/-- Defining equation for the diagonal generator: the guard is discharged by
`Nat.coprime_one_left`, so it is always the class of the double coset. -/
lemma heckeTGeneratorGamma0_def (p : ℕ) :
    heckeTGeneratorGamma0 N p =
      HeckeCosetModule.single ℤ
        (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N) 1 :=
  diagElemGamma0_of_coprime N (Nat.coprime_one_left N)

/-- The scalar generator in the coprime branch, where it is nonzero. -/
lemma heckeTScalarGamma0_of_coprime {p : ℕ} (hpN : Nat.Coprime p N) :
    heckeTScalarGamma0 N p =
      HeckeCosetModule.single ℤ (diagCosetGamma0 N ![p, p] fun _ ↦ hpN) 1 :=
  diagElemGamma0_of_coprime N hpN

/-- The scalar generator vanishes when `p` shares a factor with the level. This is the case
that lets the recurrence below be stated without splitting on whether `p` divides `N`. -/
@[simp]
theorem heckeTScalarGamma0_of_not_coprime {p : ℕ} (hpN : ¬ Nat.Coprime p N) :
    heckeTScalarGamma0 N p = 0 :=
  diagElemGamma0_of_not_coprime N hpN

/-- At `p = 0` the generator is the identity: `![1, 0]` is not everywhere positive. -/
@[simp]
theorem heckeTGeneratorGamma0_zero : heckeTGeneratorGamma0 N 0 = 1 :=
  diagElemGamma0_of_not_pos N (Nat.coprime_one_left N) fun h ↦ absurd (h 1) (by simp)

/-- The family generated from `heckeTGeneratorGamma0` by the Diamond–Shurman recurrence
`T₀ = 1`, `T₁ = T_p` and `T_{r+2} = T_p · T_{r+1} − (p · S_p) · T_r`.

The recurrence is chosen so that at a prime `p` the `r`-th term is the classical `T_{p^r}`,
but it is defined for every natural `p` and nothing here assumes primality. -/
noncomputable def heckeTGeneratorPowGamma0 (p : ℕ) : ℕ → 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ
  | 0 => 1
  | 1 => heckeTGeneratorGamma0 N p
  | r + 2 =>
    heckeTGeneratorGamma0 N p * heckeTGeneratorPowGamma0 p (r + 1) -
      ((p : ℤ) • heckeTScalarGamma0 N p) * heckeTGeneratorPowGamma0 p r

-- The three equations below hold by `rfl`, but a bare `rfl` proof would export the definitional
-- equality of `heckeTGeneratorPowGamma0`, whose body is sealed (`public section`, no
-- `@[expose]`). Unfolding through the equation lemmas with `rw` states them without doing so.
-- Inside this module a public proof may still *use* a sealed body — see
-- `heckeTScalarGamma0_of_not_coprime` above — it is only the exported defeq that is refused.
/-- The empty product: `T₀ = 1`. -/
@[simp]
theorem heckeTGeneratorPowGamma0_zero (p : ℕ) : heckeTGeneratorPowGamma0 N p 0 = 1 := by
  rw [heckeTGeneratorPowGamma0]

/-- The first term is the generator itself: `T₁ = T_p`. -/
@[simp]
theorem heckeTGeneratorPowGamma0_one (p : ℕ) :
    heckeTGeneratorPowGamma0 N p 1 = heckeTGeneratorGamma0 N p := by
  rw [heckeTGeneratorPowGamma0]

/-- The `r + 2` case of the recurrence, as a rewriting rule. Not a `simp` lemma: the right-hand
side mentions `heckeTGeneratorPowGamma0` at two smaller arguments, so it is a recursion to
unfold deliberately rather than a normal form to rewrite towards. -/
theorem heckeTGeneratorPowGamma0_succ_succ (p r : ℕ) :
    heckeTGeneratorPowGamma0 N p (r + 2) = heckeTGeneratorGamma0 N p *
      heckeTGeneratorPowGamma0 N p (r + 1) -
        ((p : ℤ) • heckeTScalarGamma0 N p) * heckeTGeneratorPowGamma0 N p r := by
  rw [heckeTGeneratorPowGamma0]

/-- When `p` shares a factor with the level the scalar term vanishes and the recurrence
degenerates to a power of the generator: `T_r = T_p^r`. -/
theorem heckeTGeneratorPowGamma0_eq_generator_pow_of_not_coprime {p : ℕ}
    (hpN : ¬ Nat.Coprime p N) (r : ℕ) :
    heckeTGeneratorPowGamma0 N p r = heckeTGeneratorGamma0 N p ^ r := by
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more r _ih0 ih1 =>
    simp [heckeTGeneratorPowGamma0_succ_succ, heckeTScalarGamma0_of_not_coprime N hpN, ih1,
      ← pow_succ']

end HeckeRing.GL2
