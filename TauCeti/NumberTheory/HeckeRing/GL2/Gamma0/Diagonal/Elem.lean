/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.Associativity
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Coset

/-!
# The diagonal elements of the `Γ₀(N)` Hecke ring

`Gamma0/Diagonal/Coset.lean` builds the double coset `Γ₀(N)·diag(a)·Γ₀(N)` as a `HeckeCoset`.
This file turns it into an element of the Hecke ring `𝕋 (Δ₀(N)) (Γ₀(N))` — the level-`N`
analogue of `diagElem` — with the coprimality guard applied once so that the vanishing case is
stated in a single place rather than at each generator.

The module exists because the element's *type* mentions `𝕋`, which comes from
`HeckeRing.Associativity`. Keeping the definition here rather than in `Coset.lean`
leaves that file at the coset layer, where two of its three consumers
(`Gamma1/UpperTriCosets.lean` and `UpperTriangularDelta0.lean`) need nothing from the ring
theory; and keeping it here rather than in `PrimePower.lean` means a consumer wanting
only the general diagonal element does not import the prime-power recurrence.

## Main definitions

* `HeckeRing.GL2.diagElemGamma0`: the class of `Γ₀(N)·diag(a)·Γ₀(N)` in the Hecke ring, or `0`
  when the head entry shares a factor with the level.

## Main results

* `HeckeRing.GL2.diagElemGamma0_of_coprime`, `_of_not_coprime`, `_of_not_pos`: the three
  branches of the definition.
* `HeckeRing.GL2.diagElemGamma0_one`, `_one_one`: the identity normal forms, at the constant
  tuple and at the vector literal `![1, 1]`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3.
-/

public section

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups HeckeCosetModule

namespace HeckeRing.GL2

variable (N : ℕ)

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
`diagElem`. It sits in this file rather than beside `diagCosetGamma0` in `Coset.lean`
because its type mentions `𝕋`, which comes from `HeckeRing.Associativity` — an import
`Coset.lean` does not have, and which two of that file's three consumers do not need. -/
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

/-- **The identity normal form at the all-ones tuple**, mirroring `diagCosetGamma0_one`:
`diag(1, 1)` is the identity matrix, so its class is the ring identity. This is the case the
two generators below reduce to at argument `1`. -/
@[simp] lemma diagElemGamma0_one : diagElemGamma0 N (fun _ ↦ 1) = 1 := by
  rw [diagElemGamma0_of_coprime N (Nat.coprime_one_left N), diagCosetGamma0_one]
  exact (HeckeCosetModule.one_def ℤ).symm

/-- The same identity at the vector literal `![1, 1]`, which is the form both generators reduce
to at argument `1`. Stated once here so `heckeTScalarGamma0_one` and
`heckeTGeneratorGamma0_one` — which have different head symbols but the same underlying goal —
are each a single `exact` rather than two copies of the same script. -/
@[simp] lemma diagElemGamma0_one_one : diagElemGamma0 N ![1, 1] = 1 := by
  rw [show (![1, 1] : Fin 2 → ℕ) = fun _ ↦ 1 by ext i; fin_cases i <;> rfl]
  exact diagElemGamma0_one N

end HeckeRing.GL2

end
