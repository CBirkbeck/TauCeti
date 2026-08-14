/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.NumberTheory.EllipticDivisibilitySequence
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Transfer

/-!
# Expanding a product of an elliptic atom with an elliptic relator

The descent that recovers the full four-index elliptic relation from the two doubling
recurrences works by rewriting a relator on four unconstrained indices into relators that all
carry a fixed pair `c, d` of small indices. This file supplies the algebraic identities that
perform that rewriting; the ordering and parity bookkeeping that makes the resulting induction
terminate is in `Transfer.lean`.

All four are polynomial identities in the atoms: `atomRel` is a fixed quadratic expression in
`atom`, so each statement expands on both sides to a combination of products of two atoms, and
`ring` closes it. No index arithmetic is involved — the atoms' arguments are carried along
unchanged — which is why nothing here needs the parity hypotheses that `atom_even`, `atom_odd`
and `atomRel_eq` require.

## Main results

* `atom_mul_atomRel_eq_of_last_eq_fst`, `atom_mul_atomRel_eq_of_last_eq_snd`: when the relator's
  last index is already one of the atom's two indices, the product is a three-term combination.
* `atom_mul_atomRel_eq`: for four unconstrained relator indices, a ten-term combination.
* `atom_sq_mul_atomRel_eq`: the nine-term combination obtained from the previous two, which is
  the form the descent actually consumes.

## Provenance

Adapted from J. Xu's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declarations `rel₆_eq₃`, `rel₆_eq₃'`, `rel₆_eq₁₀`
and `addMulSub_sq_mul_rel₄_eq₉`. That file's header reads `Authors: Junyan Xu`; following this
repository's convention for adapted material the upstream authorship is credited here rather
than in the copyright header.

The source states these against its own `addMulSub` and `rel₄`, which Mathlib now supplies as
`IsEllipticNet.atom` and `IsEllipticNet.atomRel` with the same definitions, so the statements
transfer by renaming. The source also carries an abbreviation `rel₆ W k l a b c d` for the
product `addMulSub W k l * rel₄ W a b c d`, together with a `@[simp]` lemma unfolding it. That
abbreviation is **not** ported: it names a product rather than a concept, it exists only to
shorten these four statements, and a wrapper whose sole purpose is to be unfolded again at
every use site is a second public spelling of `atom _ _ * atomRel _ _ _ _`. The statements below
therefore write the product out.
-/

public section

namespace IsEllipticNet

variable {R : Type*} [CommRing R] (W : ℤ → R)

/-- **Expanding over a fixed pair, when the relator already ends at the atom's first index.**
Each relator on the right carries both `c` and `d`, so this trades one occurrence of `c` for
the pair `c, d`. -/
theorem atom_mul_atomRel_eq_of_last_eq_fst (c d m n r : ℤ) :
    atom W c d * atomRel W m n r c =
      atom W m c * atomRel W n r c d - atom W n c * atomRel W m r c d
        + atom W r c * atomRel W m n c d := by
  simp_rw [atomRel]; ring

/-- **Expanding over a fixed pair, when the relator already ends at the atom's second index.**
The companion of `atom_mul_atomRel_eq_of_last_eq_fst` with the roles of `c` and `d` exchanged
in the atoms, the relators on the right being the same three. -/
theorem atom_mul_atomRel_eq_of_last_eq_snd (c d m n r : ℤ) :
    atom W c d * atomRel W m n r d =
      atom W m d * atomRel W n r c d - atom W n d * atomRel W m r c d
        + atom W r d * atomRel W m n c d := by
  simp_rw [atomRel]; ring

/-- **Expanding over a fixed pair, for four unconstrained relator indices.** Every relator on
the right has at least one index drawn from the fixed pair `c, d`, which is what lets the
descent lower the indices it is working on. -/
theorem atom_mul_atomRel_eq (c d m n r s : ℤ) :
    atom W c d * atomRel W m n r s =
      atom W n d * atomRel W m r s c - atom W r d * atomRel W m n s c
        + atom W s d * atomRel W m n r c
      + atom W n c * atomRel W m r s d - atom W r c * atomRel W m n s d
        + atom W s c * atomRel W m n r d
      + atom W n r * atomRel W m s c d - atom W n s * atomRel W m r c d
        + atom W r s * atomRel W m n c d
      - 2 * (atom W m d * atomRel W n r s c) := by
  simp_rw [atomRel]; ring

/-- **The squared-atom form, in which every relator on the right carries the whole fixed pair.**
This is the shape the descent consumes: the first two bracketed groups are the right-hand sides
of `atom_mul_atomRel_eq_of_last_eq_snd` and `…_fst`, and the third is the last group of
`atom_mul_atomRel_eq`. Squaring the atom is the price of having no index left outside `c, d`. -/
theorem atom_sq_mul_atomRel_eq (c d m n r s : ℤ) :
    atom W c d ^ 2 * atomRel W m n r s =
      atom W m c * (atom W n d * atomRel W r s c d - atom W r d * atomRel W n s c d
        + atom W s d * atomRel W n r c d)
      - atom W m d * (atom W n c * atomRel W r s c d - atom W r c * atomRel W n s c d
        + atom W s c * atomRel W n r c d)
      + atom W c d * (atom W n r * atomRel W m s c d - atom W n s * atomRel W m r c d
        + atom W r s * atomRel W m n c d) := by
  simp_rw [atomRel]; ring

open scoped nonZeroDivisors

/-- **The relator vanishes at a valid quadruple.** "Valid" is: one parity, nonnegative, strictly
decreasing. The two hypotheses live inside the predicate rather than outside it because the
descent applies its induction hypothesis at quadruples whose validity is not known in advance;
carrying them here means the recursive call is a `Prop` about indices alone. -/
def AtomRelVanishes (a b c d : ℤ) : Prop :=
  (d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2) → NonnegStrictAnti₄ a b c d →
    atomRel W a b c d = 0

variable {W}

/-- The minimal same-parity pair above zero, `(a % 2 + 2, a % 2)`, has its atom a nonzerodivisor
as soon as `W 1` and `W 2` are: the two parities give `W 1 * W 1` and `W 2 * W 1`. -/
private theorem atom_emod_mem_nonZeroDivisors (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (a : ℤ) :
    atom W (a % 2 + 2) (a % 2) ∈ R⁰ := by
  rcases Int.emod_two_eq_zero_or_one a with h | h <;> rw [h] <;> norm_num [atom] <;>
    exact mul_mem ‹_› ‹_›

/-- The three relators common to both expansions used by `atomRelVanishes_of_forall_le`. Each
carries the fixed pair `c₀, d₀` in its last two places and a first index at most `a`, so each is
in range of the descent hypothesis; the chain `d₀ < c₀ < c < b < a` is what makes all three
valid quadruples. -/
private theorem atomRel_triple_eq_zero {a b c c₀ d₀ : ℤ}
    (rel : ∀ {a' b' : ℤ}, a' ≤ a → AtomRelVanishes W a' b' c₀ d₀)
    (par : c₀ % 2 = d₀ % 2) (same : d₀ % 2 = a % 2 ∧ d₀ % 2 = b % 2 ∧ d₀ % 2 = c % 2)
    (le : 0 ≤ d₀) (lt : d₀ < c₀) (hc : c₀ < c) (hcb : c < b) (hba : b < a) :
    atomRel W b c c₀ d₀ = 0 ∧ atomRel W a c c₀ d₀ = 0 ∧ atomRel W a b c₀ d₀ = 0 := by
  obtain ⟨ha, hb, hcc⟩ := same
  refine ⟨rel hba.le ⟨by omega, by omega, by omega⟩ ?_,
    rel le_rfl ⟨by omega, by omega, by omega⟩ ?_,
    rel le_rfl ⟨by omega, by omega, by omega⟩ ?_⟩ <;>
    rw [nonnegStrictAnti₄_iff] <;> omega

/-- **Lowering the last index onto a fixed pair.** Given vanishing at every quadruple
`(a', b, c₀, d₀)` with `a' ≤ a`, the relator vanishes at `(a, b, c, c₀)` outright, and at
`(a, b, c, d₀)` once `c₀ < c`. Both follow from a three-term expansion trading the relator's
last index for the pair `c₀, d₀`, after which every summand carries a factor already known to
vanish. -/
theorem atomRelVanishes_of_forall_le {a c₀ d₀ : ℤ} (par : c₀ % 2 = d₀ % 2) (le : 0 ≤ d₀)
    (lt : d₀ < c₀) (rel : ∀ {a' b : ℤ}, a' ≤ a → AtomRelVanishes W a' b c₀ d₀)
    (mem : atom W c₀ d₀ ∈ R⁰) (b c : ℤ) :
    AtomRelVanishes W a b c c₀ ∧ (c₀ < c → AtomRelVanishes W a b c d₀) := by
  constructor
  · intro same anti
    rw [nonnegStrictAnti₄_iff] at anti
    obtain ⟨-, hc, hcb, hba⟩ := anti
    obtain ⟨h₁, h₂, h₃⟩ := atomRel_triple_eq_zero rel par
      ⟨by omega, by omega, by omega⟩ le lt hc hcb hba
    refine mem.2 _ ?_
    rw [mul_comm, atom_mul_atomRel_eq_of_last_eq_fst, h₁, h₂, h₃]
    ring
  · intro hc same anti
    rw [nonnegStrictAnti₄_iff] at anti
    obtain ⟨-, hdc, hcb, hba⟩ := anti
    obtain ⟨h₁, h₂, h₃⟩ := atomRel_triple_eq_zero rel par
      ⟨by omega, by omega, by omega⟩ le lt hc hcb hba
    refine mem.2 _ ?_
    rw [mul_comm, atom_mul_atomRel_eq_of_last_eq_snd, h₁, h₂, h₃]
    ring

/-- **Lowering an unconstrained last index.** With the previous lemma available at every `b, c`,
the ten-term expansion reaches a quadruple whose last index `d` is merely above `c₀`: each of
the ten summands carries a relator that either already ends at the fixed pair or is reachable
from it, and so vanishes. -/
theorem atomRelVanishes_of_lt {a c₀ d₀ : ℤ} (par : c₀ % 2 = d₀ % 2) (le : 0 ≤ d₀) (lt : d₀ < c₀)
    (rel : ∀ {a' b : ℤ}, a' ≤ a → AtomRelVanishes W a' b c₀ d₀) (mem : atom W c₀ d₀ ∈ R⁰)
    (b c d : ℤ) (hc : c₀ < d) (par' : d % 2 = d₀ % 2) :
    AtomRelVanishes W a b c d := by
  intro same anti
  rw [nonnegStrictAnti₄_iff] at anti
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  obtain ⟨hda, hdb, hdc'⟩ := same
  have fix₁ (b' c' : ℤ) := (atomRelVanishes_of_forall_le par le lt rel mem b' c').1
  have fix₂ (b' c' : ℤ) := (atomRelVanishes_of_forall_le par le lt rel mem b' c').2
  have fixb (b' c' : ℤ) :=
    (atomRelVanishes_of_forall_le par le lt (fun h ↦ rel (h.trans hba.le)) mem b' c').1
  have e₁ := fix₁ c d ⟨by omega, by omega, by omega⟩ (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₂ := fix₁ b d ⟨by omega, by omega, by omega⟩ (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₃ := fix₁ b c ⟨by omega, by omega, by omega⟩ (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₄ := fix₂ c d hc ⟨by omega, by omega, by omega⟩ (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₅ := fix₂ b d hc ⟨by omega, by omega, by omega⟩ (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₆ := fix₂ b c (by omega) ⟨by omega, by omega, by omega⟩
    (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₇ := rel (b := d) le_rfl ⟨by omega, by omega, by omega⟩
    (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₈ := rel (b := c) le_rfl ⟨by omega, by omega, by omega⟩
    (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₉ := rel (b := b) le_rfl ⟨by omega, by omega, by omega⟩
    (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₁₀ := fixb c d ⟨by omega, by omega, by omega⟩ (by rw [nonnegStrictAnti₄_iff]; omega)
  refine mem.2 _ ?_
  rw [mul_comm, atom_mul_atomRel_eq, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, e₁₀]
  ring

/-- **Only the minimal pair needs checking.** If the relator vanishes at every quadruple whose
last two indices are the minimal same-parity pair `(a % 2 + 2, a % 2)`, it vanishes at every
valid quadruple with first index `a`. The three remaining cases are `d` above the pair, `d` at
its top, and `d` at its bottom; in the `%2` spelling each is closed by `omega`, where the source
needed a chain of `Int.negOnePow` lemmas. -/
theorem atomRelVanishes_of_min {a : ℤ} (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (rel : ∀ {a' b : ℤ}, a' ≤ a → AtomRelVanishes W a' b (a % 2 + 2) (a % 2)) (b c d : ℤ) :
    AtomRelVanishes W a b c d := by
  intro same anti
  have par : (a % 2 + 2) % 2 = a % 2 % 2 := by omega
  have le : (0 : ℤ) ≤ a % 2 := by omega
  have lt : a % 2 < a % 2 + 2 := by omega
  have mem := atom_emod_mem_nonZeroDivisors one two (W := W) a
  have hda := same.1
  obtain ⟨hd, hdc, hcb, hba⟩ := (nonnegStrictAnti₄_iff a b c d).mp anti
  rcases lt_or_ge (a % 2 + 2) d with hlt | hge
  · exact atomRelVanishes_of_lt par le lt rel mem b c d hlt (by omega) same anti
  have fix := atomRelVanishes_of_forall_le par le lt rel mem b c
  rcases hge.eq_or_lt with heq | hlt₂
  · subst heq; exact fix.1 same anti
  · have hdm : d = a % 2 := by omega
    subst hdm
    rcases (show a % 2 + 2 = c ∨ a % 2 + 2 < c by omega) with heq₂ | hlt₃
    · subst heq₂; exact rel le_rfl same anti
    · exact fix.2 hlt₃ same anti

/-- The even base case, as a relator: all four indices are even, so `atomRel_two_mul` applies. -/
private theorem atomRel_even_eq_rel (m : ℤ) :
    atomRel W (2 * m) (2 * (m - 1)) (2 * 1) (2 * 0) = rel W m (m - 1) 1 0 := by
  rw [atomRel_two_mul]
  norm_num

/-- The odd base case, as a relator. All four indices are odd, so `atom_odd` reduces every atom
and no reasoning about truncated division survives. The source proves the corresponding
equivalence under `set_option allowUnsafeReducibility true` together with
`attribute [local reducible] Nat.rawCast`; putting the indices in `2 * _ + 1` form removes the
need for either. -/
private theorem atomRel_odd_eq_rel (m : ℤ) :
    atomRel W (2 * m + 1) (2 * (m - 1) + 1) (2 * 1 + 1) (2 * 0 + 1)
      = rel W (m + 1) (m - 1) 1 0 := by
  simp_rw [atomRel, atom_odd, rel]
  ring_nf

/-- **The descent.** The two doubling recurrences, holding from `m = 2` and `m = 3` on, force the
full four-index relation at every valid quadruple. The induction is on the largest index: below
`6` no valid quadruple exists, and above it `atomRelVanishes_of_min` reduces to the minimal
pair, where either the gap `b + 2 < a` admits the transfer down to a smaller first index, or
`b + 2 = a` lands on one of the two recurrences according to parity. -/
theorem atomRelVanishes_of_rel (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m : ℤ, 2 ≤ m → rel W (m + 1) m 1 0 = 0)
    (evenRec : ∀ m : ℤ, 3 ≤ m → rel W (m + 1) (m - 1) 1 0 = 0) :
    ∀ a b c d : ℤ, AtomRelVanishes W a b c d := by
  intro a
  induction a using Int.strongRec (m := 6)
  next a ha =>
    intro b c d same anti
    exact absurd ha (not_lt.mpr (six_le_of_parity_of_nonnegStrictAnti₄ same anti))
  next a h6 ih =>
    intro b c d
    refine atomRelVanishes_of_min one two ?_ b c d
    intro a' b' haa
    rcases haa.lt_or_eq with hlt | rfl
    · exact ih a' hlt b' _ _
    intro same anti
    obtain ⟨h0, h1, h2, h3⟩ := (nonnegStrictAnti₄_iff _ _ _ _).mp anti
    have hpb := same.2.1
    rcases (show b' + 2 < a' ∨ b' + 2 = a' by omega) with hb | hb
    · rw [← atomRel_avg_sub W same, ← atomRel_abs₄]
      exact ih _ (by omega) _ _ _ (parity_abs_avg_sub same)
        (nonnegStrictAnti₄_abs_avg_sub h1 (by omega) h2 h3)
    · rcases Int.emod_two_eq_zero_or_one a' with hp | hp
      · obtain ⟨k, rfl⟩ : ∃ k, a' = 2 * k := ⟨a' / 2, by omega⟩
        have hodd := oddRec (k - 1) (by omega)
        rw [sub_add_cancel] at hodd
        rw [show (2 * k % 2 : ℤ) = 2 * 0 by omega, show (2 : ℤ) * 0 + 2 = 2 * 1 by norm_num,
          show b' = 2 * (k - 1) by omega, atomRel_even_eq_rel]
        exact hodd
      · obtain ⟨k, rfl⟩ : ∃ k, a' = 2 * k + 1 := ⟨a' / 2, by omega⟩
        rw [show ((2 * k + 1) % 2 : ℤ) = 2 * 0 + 1 by omega,
          show (2 : ℤ) * 0 + 1 + 2 = 2 * 1 + 1 by norm_num,
          show b' = 2 * (k - 1) + 1 by omega, atomRel_odd_eq_rel]
        exact evenRec k (by omega)

end IsEllipticNet
