/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Tactic.Ring

/-!
# Localising a ring at `1 + I`

For an ideal `I` of a commutative ring `B`, the set `1 + I` is a submonoid. If `I` is finitely
generated and its image in a localisation at `1 + I` lies in every prime there, then a single
element of `1 + I` annihilates a power of `I`.

Only that implication is proved here, and only under `I.FG`; the converse is not stated.

## Main results

* `Ideal.oneAdd`: `1 + I` as a submonoid of `B`.
* `Ideal.exists_pow_map_eq_bot`: if `I` is finitely generated and its image lies in every
  prime of the localisation, some power of that image is zero.
* `Ideal.exists_mem_oneAdd_forall_mul_eq_zero`: the same hypothesis produces a single
  `s ∈ 1 + I` with `s * x = 0` for every `x ∈ I ^ n`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 7.49(2). The construction here
  follows the argument of that proposition's proof, which localises at `1 + I` in exactly this
  way; the statements below are stated for their own sake and do not mention `Spa`.
-/

public section

namespace Ideal

open scoped Pointwise

variable {B : Type*} [CommRing B] (I : Ideal B)

/-- **`1 + I` is a submonoid.** Closure is the identity
`(1 + a)(1 + b) = 1 + (ab + a + b)`, written here on representatives as
`ab - 1 = (a - 1)(b - 1) + (a - 1) + (b - 1)`. -/
def oneAdd : Submonoid B where
  carrier := {x | x - 1 ∈ I}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    have hexp : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring
    rw [hexp]
    exact I.add_mem (I.add_mem (I.mul_mem_left _ hb) ha) hb

@[simp] lemma mem_oneAdd {x : B} : x ∈ oneAdd I ↔ x - 1 ∈ I := Iff.rfl

variable {I} {C : Type*} [CommRing C] [Algebra B C]

/-- **A power of the image of `I` vanishes.** If every prime of `C` contains the image of `I`,
that image lies in the nilradical; being finitely generated it is then nilpotent.

Nothing here needs `C` to be a localisation — only a `B`-algebra in which the image of `I` is
contained in every prime. It is used below at `C = (1 + I)⁻¹ B`, which is the case arising in the
proof of Wedhorn's Proposition 7.49(2). -/
theorem exists_pow_map_eq_bot (hfg : I.FG)
    (hprime : ∀ P : Ideal C, P.IsPrime → I.map (algebraMap B C) ≤ P) :
    ∃ n : ℕ, (I.map (algebraMap B C)) ^ n = ⊥ := by
  have hle : I.map (algebraMap B C) ≤ (⊥ : Ideal C).radical := by
    intro x hx
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨-, hP⟩
    exact hprime P hP hx
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (hfg.map _)
  exact ⟨n, le_bot_iff.mp hn⟩

section Localisation

variable [IsLocalization (oneAdd I) C]

/-- **A single element of `1 + I` annihilates a power of `I`.** Let `I` be a finitely generated
ideal of `B` whose image in a localisation `C` at `1 + I` is contained in every prime of `C`.
Then there are `n : ℕ` and `s ∈ 1 + I` with `s * x = 0` for every `x ∈ I ^ n` — one `s` serving
the whole of `I ^ n`, not one per element. -/
theorem exists_mem_oneAdd_forall_mul_eq_zero (hfg : I.FG)
    (hprime : ∀ P : Ideal C, P.IsPrime → I.map (algebraMap B C) ≤ P) :
    ∃ (n : ℕ) (s : B), s ∈ oneAdd I ∧ ∀ x ∈ I ^ n, s * x = 0 := by
  classical
  obtain ⟨n, hn⟩ := exists_pow_map_eq_bot (C := C) hfg hprime
  -- every element of `I ^ n` maps to zero
  have hzero : ∀ x ∈ I ^ n, algebraMap B C x = 0 := by
    intro x hx
    have : algebraMap B C x ∈ (I ^ n).map (algebraMap B C) :=
      Ideal.mem_map_of_mem _ hx
    rwa [Ideal.map_pow, hn, Ideal.mem_bot] at this
  -- a finite generating set for `I ^ n`
  obtain ⟨T, hT⟩ := (hfg.pow : (I ^ n).FG)
  -- an annihilator in `1 + I` for each generator
  have hgen : ∀ t ∈ T, ∃ m : oneAdd I, (m : B) * t = 0 := by
    intro t ht
    exact (IsLocalization.map_eq_zero_iff (oneAdd I) C t).mp
      (hzero t (hT ▸ Ideal.subset_span ht))
  choose m hm using hgen
  refine ⟨n, ∏ t ∈ T.attach, (m t.1 t.2 : B), ?_, ?_⟩
  · exact Submonoid.prod_mem _ fun t _ ↦ (m t.1 t.2).2
  · rw [← hT]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨t, rfl⟩ : ∃ t : T, (t : B) = y := ⟨⟨y, hy⟩, rfl⟩
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_attach T t), mul_assoc, hm t.1 t.2, mul_zero]
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_eq_mul, mul_comm c y, ← mul_assoc, hy, zero_mul]

end Localisation

end Ideal
