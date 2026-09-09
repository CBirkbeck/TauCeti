/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Huber.PowerBounded

/-!
# Rescaling a denominator to be topologically nilpotent

Over a Tate ring every element becomes topologically nilpotent after multiplication by a high
enough power of a pseudouniformiser:

* `TauCeti.Huber.IsTateRing.exists_isTopologicallyNilpotent_pow_mul`.

The point is that the multiplier is a **unit**, so `s` and the rescaled `ϖ ^ i * s` are
associated. A construction indexed by a denominator — a rational localisation `A⟨T/s⟩`, say —
therefore does not change when the denominator is rescaled, while hypotheses asking topological
nilpotence of the denominator become available. `IsLocalization.Away.of_associated` is the
transport on the localisation itself.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §6.
-/

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **A pseudouniformiser rescales any element to a topologically nilpotent one.** For `s : A`
in a Tate ring there are a pseudouniformiser `ϖ` and an exponent `i` with `ϖ ^ i * s`
topologically nilpotent.

`ϖ ^ i` is a unit, so `s` and `ϖ ^ i * s` are associated: anything indexed by `s` up to
associates is unchanged by the rescaling. -/
theorem IsTateRing.exists_isTopologicallyNilpotent_pow_mul
    (P : PairOfDefinition A) [IsTateRing A] (s : A) :
    ∃ (ϖ : A) (i : ℕ), IsPseudoUniformizer ϖ ∧ IsTopologicallyNilpotent (ϖ ^ i * s) := by
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  obtain ⟨-, hnil⟩ := isPseudoUniformizer_iff.mp hϖ
  obtain ⟨i, hi⟩ := P.exists_pow_mul_mem hnil s
  refine ⟨ϖ, i + 1, hϖ, ?_⟩
  have hpb : IsPowerBounded (ϖ ^ i * s) :=
    mem_powerBoundedSubring.mp (P.le_powerBoundedSubring hi)
  have h := hpb.isTopologicallyNilpotent_mul_of_commute (Commute.all _ _) hnil
  rw [show ϖ ^ (i + 1) * s = ϖ ^ i * s * ϖ by ring]
  exact h

end TauCeti.Huber

end
