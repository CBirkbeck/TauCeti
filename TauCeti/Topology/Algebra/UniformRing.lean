/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The kernel of the completion map of a uniform ring

The kernel of `A → Â` is the closure of the zero ideal. This extends Mathlib's
`Mathlib/Topology/Algebra/UniformRing.lean`, where `coeRingHom` is defined, and needs no
nonarchimedean hypothesis.

## Main results

* `UniformSpace.Completion.ker_coeRingHom`: the kernel of `A → Â` is the closure of `⊥`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Example 5.33: the completion map has kernel
  `closure {0}`.
* The proof is an inseparability argument, via `Topology.IsInducing.inseparable_iff` and
  `addGroup_inseparable_iff`.
-/

public section

open UniformSpace

namespace UniformSpace.Completion

variable {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]

/-- The kernel of the completion map `A → Â` is the closure of the zero ideal. -/
theorem ker_coeRingHom :
    RingHom.ker (Completion.coeRingHom : A →+* Completion A) = (⊥ : Ideal A).closure := by
  ext x
  rw [RingHom.mem_ker, ← SetLike.mem_coe, Ideal.coe_closure]
  calc (Completion.coeRingHom x = 0)
      ↔ ((x : Completion A) = ((0 : A) : Completion A)) := by rw [Completion.coe_zero]; rfl
    _ ↔ Inseparable ((x : Completion A)) (((0 : A) : Completion A)) := inseparable_iff_eq.symm
    _ ↔ Inseparable x (0 : A) := Completion.isDenseInducing_coe.isInducing.inseparable_iff
    _ ↔ x - 0 ∈ closure ({0} : Set A) := addGroup_inseparable_iff
    _ ↔ x ∈ closure ((⊥ : Ideal A) : Set A) := by rw [sub_zero]; simp


end UniformSpace.Completion
