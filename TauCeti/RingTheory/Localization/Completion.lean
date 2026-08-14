/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Maps out of the completion of a localisation

A continuous ring homomorphism out of the completion of a localisation `S` of `A` is determined by
its restriction to `A`. Both steps from `A` to `Ŝ` are epimorphic in the relevant sense: agreeing
after `algebraMap A S` forces agreement on `S` by `IsLocalization.ringHom_ext`, and agreeing on `S`
forces agreement on `Ŝ` because `S` is dense in it.

Only continuity is required of the two maps, and the target need only be a semiring carrying a
Hausdorff topology — no compatibility between the topology and the ring operations is used, and
nothing is asked of the submonoid.

## Main results

* `TauCeti.hom_ext_completion_of_isLocalization`: two continuous ring homomorphisms out of `Ŝ`
  agreeing on `A` are equal.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §8, where this is the reason a map out of `A⟨T/s⟩` is
  pinned down by its restriction to `A`.
-/

public section

namespace TauCeti

open UniformSpace

/-- **Maps out of the completion of a localisation are determined on the base ring.** Two
continuous ring homomorphisms `Ŝ → B` into a Hausdorff topological semiring that agree after
composing with `A → S → Ŝ` are equal. -/
theorem hom_ext_completion_of_isLocalization {A S : Type*} [CommSemiring A] [CommRing S]
    [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
    {B : Type*} [Semiring B] [TopologicalSpace B] [T2Space B]
    (g h : Completion S →+* B) (hg : Continuous g) (hh : Continuous h)
    (hcomp : (g.comp Completion.coeRingHom).comp (algebraMap A S)
      = (h.comp Completion.coeRingHom).comp (algebraMap A S)) : g = h :=
  DFunLike.ext' (Completion.ext hg hh fun a ↦
    congrArg (fun k : S →+* B ↦ k a) (IsLocalization.ringHom_ext M hcomp))

end TauCeti
