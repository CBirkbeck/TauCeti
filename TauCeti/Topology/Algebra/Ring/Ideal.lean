/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The quotient of a topological ring by an ideal

Two things about `R ⧸ I` that its algebraic theory does not record. It is `T1` exactly when `I` is
closed, and hence `T0`; and when `f : R →+* S` presents `S` as a topological quotient of `R`, the
first isomorphism theorem `R ⧸ ker f ≃+* S` is a homeomorphism, so `S` carries the quotient
topology and not merely a coarser one.

Mathlib proves the corresponding statement for the quotient of a topological group by a
subgroup, as `QuotientGroup.t1Space_iff` and `QuotientGroup.instT1Space`. Those are stated for
`G ⧸ N` with `N : AddSubgroup G` in the additive case, whereas `R ⧸ I` is the quotient by an
`Ideal`. The two quotients are definitionally equal — Mathlib's own
`Ideal.topologicalRing_quotient` builds the additive structure of `R ⧸ I` out of
`QuotientAddGroup.instIsTopologicalAddGroup` — but reaching the group statement from an ideal
still means presenting `I` as `I.toAddSubgroup` and transporting the closedness hypothesis along
that presentation, which unification does not do on its own: with only `IsClosed (I : Set R)` in
context, `T1Space (R ⧸ I)` is not synthesized. So the results below are that transport, and
their proofs delegate to Mathlib rather than reproving anything.

Only separate continuity of addition is needed for the separation results, matching the hypotheses
of the group statements they delegate to; no ring topology and no multiplicative continuity is
used. The first isomorphism theorem below asks for even less: only that `R ⧸ ker f` carries the
coinduced topology, which it does by construction.

## The topological first isomorphism theorem

Algebraically, `RingHom.quotientKerEquivOfSurjective` identifies `R ⧸ ker f` with `S` for any
surjective `f`. Topologically that says nothing: `R ⧸ ker f` carries the quotient topology, and a
continuous surjection can land on a strictly coarser topology than the quotient one, so the
bijection is continuous but need not be open. What closes the gap is exactly the hypothesis that
`f` is a *quotient map*, and with it the algebraic isomorphism becomes a homeomorphism.

The quotient-map hypothesis is where the analysis lives. Over a Tate ring it is
`TauCeti.Huber.IsTateRing.isQuotientMap`, an open mapping theorem, and supplying it is real work;
everything downstream of it is the formal argument below, which uses nothing but injectivity of
`RingHom.kerLift` and the universal property of the quotient topology.

Note that closedness of `ker f` comes for free once `S` is `T1`, since a kernel is the preimage of
a point; it is not a further hypothesis of the theorem but a consequence for its consumers, and
`Ideal.Quotient.instT1Space` above then hands back the separation of `R ⧸ ker f`.

## Main results

* `Ideal.Quotient.t1Space_iff`: `T1Space (R ⧸ I) ↔ IsClosed (I : Set R)`.
* `Ideal.Quotient.instT1Space`: the instance form, so that `T0Space (R ⧸ I)` is found
  automatically once `I` is known to be closed.
* `Ideal.Quotient.continuous_lift`: a continuous ring homomorphism annihilating `I` induces a
  *continuous* homomorphism on `R ⧸ I`, with no hypothesis on `I`.
* `RingHom.isOpenMap_kerLift`: the map `R ⧸ ker f →+* S` induced by `f` is open when `f` is a
  quotient map.
* `RingHom.isHomeomorph_kerLift`: it is a homeomorphism. `IsHomeomorph.homeomorph` bundles that as
  `R ⧸ ker f ≃ₜ S`, and the map bundled is the ring homomorphism `RingHom.kerLift`, so the ring
  structure comes along with it and needs no transport of its own.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Example 6.38, where a rational localisation is
  presented as a quotient `C ⧸ 𝔞` and its Hausdorff completion is taken.
-/

public section

variable {R : Type*} [TopologicalSpace R] [CommRing R] [SeparatelyContinuousAdd R] (I : Ideal R)

namespace Ideal.Quotient

/-- The quotient of a topological ring by an ideal is `T1` exactly when the ideal is closed.
This is `QuotientAddGroup.t1Space_iff` read through the identification of `R ⧸ I` with the
quotient of `R` by `I.toAddSubgroup`. -/
theorem t1Space_iff : T1Space (R ⧸ I) ↔ IsClosed (I : Set R) :=
  QuotientAddGroup.t1Space_iff (N := I.toAddSubgroup)

/-- The quotient of a topological ring by a closed ideal is `T1`, hence `T0`. Stated as an
instance, with the closedness of `I` as an instance argument, so that the separation of `R ⧸ I`
is available to instance search wherever `I` is known to be closed; this follows
`Ideal.Quotient.normedCommRing`, which takes `IsClosed (I : Set R)` the same way. -/
instance instT1Space [IsClosed (I : Set R)] : T1Space (R ⧸ I) := (t1Space_iff I).mpr ‹_›

omit [SeparatelyContinuousAdd R] in
/-- **A continuous ring homomorphism that kills `I` lifts to a continuous map on `R ⧸ I`.**

No hypothesis on `I` is needed: closedness of `I` is what makes `R ⧸ I` separated
(`Ideal.Quotient.instT1Space` above), which matters for maps *into* `R ⧸ I`, not for maps out
of it. -/
theorem continuous_lift {S : Type*} [Semiring S] [TopologicalSpace S] {f : R →+* S}
    (hf : Continuous f) (hI : ∀ a ∈ I, f a = 0) :
    Continuous (Ideal.Quotient.lift I f hI) :=
  -- `R ⧸ I` carries the coinduced topology, so continuity of a map out of it is continuity of its
  -- composite with the quotient map, which is `f`.
  continuous_coinduced_dom.mpr hf

end Ideal.Quotient

section FirstIsomorphism

open Topology

variable {R S : Type*} [TopologicalSpace R] [CommRing R] [TopologicalSpace S] [Semiring S]
  {f : R →+* S}

namespace RingHom

/-- **The lift of a quotient map to `R ⧸ ker f` is open.**

Surjectivity of `f` is not enough on its own: it makes the lift a continuous bijection, and a
continuous bijection is open only when the topology it lands in is no coarser than the one it
carries. That `f` is a quotient map is exactly the statement that it is not coarser. -/
theorem isOpenMap_kerLift (hq : IsQuotientMap (f : R → S)) : IsOpenMap (kerLift f) := by
  intro U hU
  -- `f` coinduces the topology of `S`, so it is enough to open the preimage; and that preimage is
  -- `mk (ker f) ⁻¹' U`, because `RingHom.kerLift` is injective
  rw [← hq.isCoinducing.isOpen_preimage]
  have himg : ⇑f ⁻¹' (kerLift f '' U) = ⇑(Ideal.Quotient.mk (ker f)) ⁻¹' U := by
    ext x
    refine ⟨?_, fun hx ↦ ⟨_, hx, kerLift_mk f x⟩⟩
    rintro ⟨u, hu, hux⟩
    have hu' : u = Ideal.Quotient.mk (ker f) x :=
      kerLift_injective f (hux.trans (kerLift_mk f x).symm)
    exact Set.mem_preimage.mpr (hu' ▸ hu)
  rw [himg]
  exact hU.preimage continuous_coinduced_rng

/-- **The topological first isomorphism theorem for rings.** A ring homomorphism that is a
quotient map presents its target as the quotient of its source by its kernel, topologically as
well as algebraically.

`IsHomeomorph.homeomorph` turns this into `R ⧸ ker f ≃ₜ S`. What it bundles is `RingHom.kerLift`,
which is a ring homomorphism, so a consumer needing the isomorphism of rings has it already —
`RingHom.quotientKerEquivOfSurjective` is that same map. -/
theorem isHomeomorph_kerLift (hq : IsQuotientMap (f : R → S)) : IsHomeomorph (kerLift f) where
  continuous := Ideal.Quotient.continuous_lift (ker f) hq.continuous fun _ ↦ mem_ker.mp
  isOpenMap := isOpenMap_kerLift hq
  bijective := ⟨kerLift_injective f, fun y ↦
    let ⟨x, hx⟩ := hq.surjective y
    ⟨Ideal.Quotient.mk (ker f) x, (kerLift_mk f x).trans hx⟩⟩

end RingHom

end FirstIsomorphism
