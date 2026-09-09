/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AugmentationPoint.Basic
public import TauCeti.RingTheory.Idempotents.Connected.Component

/-!
# The connected component defined by an augmentation

An algebra homomorphism from a commutative algebra to its ground field determines a rational point
of the algebra's prime spectrum. This file records that the component idempotent maps to one and
the factorization of the augmentation through the quotient cutting out that point's connected
component when the prime spectrum is locally connected.

## Main declarations

* `AlgHom.map_connectedComponentIdempotent_kernelPoint_eq_one`: the augmentation maps the
  component idempotent of its kernel point to one.
* `AlgHom.kernelPointConnectedComponentAlgHom`: the augmentation factored through the
  quotient cutting out the connected component of its kernel point.
* `AlgHom.kernelPoint_comp_connectedComponentQuotient_mem`: a point of the component
  quotient maps into the selected connected component.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 2.a.
* The Stacks Project, Tags 00EE and 022R.

The connected-component factorization supplies a prerequisite for Layer 3, "Identity component
`G°` and component group `π₀(G)`", of the ReductiveGroups roadmap. It concerns only the ordinary
connected component over the ground field and asserts no compatibility with base change.
-/

public section

open AlgebraicGeometry

section

universe u v

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [Algebra k H]
variable (f : H →ₐ[k] k)

variable [LocallyConnectedSpace (PrimeSpectrum H)]

/-- An augmentation takes the idempotent selecting the connected component of its kernel point to
one. -/
@[simp]
theorem _root_.AlgHom.map_connectedComponentIdempotent_kernelPoint_eq_one :
    f (PrimeSpectrum.connectedComponentIdempotent (AlgHom.kernelPoint f)) = 1 := by
  have hnot : PrimeSpectrum.connectedComponentIdempotent (AlgHom.kernelPoint f) ∉
      (AlgHom.kernelPoint f).asIdeal :=
    PrimeSpectrum.connectedComponentIdempotent_notMem_asIdeal (AlgHom.kernelPoint f)
  rw [AlgHom.kernelPoint_asIdeal, RingHom.mem_ker] at hnot
  have hidempotent : IsIdempotentElem
      (f (PrimeSpectrum.connectedComponentIdempotent (AlgHom.kernelPoint f))) :=
    (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent (AlgHom.kernelPoint f)).map
      f.toRingHom
  exact (IsIdempotentElem.iff_eq_zero_or_one.mp hidempotent).resolve_left hnot

/-- The ideal cutting out the connected component of an augmentation's kernel point is contained
in the kernel of the augmentation. -/
theorem _root_.AlgHom.connectedComponentIdeal_kernelPoint_le_ker :
    PrimeSpectrum.connectedComponentIdeal (AlgHom.kernelPoint f) ≤
      RingHom.ker (f : H →+* k) := by
  simpa only [AlgHom.kernelPoint_asIdeal] using
    PrimeSpectrum.connectedComponentIdeal_le_asIdeal (AlgHom.kernelPoint f)

/-- The augmentation factored through the quotient cutting out the connected component of its
kernel point. -/
noncomputable def _root_.AlgHom.kernelPointConnectedComponentAlgHom :
    (H ⧸ PrimeSpectrum.connectedComponentIdeal (AlgHom.kernelPoint f)) →ₐ[k] k :=
  Ideal.Quotient.liftₐ (PrimeSpectrum.connectedComponentIdeal (AlgHom.kernelPoint f)) f
    (AlgHom.connectedComponentIdeal_kernelPoint_le_ker f)

/-- The factored augmentation composed with the quotient map is the original augmentation. -/
@[simp]
theorem _root_.AlgHom.kernelPointConnectedComponentAlgHom_comp_mk :
    (AlgHom.kernelPointConnectedComponentAlgHom f).comp
      (Ideal.Quotient.mkₐ k (PrimeSpectrum.connectedComponentIdeal (AlgHom.kernelPoint f))) = f :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The factored augmentation evaluates a quotient constructor as the original augmentation. -/
@[simp]
theorem _root_.AlgHom.kernelPointConnectedComponentAlgHom_mk (h : H) :
    AlgHom.kernelPointConnectedComponentAlgHom f
        (Ideal.Quotient.mk (PrimeSpectrum.connectedComponentIdeal (AlgHom.kernelPoint f)) h) = f h
          :=
  DFunLike.congr_fun (AlgHom.kernelPointConnectedComponentAlgHom_comp_mk f) h

/-- A rational point of the quotient cutting out a connected component maps into that component
under the quotient map. -/
theorem _root_.AlgHom.kernelPoint_comp_connectedComponentQuotient_mem (z : PrimeSpectrum H)
    (g : (H ⧸ PrimeSpectrum.connectedComponentIdeal z) →ₐ[k] k) :
    AlgHom.kernelPoint
        (g.comp (Ideal.Quotient.mkₐ k (PrimeSpectrum.connectedComponentIdeal z))) ∈
      connectedComponent z := by
  let y : PrimeSpectrum (H ⧸ PrimeSpectrum.connectedComponentIdeal z) := AlgHom.kernelPoint g
  have hy := (PrimeSpectrum.primeSpectrumQuotientHomeomorphConnectedComponent z y).property
  rw [PrimeSpectrum.primeSpectrumQuotientHomeomorphConnectedComponent_apply_coe] at hy
  dsimp only [y] at hy
  have hcomap :
      PrimeSpectrum.comap
          (Ideal.Quotient.mk (PrimeSpectrum.connectedComponentIdeal z))
          (AlgHom.kernelPoint g) =
        AlgHom.kernelPoint
          (g.comp (Ideal.Quotient.mkₐ k (PrimeSpectrum.connectedComponentIdeal z))) :=
    AlgHom.comap_kernelPoint g
      (Ideal.Quotient.mkₐ k (PrimeSpectrum.connectedComponentIdeal z))
  rw [hcomap] at hy
  exact hy

end
