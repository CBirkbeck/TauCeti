/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries

/-!
# A continuous homomorphism out of `A⟨X⟩_T` is determined by its generators

Proposition 5.50 asserts not just that the evaluation at `b` exists but that it is the *only*
continuous extension of `φ` sending `Xᵢ` to `bᵢ`. That uniqueness is what this file proves, and it
is a statement about arbitrary continuous ring homomorphisms out of `A⟨X⟩_T` rather than about the
evaluation: nothing here mentions summability, boundedness or `weightedEval`.

The reason it holds is that the polynomials are dense (`TauCeti.Huber.dense_weightedPolynomials`,
Wedhorn 5.49). Two ring homomorphisms agreeing on the constants and the variables agree on every
polynomial, by `MvPolynomial.ringHom_ext`; if they are also continuous and the target is Hausdorff,
agreeing on a dense subring forces them to agree everywhere.

## Main results

* `TauCeti.Huber.eqOn_weightedPolynomials`: two ring homomorphisms agreeing on the generators
  agree on the polynomial subring.
* `TauCeti.Huber.ringHom_ext_of_continuous`: two *continuous* such homomorphisms are equal.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Propositions 5.49 and 5.50.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [TopologicalSpace B] {T : Fin k → Set A} {hT : IsWeightFamily T}

omit [TopologicalSpace B] in
/-- **Agreement on the generators propagates to the polynomials.** Two ring homomorphisms out of
`A⟨X⟩_T` that agree on every constant series and every variable agree on the whole polynomial
subring. No topology is involved. -/
theorem eqOn_weightedPolynomials {f g : weightedRestrictedSubring T hT →+* B}
    (hC : ∀ a, f (weightedC T hT a) = g (weightedC T hT a))
    (hX : ∀ i, f (weightedX T hT i) = g (weightedX T hT i)) :
    Set.EqOn f g (weightedPolynomials T hT : Set (weightedRestrictedSubring T hT)) := by
  have hcomp : f.comp (weightedPolynomialHom T hT) = g.comp (weightedPolynomialHom T hT) :=
    MvPolynomial.ringHom_ext (by simpa using hC) (by simpa using hX)
  intro x hx
  obtain ⟨p, rfl⟩ := mem_weightedPolynomials_iff_exists.mp hx
  exact congrArg (fun h : MvPolynomial (Fin k) A →+* B ↦ h p) hcomp

/-- **A continuous homomorphism out of `A⟨X⟩_T` is determined by its values on the generators.**
This is the uniqueness half of Proposition 5.50: an extension of `φ` sending each `Xᵢ` to `bᵢ` is
unique among *continuous* homomorphisms.

Continuity is essential — the polynomials are only dense, not everything — and so is the target
being Hausdorff. -/
theorem ringHom_ext_of_continuous [T2Space B] {f g : weightedRestrictedSubring T hT →+* B}
    (hf : Continuous f) (hg : Continuous g)
    (hC : ∀ a, f (weightedC T hT a) = g (weightedC T hT a))
    (hX : ∀ i, f (weightedX T hT i) = g (weightedX T hT i)) : f = g :=
  RingHom.coe_inj (hf.ext_on (dense_weightedPolynomials hT) hg (eqOn_weightedPolynomials hC hX))

end TauCeti.Huber

end
