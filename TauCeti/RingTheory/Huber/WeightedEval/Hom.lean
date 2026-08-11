/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Mul

/-!
# The evaluation of `A⟨X⟩_T` as a ring homomorphism

The additive and multiplicative laws of Wedhorn's evaluation are proved in
`WeightedEval/Map.lean` and `WeightedEval/Mul.lean` as statements about individual
`T`-restricted series. On `A⟨X⟩_T` itself — where restrictedness is carried by membership rather
than by a hypothesis — they assemble into a ring homomorphism, which is the shape Proposition 5.50
needs.

Its continuity, and the uniqueness that makes 5.50 a *universal* property, are still not proved
here.

## Main definitions

* `TauCeti.Huber.weightedEvalHom`: evaluation as a ring homomorphism `A⟨X⟩_T →+* B`.

## Main results

* `TauCeti.Huber.coe_weightedEvalHom`: it is `TauCeti.Huber.weightedEval` on the underlying
  series, which is how every computation about it is done.
* `TauCeti.Huber.weightedEvalHom_weightedC` and `TauCeti.Huber.weightedEvalHom_weightedX`: it
  restricts to `φ` on constants and sends the `i`-th variable to `bᵢ`. Together with the ring-hom
  structure these are the properties 5.50 asks of it.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B]
  [T3Space B] [T2Space B] {φ : A →+* B} {T : Fin k → Set A} {b : Fin k → B}

/-- **Wedhorn's evaluation as a ring homomorphism** out of `A⟨X⟩_T`.

Every field is one of the laws already proved: `weightedEval_C` at `1`, `weightedEval_zero`,
`weightedEval_add` and `weightedEval_mul`. The restrictedness each of those needs is exactly what
membership in `TauCeti.Huber.weightedRestrictedSubring` supplies, which is why the map is a
homomorphism on `A⟨X⟩_T` and only a collection of identities off it. -/
noncomputable def weightedEvalHom (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) : weightedRestrictedSubring T hT →+* B where
  toFun f := weightedEval φ b (f : MvPowerSeries (Fin k) A)
  map_one' := by
    rw [OneMemClass.coe_one, ← MvPowerSeries.monomial_zero_one, weightedEval_monomial]
    simp
  map_mul' f g := weightedEval_mul hφ hb (mem_weightedRestrictedSubring.mp f.property)
    (mem_weightedRestrictedSubring.mp g.property)
  map_zero' := weightedEval_zero φ b
  map_add' f g := weightedEval_add hφ hb (mem_weightedRestrictedSubring.mp f.property)
    (mem_weightedRestrictedSubring.mp g.property)

/-- The homomorphism is `TauCeti.Huber.weightedEval` on the underlying series. The body is not
exported, so this is how a consumer computes with it. -/
@[simp]
theorem coe_weightedEvalHom (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) (f : weightedRestrictedSubring T hT) :
    weightedEvalHom hT hφ hb f = weightedEval φ b (f : MvPowerSeries (Fin k) A) := (rfl)

/-- **The homomorphism restricts to `φ` on constants.** With `weightedEvalHom_weightedX` this is
what makes it *the* evaluation at `b` extending `φ`, which is the property Proposition 5.50 asks
of it.

Not `@[simp]`: `coe_weightedEvalHom`, `coe_weightedC` and `weightedEval_C` are already simp, so
simp closes the goal without it. It is named because it is the property 5.50 asks for, not because
automation needs it. -/
theorem weightedEvalHom_weightedC (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) (a : A) :
    weightedEvalHom hT hφ hb (weightedC T hT a) = φ a := by
  rw [coe_weightedEvalHom, coe_weightedC, weightedEval_C]

/-- **The homomorphism sends the `i`-th variable to `bᵢ`.** Not `@[simp]`, for the same reason as
`TauCeti.Huber.weightedEvalHom_weightedC`. -/
theorem weightedEvalHom_weightedX (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) (i : Fin k) :
    weightedEvalHom hT hφ hb (weightedX T hT i) = b i := by
  rw [coe_weightedEvalHom, coe_weightedX, weightedEval_X]

end TauCeti.Huber

end
