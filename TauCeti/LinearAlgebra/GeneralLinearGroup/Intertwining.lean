/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Intertwiners of linear automorphisms

A linear map `f : V →ₗ[K] W` **intertwines** automorphisms `a` of `V` and `b` of `W` when
`f ∘ a = b ∘ f`. This is the heterogeneous form of `SemiconjBy`: source and target live in
different modules, so the relation is not a statement inside one monoid and Mathlib's
`SemiconjBy` API does not apply to it.

## Main declarations

* `TauCeti.GeneralLinearGroup.comp_inv_eq_of_comp_eq`: an intertwiner of two automorphisms also
  intertwines their inverses.
-/

public section

namespace TauCeti

open LinearMap

namespace GeneralLinearGroup

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}
variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

/-- **Intertwining passes to inverses.** If `f` intertwines the automorphisms `a` and `b`, then it
intertwines `a⁻¹` and `b⁻¹`. -/
theorem comp_inv_eq_of_comp_eq (f : V →ₗ[K] W) (a : GeneralLinearGroup K V)
    (b : GeneralLinearGroup K W)
    (hab : f.comp (a : Module.End K V) = (b : Module.End K W).comp f) :
    f.comp (↑a⁻¹ : Module.End K V) = (↑b⁻¹ : Module.End K W).comp f := by
  -- `↑a⁻¹` is the inverse equivalence's map, so the transposition lemma for equivalences applies
  change f.comp a.toLinearEquiv.symm.toLinearMap = _
  rw [LinearEquiv.comp_toLinearMap_symm_eq, LinearMap.comp_assoc]
  change _ = (↑b⁻¹ : Module.End K W).comp (f.comp (a : Module.End K V))
  rw [hab, ← LinearMap.comp_assoc]
  ext x
  exact (b.toLinearEquiv.symm_apply_apply _).symm

end GeneralLinearGroup

end TauCeti
