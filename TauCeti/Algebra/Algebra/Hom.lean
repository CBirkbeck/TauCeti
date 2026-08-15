/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Hom

/-!
# The algebra structure an algebra homomorphism induces

An `f : A →ₐ[R] B` induces an `A`-algebra structure on `B` through
`f.toRingHom.toAlgebra`, and the structure map of that algebra is `f` itself.

Mathlib has this for a bare ring homomorphism, as `RingHom.algebraMap_toAlgebra`, but only as an
equality of ring homomorphisms. This file states the pointwise `AlgHom` form, which is what a
consumer discharging an `∀ x, algebraMap A B x = f x` hypothesis actually needs.

## Main results

* `AlgHom.algebraMap_toAlgebra_apply`: the structure map of `f.toRingHom.toAlgebra` is `f`.
-/

public section

/-- **The structure map of the algebra an `AlgHom` induces is that `AlgHom`.**

The fact is definitional, so `rfl` proves it; naming it keeps consumers from repeating a
`rfl` whose correctness depends on how `RingHom.toAlgebra` is implemented, and gives the
`∀ x, algebraMap A B x = f x` hypotheses of the `Isogeny` degree API a witness to apply. -/
theorem AlgHom.algebraMap_toAlgebra_apply {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (x : A) :
    @algebraMap A B _ _ f.toRingHom.toAlgebra x = f x := by
  rw [RingHom.algebraMap_toAlgebra]
  exact congrFun (AlgHom.coe_toRingHom f) x
