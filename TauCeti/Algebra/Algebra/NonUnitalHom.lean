/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.GroupWithZero.Idempotent

/-!
# Unitality of a non-unital algebra homomorphism

A non-unital algebra homomorphism need not send `1` to `1`, and the zero map shows it need not.
Into a domain there is nothing in between: `p 1` is idempotent, so it is `0` or `1`, and `p 1 = 0`
forces `p` itself to vanish. A non-unital algebra map into a domain is therefore either the zero
map or an ordinary algebra map, with the zero map the only non-unital one.

This is the dichotomy that lets a type of multiplicative maps carry a zero without adjoining one.

## Main results

* `NonUnitalAlgHom.toAlgHomOfMapOne`: a non-unital algebra map sending `1` to `1`, as an `AlgHom`.
* `NonUnitalAlgHom.eq_zero_or_map_one`: into a domain, a non-unital algebra map is the zero map
  or sends `1` to `1`.
-/

public section

namespace NonUnitalAlgHom

variable {F A B : Type*} [CommSemiring F] [Semiring A] [Semiring B] [Algebra F A] [Algebra F B]

/-- **A non-unital algebra map that preserves `1` is an algebra map.** -/
-- `@[expose]`: the two lemmas below say the underlying function is unchanged, which is the
-- whole content of this construction, and both are `rfl` only if the body is visible to them.
@[expose]
def toAlgHomOfMapOne (p : A →ₙₐ[F] B) (h : p 1 = 1) : A →ₐ[F] B where
  toFun := p
  map_one' := h
  map_mul' := map_mul p
  map_zero' := map_zero p
  map_add' := map_add p
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, h]

@[simp]
theorem coe_toAlgHomOfMapOne (p : A →ₙₐ[F] B) (h : p 1 = 1) :
    ⇑(p.toAlgHomOfMapOne h) = ⇑p :=
  rfl

@[simp]
theorem toAlgHomOfMapOne_apply (p : A →ₙₐ[F] B) (h : p 1 = 1) (x : A) :
    p.toAlgHomOfMapOne h x = p x :=
  rfl

/-- **Into a domain, a non-unital algebra map is the zero map or unital.** `p 1` is idempotent,
hence `0` or `1`, and at `0` the map vanishes everywhere. -/
theorem eq_zero_or_map_one {B : Type*} [Ring B] [IsDomain B] [Algebra F B] (p : A →ₙₐ[F] B) :
    p = 0 ∨ p 1 = 1 := by
  have hidem : IsIdempotentElem (p 1) := by
    change p 1 * p 1 = p 1
    rw [← map_mul, mul_one]
  refine (IsIdempotentElem.iff_eq_zero_or_one.mp hidem).imp (fun h => ?_) id
  ext x
  rw [NonUnitalAlgHom.zero_apply, ← mul_one x, map_mul, h, mul_zero]

/-- A non-unital algebra map into a domain that is not the zero map is unital. -/
theorem map_one_of_ne_zero {B : Type*} [Ring B] [IsDomain B] [Algebra F B] {p : A →ₙₐ[F] B}
    (hp : p ≠ 0) : p 1 = 1 :=
  p.eq_zero_or_map_one.resolve_left hp

end NonUnitalAlgHom

end
