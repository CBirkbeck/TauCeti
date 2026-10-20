/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.Data.List.Rotate
public import Mathlib.Algebra.Group.Conj

/-!
# Conjugacy and cyclic rotation in free groups

Rotating a word conjugates the free-group element it represents. Together with Mathlib's
explicit cyclic-reduction conjugator, this relates rotation of cyclic reductions to
conjugacy of the original elements.

The word decomposition used here is from
`Mathlib.GroupTheory.FreeGroup.CyclicallyReduced`.
-/

public section

namespace FreeGroup

variable {α : Type*}

/-- Rotating a word is conjugation by the inverse of its initial segment. -/
theorem conj_mk_rotate (u : List (α × Bool)) (n : ℕ) :
    (mk (u.take (n % u.length)))⁻¹ * mk u * mk (u.take (n % u.length)) =
      mk (u.rotate n) := by
  let p := u.take (n % u.length)
  let q := u.drop (n % u.length)
  have hu : u = p ++ q := (List.take_append_drop _ _).symm
  have hv : u.rotate n = q ++ p := List.rotate_eq_drop_append_take_mod
  calc
    _ = (mk p)⁻¹ * (mk p * mk q) * mk p := by rw [mul_mk, ← hu]
    _ = mk q * mk p := by rw [inv_mul_cancel_left]
    _ = mk (u.rotate n) := by rw [hv, ← mul_mk]

/-- Two words related by a cyclic rotation represent conjugate elements of a free group.
The words need not be reduced. -/
theorem isConj_mk_of_isRotated {u v : List (α × Bool)} (h : u.IsRotated v) :
    IsConj (mk u) (mk v) := by
  obtain ⟨n, rfl⟩ := h
  exact isConj_iff.mpr ⟨(mk (u.take (n % u.length)))⁻¹,
    by simpa only [inv_inv] using conj_mk_rotate u n⟩

/-- The cyclic reduction of a reduced-word representative has an explicit group conjugator. -/
theorem mk_conjugator_mul_mk_reduceCyclically (x : FreeGroup α) [DecidableEq α] :
    mk (reduceCyclically.conjugator x.toWord) *
        mk (reduceCyclically x.toWord) *
        (mk (reduceCyclically.conjugator x.toWord))⁻¹ = x := by
  rw [inv_mk, mul_mk, mul_mk,
    reduceCyclically.conj_conjugator_reduceCyclically, mk_toWord]

/-- Every free-group element is conjugate to its cyclic reduction. -/
theorem isConj_mk_reduceCyclically (x : FreeGroup α) [DecidableEq α] :
    IsConj x (mk (reduceCyclically x.toWord)) := by
  apply IsConj.symm
  exact isConj_iff.mpr ⟨mk (reduceCyclically.conjugator x.toWord),
    mk_conjugator_mul_mk_reduceCyclically x⟩

/-- Elements whose cyclic reductions differ by a rotation are conjugate. -/
theorem isConj_of_isRotated_reduceCyclically [DecidableEq α] {x y : FreeGroup α}
    (h : (reduceCyclically x.toWord).IsRotated (reduceCyclically y.toWord)) :
    IsConj x y :=
  (isConj_mk_reduceCyclically x).trans <|
    (isConj_mk_of_isRotated h).trans (isConj_mk_reduceCyclically y).symm

end FreeGroup
