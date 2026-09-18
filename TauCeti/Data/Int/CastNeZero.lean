/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Group.Even

/-!
# Integer casts that stay nonzero

Two ways an integer known to be nonzero in a ring stays nonzero: along a faithful algebra, where
the structure map is injective, and at `2` when the integer is even — an even integer invertible
in a ring forces `2` to be, since it is `2` times something.

Both are what an invertibility hypothesis on an index gets used for: `(n : R) ≠ 0` travels to an
extension, and at even `n` it yields `(2 : R) ≠ 0`.
-/

public section

namespace Int

/-- **A nonzero integer cast stays nonzero along a faithful algebra**, the structure map being
injective there. -/
theorem cast_ne_zero_of_algebraMap {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    [FaithfulSMul R A] {n : ℤ} (h : (n : R) ≠ 0) : (n : A) ≠ 0 := by
  intro h₀
  refine h (FaithfulSMul.algebraMap_injective R A ?_)
  rw [map_intCast, h₀, map_zero]

/-- **An even integer invertible in a ring makes `2` invertible there**: it is `2` times something,
so `2` cannot vanish. -/
theorem two_ne_zero_of_even_of_cast_ne_zero {R : Type*} [NonAssocRing R] {n : ℤ} (heven : Even n)
    (h : (n : R) ≠ 0) : ((2 : ℤ) : R) ≠ 0 := by
  obtain ⟨m, rfl⟩ := heven
  intro h₀
  refine h ?_
  push_cast at h₀ ⊢
  rw [← two_mul, h₀, zero_mul]

end Int

end
