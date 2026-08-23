/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Eliminating the constructors of an affine point

`WeierstrassCurve.Affine.Point` is a two-constructor inductive type: the point at infinity, and an
affine point together with a nonsingularity certificate. Matching on it is normally a `rcases`, but
that is unavailable when the point is a compound term such as `n • P` — the case split has to
generalise the term first, and then the connection to `n • P` is lost.

This file states the elimination as an existential instead, so that it applies to any term.

## Main results

* `WeierstrassCurve.Affine.Point.exists_eq_some_of_ne_zero`: a nonzero affine point is `.some`,
  in a form that applies to a compound point.
-/

public section

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [CommRing F] {E : WeierstrassCurve F}

/-- **A nonzero affine point is `.some`.** This is the `rcases` on `Affine.Point`'s two
constructors, packaged as an existential so that it can be applied to a compound point such as
`n • P` without first generalising it — which would discard the equation identifying the result
with `n • P`, the very thing consumers go on to rewrite with. -/
theorem exists_eq_some_of_ne_zero {P : Affine.Point E.toAffine} (hP : P ≠ 0) :
    ∃ x y, ∃ hns : E.toAffine.Nonsingular x y, P = .some _ _ hns := by
  rcases P with _ | ⟨_, _, hns⟩
  · exact absurd rfl hP
  · exact ⟨_, _, hns, rfl⟩

end WeierstrassCurve.Affine.Point
