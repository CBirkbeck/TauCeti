/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# The pullback of a regular function is regular

`Isogeny/Basic.lean` models an isogeny contravariantly, by a pullback
`W₂.CoordinateRing →ₐ[F] W₁.FunctionField` into the *function field* of the source. This file
records that the pullback in fact lands in the *coordinate ring*: a function regular on `W₂` pulls
back to one regular on `W₁`.

## Why this is not immediate

`MapsInfinity` — the pointedness condition carried by every `Isogeny` — says that every element of
`W₁.CoordinateRing` is integral over `W₂.CoordinateRing`. That is the opposite direction: it
controls the source coordinate ring in terms of the target, not the image of the pullback. The
statement here is what lets the two coordinate rings be compared at all, and it is what
`IntermediateRing/Finite.lean` needs in order to drop its separability hypothesis.
-/

public section

namespace TauCeti

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

namespace Isogeny

/-- **The pullback of a regular function is regular.** The pullback of an isogeny lands in the
image of the source coordinate ring, not merely in the source function field. -/
theorem pullback_mem_range (φ : Isogeny W₁ W₂) [IsDedekindDomain W₁.CoordinateRing]
    (x : W₂.CoordinateRing) :
    φ.pullback x ∈ (algebraMap W₁.CoordinateRing W₁.FunctionField).range := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    W₁.FunctionField _ (fun v => ?_)
  sorry

end Isogeny

end TauCeti
