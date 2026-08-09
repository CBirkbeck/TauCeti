/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Transporting the value group along an equivalence of valuations

Mathlib's `Valuation.IsEquiv.orderMonoidIso` is an isomorphism of the value monoids *with
zero*, `ValueGroup₀ (.ofClass v) ≃*o ValueGroup₀ (.ofClass w)`. Consumers that work with the
value **group** — for instance any convex subgroup of it — need the corresponding
isomorphism of groups, which this file supplies.

Since `ValueGroup₀ f = WithZero ↥(valueGroup f)`, it is exactly the inverse of Mathlib's
`OrderMonoidIso.withZero`, the equivalence between order isomorphisms of two groups and
order isomorphisms of those groups with a zero adjoined.

## Main definitions

* `Valuation.IsEquiv.valueGroupOrderIso` : The induced order isomorphism of value groups.

-/

public section

namespace TauCeti.Valuation

open MonoidWithZeroHom

variable {A : Type*} [Ring A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀']

/-- The order isomorphism of **value groups** induced by an equivalence of valuations.
Mathlib's `IsEquiv.orderMonoidIso` is an isomorphism of the value monoids *with zero*, and
`ValueGroup₀ f = WithZero ↥(valueGroup f)`, so this is exactly the inverse of Mathlib's
`OrderMonoidIso.withZero`, which identifies order isomorphisms of two groups with those of
the groups with zero adjoined. -/
noncomputable def _root_.Valuation.IsEquiv.valueGroupOrderIso {v : Valuation A Γ₀}
    {w : Valuation A Γ₀'} (h : v.IsEquiv w) :
    valueGroup (.ofClass v) ≃*o valueGroup (.ofClass w) :=
  OrderMonoidIso.withZero.symm h.orderMonoidIso

/-- The induced value-group isomorphism agrees with `orderMonoidIso` under the coercion. -/
@[simp]
theorem _root_.Valuation.IsEquiv.valueGroupOrderIso_coe {v : Valuation A Γ₀}
    {w : Valuation A Γ₀'} (h : v.IsEquiv w) (γ : valueGroup (.ofClass v)) :
    ((h.valueGroupOrderIso γ : valueGroup (.ofClass w)) : ValueGroup₀ (.ofClass w))
      = h.orderMonoidIso (γ : ValueGroup₀ (.ofClass v)) :=
  (rfl)

end TauCeti.Valuation
