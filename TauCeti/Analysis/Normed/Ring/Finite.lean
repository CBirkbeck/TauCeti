/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Homomorphisms from a finite group to the units of a normed ring

Every element of a finite (left-cancellative) monoid has finite order, hence so does its image
under a homomorphism, and an element of finite order in a normed ring with multiplicative norm has
norm `1` (`IsOfFinOrder.norm_eq_one`). This file records the consequence for homomorphisms into the
unit group, the multiplicative counterpart of Mathlib's `AddChar.norm_apply`: a character of a
finite group, such as a nebentypus character on `(ZMod N)ˣ`, takes values of norm `1`.

## Main results

* `MonoidHom.norm_coe_apply`: `‖(χ g : α)‖ = 1` for `χ : G →* αˣ` and `G` finite.
-/

public section

namespace MonoidHom

variable {G α : Type*} [LeftCancelMonoid G] [Finite G] [NormedRing α] [NormMulClass α]
  [NormOneClass α]

/-- **A homomorphism from a finite group to the units of a normed ring takes values of norm
`1`.** The multiplicative counterpart of `AddChar.norm_apply`. -/
@[simp]
theorem norm_coe_apply (χ : G →* αˣ) (g : G) : ‖(χ g : α)‖ = 1 :=
  (((Units.coeHom α).comp χ).isOfFinOrder (isOfFinOrder_of_finite g)).norm_eq_one

end MonoidHom
