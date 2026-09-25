/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# A semisimple module is the direct sum of its isotypic components

Mathlib shows that the isotypic components of a module are independent
(`sSupIndep_isotypicComponents`) and, for a semisimple module, span it
(`sSup_isotypicComponents`); it reads off the consequence for endomorphisms
(`IsSemisimpleModule.endAlgEquiv`). This file records the consequence for the module itself: a
semisimple module is the internal direct sum of its isotypic components. When there are finitely
many components, for instance when the module is Noetherian, composing with
`DFinsupp.linearEquivFunOnFintype` presents it as their product.

## Main definitions

* `TauCeti.IsSemisimpleModule.linearEquivIsotypicComponents`: a semisimple module is linearly
  equivalent to the direct sum of its isotypic components.
-/

public section

namespace TauCeti.IsSemisimpleModule

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
  [DecidableEq (isotypicComponents R M)]

/-- **A semisimple module is the direct sum of its isotypic components.** The equivalence sends
an element to its family of components, and its inverse adds the components up. This is the
module-level counterpart of `IsSemisimpleModule.endAlgEquiv`. -/
noncomputable def linearEquivIsotypicComponents : M ≃ₗ[R] Π₀ c : isotypicComponents R M, c.1 :=
  .symm <| ((sSupIndep_iff _).mp <| sSupIndep_isotypicComponents R M).linearEquiv <|
    (sSup_eq_iSup' _).symm.trans <| sSup_isotypicComponents R M

end TauCeti.IsSemisimpleModule
