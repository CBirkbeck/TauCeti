/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# A `Fintype` structure on the subgroups of a finite group

## Main definitions

* `Subgroup.fintypeOfFinite`: the `Fintype` structure `Fintype.ofFinite` on a subgroup of a finite
  group.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

-- Not a global instance: Mathlib's `Subgroup.instFintypeSubtypeMemOfDecidablePred` asks for
-- decidable membership instead, and the two structures are not definitionally equal. Files about
-- the subgroups of a finite group install this one with `attribute [local instance]`, so that
-- their statements share one `Fintype` structure.
/-- The `Fintype` structure on a subgroup of a finite group given by `Fintype.ofFinite`. -/
@[instance_reducible, expose]
noncomputable def fintypeOfFinite [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

end Subgroup
