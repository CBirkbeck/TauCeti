/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import
  TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Mackey.AllDegrees

/-!
# Finite Mackey decomposition

For the discrete symmetric group on three letters, every subgroup is open and closed.
The cohomological restriction–transfer identity is therefore a finite double-coset sum
in every degree, for any discrete coefficient module.
-/

public section

open CategoryTheory TauCeti.ContCohomology TauCeti.ContinuousCohomology

namespace TauCeti.Examples.FiniteMackey

local instance permTopology : TopologicalSpace (Equiv.Perm (Fin 3)) := ⊥
local instance permDiscrete : DiscreteTopology (Equiv.Perm (Fin 3)) := ⟨rfl⟩
local instance permCompact : CompactSpace (Equiv.Perm (Fin 3)) := Finite.compactSpace

variable (U V : Subgroup (Equiv.Perm (Fin 3))) (M : Type) [AddCommGroup M]
  [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction (Equiv.Perm (Fin 3)) M]

local instance moduleContinuousSMul : ContinuousSMul (Equiv.Perm (Fin 3)) M where
  continuous_smul := continuous_of_discreteTopology

example (r : DoubleCoset.Quotient (V : Set (Equiv.Perm (Fin 3))) (U : Set (Equiv.Perm (Fin 3))) →
    Equiv.Perm (Fin 3))
    (hr : ∀ D, DoubleCoset.mk V U (r D) = D) (n : ℕ) :
    letI := Fintype.ofFinite (DoubleCoset.Quotient (V : Set (Equiv.Perm (Fin 3)))
      (U : Set (Equiv.Perm (Fin 3))))
    corestriction U M (isOpen_discrete _) n ≫
        res V (ofDiscreteModule ℤ (Equiv.Perm (Fin 3)) M) n =
      ∑ D, mackeyTerm U V M (isOpen_discrete _) (isClosed_discrete _) (r D) n := by
  exact corestriction_mackey U V M (isOpen_discrete _) (isClosed_discrete _) r hr n

end TauCeti.Examples.FiniteMackey
