/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.Restricted.PowerSeries

/-!
# The two-sided restricted Laurent object — SCAFFOLD
-/

public section

open Filter

open scoped Topology

namespace TauCeti.Huber

variable (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **Wedhorn Example 6.39.** The coefficient families of `A⟨X, X⁻¹⟩`: two-sided families
`a : ℤ → A` such that for every neighbourhood `U` of zero, `aₙ ∈ U` for all but finitely many
`n` — that is, `a` tends to `0` along `cofinite`. -/
def laurentRestricted : Submodule A (ℤ → A) where
  carrier := {a | ZeroAtFilter cofinite a}
  zero_mem' := zero_zeroAtFilter _
  add_mem' ha hb := ha.add hb
  smul_mem' c _ ha := ha.smul c

end TauCeti.Huber
