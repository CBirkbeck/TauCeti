/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1

/-!
# The Hecke triple of `Γ₀(N)`

The image of `Γ₀(N)` in `GL₂(ℚ)` forms a Hecke triple with the same submonoid `Δ₀(N)` that
carries the Hecke triple of `Γ₁(N)`. This is the setting of Shimura §3.3: the Hecke ring
`R(Γ₀(N), Δ₀(N))` whose operators act on `M_k(Γ₀(N))`.

`Δ₀(N)` is reused verbatim from `TauCeti.NumberTheory.HeckeRing.GL2.Gamma1`; nothing about it
is specific to `Γ₁(N)`. What differs is only which group sits inside it, and the containment
`Γ₀(N) ≤ Δ₀(N)` is already available there as `Gamma0_map_le_Delta0` — it is exactly the
statement that made `Δ₀(N)` be defined with a *unit* upper-left entry rather than `a ≡ 1`.

The two triples are genuinely different Hecke rings, not two names for one: `Γ₁(N) ≤ Γ₀(N)`,
so `R(Γ₀(N), Δ₀(N))` is the smaller ring, and the surjection between them (Shimura Thm 3.35)
is what identifies the level-`N` operators with their level-one preimages.

## Main definitions

* `HeckeRing.GL2.Gamma0Image`: the image of `Γ₀(N)` in `GL₂(ℚ)`.

## Main results

* `HeckeRing.GL2.Delta0_le_commensurator_Gamma0Image`: `Δ₀(N)` lies in the commensurator of
  `Γ₀(N)`.
* the `IsHeckeTriple (Delta0 N) (Gamma0Image N) (Gamma0Image N)` instance.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup
  Subgroup.Commensurable HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- The image of `Γ₀(N)` in `GL₂(ℚ)`. -/
noncomputable def Gamma0Image : Subgroup (GL (Fin 2) ℚ) :=
  (Gamma0 N).map (mapGL ℚ)

/-- Membership in the image of `Γ₀(N)`, by an integral witness. -/
@[simp] lemma mem_Gamma0Image_iff {g : GL (Fin 2) ℚ} :
    g ∈ Gamma0Image N ↔ ∃ σ ∈ Gamma0 N, mapGL ℚ σ = g := by
  rw [Gamma0Image, Subgroup.mem_map]

variable [NeZero N]

/-- `Γ₀(N)` is commensurable with `SL₂(ℤ)`: it has finite index in it. -/
lemma commensurable_Gamma0Image_SLnZ : Commensurable (Gamma0Image N) (SLnZ 2) :=
  commensurable_map_SLnZ 2 (Gamma0 N)

/-- `Δ₀(N)` lies in the commensurator of `Γ₀(N)`: it lies in that of `SL₂(ℤ)`, and the two
groups are commensurable. -/
lemma Delta0_le_commensurator_Gamma0Image :
    Delta0 N ≤ (commensurator (Gamma0Image N)).toSubmonoid := by
  rw [Subgroup.Commensurable.eq (commensurable_Gamma0Image_SLnZ N)]
  exact (Delta0_le_posDetInt N).trans (posDetInt_le_commensurator 2)

/-- **The Hecke triple of `Γ₀(N)`**: `Γ₀(N) ≤ Δ₀(N) ≤ commensurator(Γ₀(N))` inside `GL₂(ℚ)` —
the setting of Shimura §3.3, in which the Hecke ring `R(Γ₀(N), Δ₀(N))` is formed. -/
instance : IsHeckeTriple (Delta0 N) (Gamma0Image N) (Gamma0Image N) :=
  IsHeckeTriple.of_diagonal (Gamma0_map_le_Delta0 N) (Delta0_le_commensurator_Gamma0Image N)

end HeckeRing.GL2
