/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.Basic
public import TauCeti.NumberTheory.ModularForms.WithCenter

/-!
# The Hecke triple of `Γ₁(N)·{±I}`

`Gamma1/Basic.lean` puts `Γ₁(N)` into a Hecke triple `Γ₁(N) ≤ Δ₀(N) ≤ commensurator(Γ₁(N))`.
This file does the same for `Γ₁(N)·{±I}`, the subgroup `(Gamma1 N).withCenter` obtained by
adjoining the centre of `SL₂(ℤ)`.

## Why the enlarged group is the one some statements need

`Γ₁(N)` does **not** contain `-I` once `N ≥ 3` — `-I` has diagonal `(-1, -1)` while `Γ₁(N)` asks
for `≡ (1, 1)`, so `CongruenceSubgroup.neg_one_mem_Gamma1_iff` holds exactly when `N ∣ 2`. Any
statement whose hypothesis is "this subgroup contains `-I`" is therefore simply false at `Γ₁(N)`
for almost every level, and a fundamental-domain or Petersson argument that needs it has to run
over a group that does contain it.

`Γ.withCenter = Γ ⊔ Z(G)` contains `-I` for **every** `Γ`, and it is the group TauCeti's Petersson
layer already works with: `ModularForms.peterssonInnerCosets` sums over `SL(2, ℤ) ⧸ Γ.withCenter`.
What was missing is that this enlarged group is itself a Hecke triple with the same `Δ₀(N)`, which
is what lets a Hecke coset be formed over it at all.

Nothing here is deep — the point is that the passage from `Γ₁(N)` to `Γ₁(N)·{±I}` costs nothing
on either side of the triple. Containment in `Δ₀(N)` survives because `Γ₀(N)` already contains
`-I`, so it absorbs the central factor and `Γ₁(N)·{±I} ≤ Γ₀(N)` still holds; commensurability
survives because the enlarged group still has finite index in `SL₂(ℤ)`, containing `Γ₁(N)`.

## Main results

* `HeckeRing.GL2.Gamma1_withCenter_le_Gamma0`: `Γ₁(N)·{±I} ≤ Γ₀(N)`.
* `HeckeRing.GL2.map_Gamma1_withCenter_le_Delta0` and
  `HeckeRing.GL2.Delta0_le_commensurator_map_Gamma1_withCenter`: the two halves of the triple.
* the `IsHeckeTriple (Delta0 N) ((Gamma1 N).withCenter.map (mapGL ℚ))` instance they found.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1–3.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn Subgroup

open scoped MatrixGroups Pointwise

namespace HeckeRing.GL2

variable (N : ℕ)

/-- **`Γ₁(N)·{±I} ≤ Γ₀(N)`.** The central factor is absorbed: `Γ₀(N)` contains `-I`, so it is
closed under negation, and `Γ₁(N) ≤ Γ₀(N)` already. -/
lemma Gamma1_withCenter_le_Gamma0 : (Gamma1 N).withCenter ≤ Gamma0 N := by
  intro γ hγ
  obtain ⟨δ, hδ, h | h⟩ := Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mp hγ
  · exact h ▸ Gamma1_in_Gamma0 N hδ
  · have hn : (-δ : SL(2, ℤ)) = (-1 : SL(2, ℤ)) * δ := by simp
    exact h ▸ hn ▸ (Gamma0 N).mul_mem (by simp) (Gamma1_in_Gamma0 N hδ)

/-- **`Γ₁(N)·{±I} ≤ Δ₀(N)`**, transported to the images in `GL₂(ℚ)`. -/
lemma map_Gamma1_withCenter_le_Delta0 :
    (((Gamma1 N).withCenter).map (mapGL ℚ)).toSubmonoid ≤ Delta0 N := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact Gamma0Image_le_Delta0 N
    ((mem_Gamma0Image_iff N).mpr ⟨σ, Gamma1_withCenter_le_Gamma0 N hσ, rfl⟩)

variable [NeZero N]

/-- `Γ₁(N)·{±I}` still has finite index in `SL₂(ℤ)`: it contains `Γ₁(N)`, which does. -/
instance : ((Gamma1 N).withCenter).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Subgroup.le_withCenter (Gamma1 N))

/-- **`Δ₀(N)` lies in the commensurator of `Γ₁(N)·{±I}`**: it lies in that of `SL₂(ℤ)`, and the
two groups are commensurable, the enlarged group still having finite index. -/
lemma Delta0_le_commensurator_map_Gamma1_withCenter :
    Delta0 N ≤
      (Commensurable.commensurator (((Gamma1 N).withCenter).map (mapGL ℚ))).toSubmonoid := by
  rw [Commensurable.eq (commensurable_map_SLnZ 2 ((Gamma1 N).withCenter))]
  exact (Delta0_le_posDetInt N).trans (posDetInt_le_commensurator 2)

/-- **The Hecke triple of `Γ₁(N)·{±I}`**: `Γ₁(N)·{±I} ≤ Δ₀(N) ≤ commensurator(Γ₁(N)·{±I})` inside
`GL₂(ℚ)`, with the same monoid `Δ₀(N)` as the triple of `Γ₁(N)` itself.

Stated at the unfolded `((Gamma1 N).withCenter).map (mapGL ℚ)` for the same reason the `Γ₁(N)`
instance is: instance search unfolds no abbreviation, and this is the spelling a consumer meets. -/
instance : IsHeckeTriple (Delta0 N) (((Gamma1 N).withCenter).map (mapGL ℚ))
    (((Gamma1 N).withCenter).map (mapGL ℚ)) :=
  IsHeckeTriple.of_diagonal (map_Gamma1_withCenter_le_Delta0 N)
    (Delta0_le_commensurator_map_Gamma1_withCenter N)

end HeckeRing.GL2
