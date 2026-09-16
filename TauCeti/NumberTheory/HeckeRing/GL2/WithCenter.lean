/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Index.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic

/-!
# Adjoining the centre to a subgroup of `Γ₀(N)`

`Γ.withCenter = Γ ⊔ Z(G)` is the enlargement that makes "this subgroup contains `-I`" true.
It is needed because `Γ₁(N)` does **not** contain `-I` once `N ≥ 3`, so any fundamental-domain
or Petersson argument whose hypothesis is that containment has to run over the enlarged group.

Both facts below are about an arbitrary `H ≤ Γ₀(N)` and say nothing about `Γ₁(N)`: the
enlargement costs nothing on the `Δ₀(N)` side of a Hecke triple, because `Γ₀(N)` already
contains `-I` and so absorbs the central factor. `Gamma1/WithCenter.lean` is the consumer,
where `H := Γ₁(N)` gives the triple of `Γ₁(N)·{±I}`.

## Main results

* `HeckeRing.GL2.withCenter_le_Gamma0`: adjoining the centre keeps a subgroup of `Γ₀(N)`
  inside `Γ₀(N)`.
* `HeckeRing.GL2.map_withCenter_le_Delta0`: and its image in `GL₂(ℚ)` inside `Δ₀(N)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1–3.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn Subgroup

open scoped MatrixGroups Pointwise

namespace HeckeRing.GL2

variable (N : ℕ)

/-- **Adjoining the centre keeps a subgroup of `Γ₀(N)` inside `Γ₀(N)`.** The central factor is
absorbed: the centre of `SL₂(ℤ)` is `{±I}`, and `Γ₀(N)` contains `-I`. -/
lemma withCenter_le_Gamma0 {H : Subgroup SL(2, ℤ)} (hH : H ≤ Gamma0 N) :
    H.withCenter ≤ Gamma0 N :=
  withCenter_le_iff.mpr ⟨hH, fun _ hγ ↦ by
    rcases mem_center_iff_eq_one_or_eq_neg_one.mp hγ with rfl | rfl
    · exact one_mem _
    · simp⟩

/-- **`H·{±I} ≤ Δ₀(N)`** for `H ≤ Γ₀(N)`, transported to the images in `GL₂(ℚ)`. -/
lemma map_withCenter_le_Delta0 {H : Subgroup SL(2, ℤ)} (hH : H ≤ Gamma0 N) :
    ((H.withCenter).map (mapGL ℚ)).toSubmonoid ≤ Delta0 N :=
  fun _ hg ↦ Gamma0Image_le_Delta0 N ((mem_Gamma0Image_iff N).mpr
    (Subgroup.mem_map.mp (Subgroup.map_mono (withCenter_le_Gamma0 N hH) hg)))

end HeckeRing.GL2
