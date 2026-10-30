/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Binary cycles in finite coordinates

When the vertex and chosen-dart types are finite, binary edge and vertex chains may be
represented by functions rather than finitely supported functions. The incidence boundary and its
cycle space in these coordinates agree with the Finsupp construction. In particular, loops
contribute zero columns
and parallel darts retain separate coordinates.

This comparison lets a spanning-forest cycle basis be used in either representation.

## References

* A. Hatcher, *Algebraic Topology*, §2.2 (incidence boundaries).
* R. Diestel, *Graph Theory*, §1.9 (binary cycle spaces).
-/

public section

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph) (O : Set Γ.E) [Finite Γ.V] [Finite O]

/-- The binary incidence boundary on finite-function coordinates. An edge contributes one at
each distinct endpoint; a loop contributes zero. -/
noncomputable def cycleBoundary : (O → ZMod 2) →ₗ[ZMod 2] (Γ.V → ZMod 2) :=
  (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) Γ.V).toLinearMap.comp <|
    (Γ.modTwoCycleBoundary O).comp
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm.toLinearMap

/-- The binary cycle space of a finite Serre graph in finite-function coordinates. -/
noncomputable def cycleSpace : Submodule (ZMod 2) (O → ZMod 2) :=
  (Γ.cycleBoundary O).ker

@[simp] theorem cycleBoundary_apply (c : O → ZMod 2) (v : Γ.V) :
    Γ.cycleBoundary O c v =
      Γ.modTwoCycleBoundary O
        ((Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm c) v :=
  by simp only [cycleBoundary, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Finsupp.linearEquivFunOnFinite_apply]

/-- The incidence column of a dart has a coefficient at each endpoint and vanishes for a loop. -/
@[simp] theorem cycleBoundary_single [DecidableEq O] [DecidableEq Γ.V] (e : O) :
    Γ.cycleBoundary O (Pi.single e 1) =
      Pi.single (Γ.tgt e.1) 1 - Pi.single (Γ.src e.1) 1 := by
  ext v
  simp [cycleBoundary_apply, Finsupp.linearEquivFunOnFinite_symm_single,
    incidenceBoundary_single, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- A finite binary edge chain is a cycle precisely when its Finsupp representation is one. -/
@[simp] theorem mem_cycleSpace_iff (c : O → ZMod 2) :
    c ∈ Γ.cycleSpace O ↔
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm c ∈
        Γ.modTwoCycleSpace O := by
  rw [cycleSpace, LinearMap.mem_ker, mem_modTwoCycleSpace_iff]
  simp [cycleBoundary]

/-- The finite-function boundary is the Finsupp boundary transported through the two
coordinate equivalences. -/
theorem cycleBoundary_finsupp :
    (Γ.cycleBoundary O).comp
        (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).toLinearMap =
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) Γ.V).toLinearMap.comp
        (Γ.modTwoCycleBoundary O) := by
  ext c v
  simp [cycleBoundary]

private noncomputable def cycleSpaceToFinsupp :
    Γ.cycleSpace O →ₗ[ZMod 2] Γ.modTwoCycleSpace O where
  toFun := fun c => ⟨(Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm c,
    (Γ.mem_cycleSpace_iff O c).mp c.property⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    simp
  map_smul' := by
    intro r a
    apply Subtype.ext
    simp

/-- The binary cycle space in finite-function coordinates is linearly equivalent to the
Finsupp kernel, with each edge coordinate preserved. -/
noncomputable def cycleSpaceFinsuppEquiv :
    Γ.cycleSpace O ≃ₗ[ZMod 2] Γ.modTwoCycleSpace O where
  toLinearMap := Γ.cycleSpaceToFinsupp O
  invFun := fun c => ⟨(Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O) c,
    by rw [Γ.mem_cycleSpace_iff]; simp [c.property]⟩
  left_inv := by
    intro c
    apply Subtype.ext
    simp [cycleSpaceToFinsupp]
  right_inv := by
    intro c
    apply Subtype.ext
    simp [cycleSpaceToFinsupp]

@[simp] theorem cycleSpaceFinsuppEquiv_apply (c : Γ.cycleSpace O) :
    (Γ.cycleSpaceFinsuppEquiv O c : O →₀ ZMod 2) =
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm c :=
  by
    rw [cycleSpaceFinsuppEquiv]
    simp [cycleSpaceToFinsupp]

@[simp] theorem cycleSpaceFinsuppEquiv_symm_apply (c : Γ.modTwoCycleSpace O) :
    ((Γ.cycleSpaceFinsuppEquiv O).symm c : O → ZMod 2) =
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O) c := by
  let e := Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O
  have h := congrArg Subtype.val ((Γ.cycleSpaceFinsuppEquiv O).apply_symm_apply c)
  rw [cycleSpaceFinsuppEquiv_apply] at h
  calc
    ((Γ.cycleSpaceFinsuppEquiv O).symm c : O → ZMod 2) =
        e (e.symm ((Γ.cycleSpaceFinsuppEquiv O).symm c : O → ZMod 2)) :=
      (e.apply_symm_apply _).symm
    _ = e c := congrArg e h

end TauCeti.SerreGraph
