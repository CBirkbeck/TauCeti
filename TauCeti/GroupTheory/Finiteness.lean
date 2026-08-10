/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Two closure properties of finitely generated groups

Mathlib has a substantial theory of finitely generated commutative groups in
`Mathlib/GroupTheory/FiniteAbelian/Basic.lean` — the structure theorem, `finite_of_fg_isMulTorsion`,
and `Subgroup.finiteIndex_range_powMonoidHom_of_fg`, which is the finiteness of `G ⧸ Gⁿ`. Two
closure properties it does not carry are collected here:

## Main results

* `Subgroup.fg_of_commGroup_fg`: a subgroup of a finitely generated commutative group is finitely
  generated. This is Noetherianity of `ℤ` transported through `Additive`; because the proof passes
  through `Additive G`, `to_additive` cannot produce it and an additive version would have to be
  written by hand.
* `Group.fg_of_fg_ker_of_fg_range`: an extension of finitely generated groups is finitely
  generated — if the kernel and the range of `φ : G →* H` are finitely generated then so is `G`,
  the generators being preimages of generators of the range together with generators of the
  kernel. This one needs no commutativity and *is* `@[to_additive]`.

Both are steps towards the `S`-unit group being finitely generated, which
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 names as an input to the weak Mordell–Weil
theorem: the group of `S`-units sits in an extension whose kernel is the unit group of the base
and whose range is a subgroup of a free group of rank `|S|`, so establishing finite generation
needs exactly these two facts. The finiteness that the descent then applies to it is Mathlib's
`Subgroup.finiteIndex_range_powMonoidHom_of_fg`, read through
`Subgroup.finiteIndex_iff_finite_quotient`; nothing here reproves it.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll). Following this repository's convention
for adapted material, the upstream authorship is credited here rather than in the copyright header.

That source file also carries `finite_modPow`, `finite_of_fg_of_pow_eq_one` and two `ℤ`-module
translation helpers. **None of them is ported: all four are now in Mathlib** — as
`Subgroup.finiteIndex_range_powMonoidHom_of_fg`, `CommGroup.finite_of_fg_isMulTorsion`, the
instance `AddMonoid.FG.to_moduleFinite_int`, and `Module.Finite.iff_addGroup_fg` composed with
`AddGroup.fg_iff_mul_fg`. The source predates those additions, some of which its own author
upstreamed, so check Mathlib again before porting anything further from it.
-/

public section

/-- A subgroup of a finitely generated commutative group is finitely generated, as `ℤ` is a
Noetherian ring: `Additive G` is then a finitely generated `ℤ`-module, hence Noetherian, so the
submodule corresponding to `H` is finitely generated. (The proof passes through `Additive G`, so
`to_additive` cannot translate it.) -/
theorem Subgroup.fg_of_commGroup_fg {G : Type*} [CommGroup G] [Group.FG G] (H : Subgroup G) :
    Group.FG H :=
  AddGroup.fg_iff_mul_fg.mp <| Module.Finite.iff_addGroup_fg.mp <| Module.Finite.iff_fg.mpr <|
    IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule H.toAddSubgroup)

/-- An extension of finitely generated groups is finitely generated: if the kernel and the range
of `φ : G →* H` are finitely generated, then so is `G`. The generators are preimages of
generators of the range together with generators of the kernel. -/
@[to_additive /-- An extension of finitely generated additive groups is finitely generated: if the
kernel and the range of `φ : G →+ H` are finitely generated, then so is `G`. The generators are
preimages of generators of the range together with generators of the kernel. -/]
theorem Group.fg_of_fg_ker_of_fg_range {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hker : Group.FG φ.ker) (hrange : Group.FG φ.range) : Group.FG G := by
  obtain ⟨T, hT, hTfin⟩ := Group.fg_iff.mp hrange
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp hker
  set σ : φ.range → G := Function.surjInv φ.rangeRestrict_surjective with hσ
  set U : Set G := σ '' T ∪ (φ.ker.subtype '' S) with hU
  refine Group.fg_iff.mpr ⟨U, ?_, (hTfin.image σ).union (hSfin.image _)⟩
  -- the kernel is contained in the closure of `U`
  have hkerle : φ.ker ≤ Subgroup.closure U := by
    calc φ.ker = (⊤ : Subgroup φ.ker).map φ.ker.subtype := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (Subgroup.closure S).map φ.ker.subtype := by rw [hS]
      _ = Subgroup.closure (φ.ker.subtype '' S) := MonoidHom.map_closure ..
      _ ≤ Subgroup.closure U := Subgroup.closure_mono Set.subset_union_right
  -- the closure of `U` surjects onto the range
  have hmap : (Subgroup.closure U).map φ.rangeRestrict = ⊤ := by
    rw [eq_top_iff, ← hT]
    refine (Subgroup.closure_mono ?_).trans_eq (MonoidHom.map_closure ..).symm
    intro t ht
    exact ⟨σ t, Set.mem_union_left _ ⟨t, ht, rfl⟩, Function.surjInv_eq _ t⟩
  -- so `U` generates everything, by `comap_map_eq` for the range restriction
  have h := Subgroup.comap_map_eq φ.rangeRestrict (Subgroup.closure U)
  rw [hmap, Subgroup.comap_top, MonoidHom.ker_rangeRestrict, sup_eq_left.mpr hkerle] at h
  exact h.symm

end
