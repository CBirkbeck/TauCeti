/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Finiteness

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Two closure properties of finitely generated groups

Mathlib has a substantial theory of finitely generated commutative groups in
`Mathlib/GroupTheory/FiniteAbelian/Basic.lean` — the structure theorem, `finite_of_fg_isMulTorsion`,
and `Subgroup.finiteIndex_range_powMonoidHom_of_fg`, which is the finiteness of `G ⧸ Gⁿ`. Two
closure properties it does not carry are collected here, each in both forms and each an
`instance`, matching how Mathlib states its other `FG` closure properties (`Group.fg_range`,
`QuotientGroup.fg`):

## Main results

* `AddSubgroup.fg_of_addCommGroup` and `Subgroup.fg_of_commGroup`: a subgroup of a finitely
  generated commutative group is finitely generated. The argument is Noetherianity of `ℤ`, so the
  *additive* statement is the foundational one and the multiplicative statement is transported
  from it through `Additive`. `to_additive` cannot relate them — it would have to translate the
  `ℤ`-module argument itself — so the pair is written out by hand.
* `Group.fg_of_fg_ker_of_fg_range`: an extension of finitely generated groups is finitely
  generated — if the kernel and the range of `φ : G →* H` are finitely generated then so is `G`,
  the generators being preimages of generators of the range together with generators of the
  kernel. This one needs no commutativity and *is* `@[to_additive]`, giving
  `AddGroup.fg_of_fg_ker_of_fg_range`.

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

/-- A subgroup of a finitely generated additive commutative group is finitely generated, as `ℤ`
is a Noetherian ring: `G` is then a finitely generated `ℤ`-module, hence Noetherian, so the
submodule corresponding to `H` is finitely generated.

This is the foundational form — the argument is about `ℤ`-modules, so it is naturally additive —
and `Subgroup.fg_of_commGroup` is transported from it. An instance, matching how Mathlib
states its other `FG` closure properties (`Group.fg_range`, `QuotientGroup.fg`). -/
instance (priority := 100) AddSubgroup.fg_of_addCommGroup {G : Type*} [AddCommGroup G]
    [AddGroup.FG G] (H : AddSubgroup G) : AddGroup.FG H :=
  Module.Finite.iff_addGroup_fg.mp <| Module.Finite.iff_fg.mpr <|
    IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule H)

/-- A subgroup of a finitely generated commutative group is finitely generated: the additive
statement `AddSubgroup.fg_of_addCommGroup` transported through `Additive G`. -/
instance (priority := 100) Subgroup.fg_of_commGroup {G : Type*} [CommGroup G] [Group.FG G]
    (H : Subgroup G) : Group.FG H :=
  have : AddGroup.FG (Additive G) := AddGroup.fg_iff_mul_fg.mpr ‹_›
  (Group.fg_iff_subgroup_fg H).mpr <| (Subgroup.fg_iff_add_fg H).mpr <|
    (AddGroup.fg_iff_addSubgroup_fg (Subgroup.toAddSubgroup H)).mp inferInstance

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
