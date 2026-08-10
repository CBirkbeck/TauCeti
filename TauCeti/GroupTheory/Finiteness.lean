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
# Closure properties of finitely generated groups

Mathlib has a substantial theory of finitely generated commutative groups in
`Mathlib/GroupTheory/FiniteAbelian/Basic.lean` — the structure theorem, `finite_of_fg_isMulTorsion`,
and `Subgroup.finiteIndex_range_powMonoidHom_of_fg`, which is the finiteness of `G ⧸ Gⁿ`. Three
closure properties it does not carry are collected here.

## Main results

* `AddSubgroup.fg_of_addCommGroup` and `Subgroup.fg_of_commGroup`: a subgroup of a finitely
  generated commutative group is finitely generated. The argument is Noetherianity of `ℤ`, so the
  *additive* statement is the foundational one and the multiplicative statement is transported
  from it through `Additive`; `to_additive` cannot relate them — it would have to translate the
  `ℤ`-module argument itself — so the pair is written out by hand and registered with
  `to_additive existing`. Both are `instance`s, matching how Mathlib states its other `FG` closure
  properties (`Group.fg_range`, `QuotientGroup.fg`, `Subgroup.fg_of_index_ne_zero`).
* `Group.fg_of_fg_ker_of_fg_range`: an extension of finitely generated groups is finitely
  generated — if the kernel and the range of `φ : G →* H` are finitely generated then so is `G`.
  This needs no commutativity and *is* `@[to_additive]`. It is a plain theorem rather than an
  instance, because `φ` is an explicit argument that typeclass resolution cannot infer.
* `Subgroup.fg_of_fg_map_of_fg_inf_ker`: the relativization of the previous result to an arbitrary
  subgroup `K`, of which it is the `K = ⊤` case. This is the `Subgroup` analogue of Mathlib's
  `Submodule.fg_of_fg_map_of_fg_inf_ker`, an absence Mathlib records explicitly — a comment in
  `Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean` restructures a proof "due to no
  `Subgroup` version of `Submodule.fg_of_fg_map_of_fg_inf_ker` existing". Also `@[to_additive]`.

Both are steps towards the `S`-unit group being finitely generated, which
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 names as an input to the weak Mordell–Weil
theorem: the group of `S`-units sits in an extension whose kernel is the unit group of the base
and whose range is a subgroup of a free group of rank `|S|`, so establishing finite generation
needs exactly these two facts. The finiteness that the descent then applies to it is Mathlib's
`Subgroup.finiteIndex_range_powMonoidHom_of_fg`, read through
`Subgroup.finiteIndex_iff_finite_quotient`; nothing here reproves it.

`AddSubgroup.fg_of_addCommGroup`, `Subgroup.fg_of_commGroup` and `Group.fg_of_fg_ker_of_fg_range`
are adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll). Following this repository's convention
for adapted material, the upstream authorship is credited here rather than in the copyright header.

**`Subgroup.fg_of_fg_map_of_fg_inf_ker` is new here**, with no counterpart in that source: it is
the relativization of the extension lemma, and Mathlib records its absence in the comment at
`Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean` quoted above.

That source file also carries `finite_modPow`, `finite_of_fg_of_pow_eq_one` and two `ℤ`-module
translation helpers. **None of them is ported: all four are now in Mathlib** — as
`Subgroup.finiteIndex_range_powMonoidHom_of_fg`, `CommGroup.finite_of_fg_isMulTorsion`, the
instance `AddMonoid.FG.to_moduleFinite_int`, and `Module.Finite.iff_addGroup_fg` composed with
`AddGroup.fg_iff_mul_fg`. The source predates those additions, some of which its own author
upstreamed, so check Mathlib again before porting anything further from it.

**Concurrent work upstream.** The open Mathlib pull request
[mathlib4#40791](https://github.com/leanprover-community/mathlib4/pull/40791) ("dirichlet's s-unit
theorem", by `vvvv-ops`, open since 2026-06-19) carries two of the results here as file-local
helpers of `Mathlib/RingTheory/DedekindDomain/SUnit.lean`, under different names:
`Subgroup.fg_of_commGroup` as `Subgroup.fg_of_fg_commGroup`, and
`Group.fg_of_fg_ker_of_fg_range` as `CommGroup.fg_of_fg_ker_of_fg_range` — the latter
`CommGroup`-only, where the version here needs no commutativity. On a bump that lands #40791, drop
`Subgroup.fg_of_commGroup` in favour of upstream's; the extension lemma here is strictly more
general, and `Subgroup.fg_of_fg_map_of_fg_inf_ker` has no counterpart there at all.
-/

public section

/-- **A subgroup of a finitely generated additive commutative group is finitely generated.** The
additive form of `Subgroup.fg_of_commGroup`. -/
-- `ℤ` is Noetherian, so `G` is a finitely generated `ℤ`-module and hence Noetherian, and the
-- submodule corresponding to `H` is finitely generated. The argument is about `ℤ`-modules, which
-- is why this additive form is the one proved directly.
instance (priority := 100) AddSubgroup.fg_of_addCommGroup {G : Type*} [AddCommGroup G]
    [AddGroup.FG G] (H : AddSubgroup G) : AddGroup.FG H :=
  (AddGroup.fg_iff_addSubgroup_fg H).mpr <| H.toIntSubmodule_toAddSubgroup ▸
    (Submodule.fg_iff_addSubgroup_fg _).mp (IsNoetherian.noetherian (R := ℤ) H.toIntSubmodule)

/-- **A subgroup of a finitely generated commutative group is finitely generated.** The
multiplicative form of `AddSubgroup.fg_of_addCommGroup`. -/
-- Transported through `Additive G`. `to_additive` cannot relate the two — it would have to
-- translate the `ℤ`-module argument itself — so the pair is written out by hand and registered
-- with `to_additive existing`, which puts it in the dictionary so downstream `@[to_additive]`
-- proofs using either can translate.
@[to_additive existing]
instance (priority := 100) Subgroup.fg_of_commGroup {G : Type*} [CommGroup G] [Group.FG G]
    (H : Subgroup G) : Group.FG H :=
  -- `AddGroup.FG (Additive G)` is Mathlib's instance `AddGroup.fg_of_group_fg`, found by search
  (Group.fg_iff_subgroup_fg H).mpr <| (Subgroup.fg_iff_add_fg H).mpr <|
    (AddGroup.fg_iff_addSubgroup_fg (Subgroup.toAddSubgroup H)).mp inferInstance

/-- **An extension of finitely generated groups is finitely generated:** if the kernel and the
range of `φ : G →* H` are finitely generated, then so is `G`. This is the `K = ⊤` case of
`Subgroup.fg_of_fg_map_of_fg_inf_ker`. -/
-- The generators are preimages of generators of the range together with generators of the kernel.
@[to_additive /-- **An extension of finitely generated additive groups is finitely generated:** if
the kernel and the range of `φ : G →+ H` are finitely generated, then so is `G`. This is the
`K = ⊤` case of `AddSubgroup.fg_of_fg_map_of_fg_inf_ker`. -/]
theorem Group.fg_of_fg_ker_of_fg_range {G H : Type*} [Group G] [Group H] (φ : G →* H)
    [Group.FG φ.ker] [Group.FG φ.range] : Group.FG G := by
  obtain ⟨T, hT, hTfin⟩ := Group.fg_iff.mp ‹Group.FG φ.range›
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp ‹Group.FG φ.ker›
  set σ : φ.range → G := Function.surjInv φ.rangeRestrict_surjective
  set U : Set G := σ '' T ∪ (φ.ker.subtype '' S)
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

/-- **A subgroup whose image and whose intersection with the kernel are finitely generated is
itself finitely generated.** The `Subgroup` analogue of Mathlib's
`Submodule.fg_of_fg_map_of_fg_inf_ker`, whose absence Mathlib records explicitly: a comment in
`Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean` restructures a proof "due to no
`Subgroup` version of `Submodule.fg_of_fg_map_of_fg_inf_ker` existing".

It is the relativization of `Group.fg_of_fg_ker_of_fg_range`, which is its `K = ⊤` case. -/
@[to_additive /-- **An additive subgroup whose image and whose intersection with the kernel are
finitely generated is itself finitely generated.** The `AddSubgroup` analogue of Mathlib's
`Submodule.fg_of_fg_map_of_fg_inf_ker`. -/]
theorem Subgroup.fg_of_fg_map_of_fg_inf_ker {G H : Type*} [Group G] [Group H] (φ : G →* H)
    {K : Subgroup G} (h₁ : (K.map φ).FG) (h₂ : (K ⊓ φ.ker).FG) : K.FG := by
  have : Group.FG (φ.domRestrict K).ker := by
    have : Group.FG (K ⊓ φ.ker : Subgroup G) := (Group.fg_iff_subgroup_fg _).mpr h₂
    rw [MonoidHom.ker_domRestrict, ← Subgroup.inf_subgroupOf_left]
    have e := (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ φ.ker ≤ K)).symm
    exact Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  have : Group.FG (φ.domRestrict K).range := by
    rw [MonoidHom.domRestrict_range]; exact (Group.fg_iff_subgroup_fg _).mpr h₁
  exact (Group.fg_iff_subgroup_fg K).mp (Group.fg_of_fg_ker_of_fg_range (φ.domRestrict K))

end
