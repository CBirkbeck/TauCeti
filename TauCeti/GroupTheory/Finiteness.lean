/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Finitely generated commutative groups

Mathlib knows that a finitely generated commutative group is a finitely generated `ℤ`-module
(`Module.Finite.iff_addGroup_fg`) and has the structure theory of modules over a PID, but it does
not carry the three closure properties that a descent argument needs. This file supplies them:

## Main results

* `Subgroup.fg_of_commGroup_fg`: a subgroup of a finitely generated commutative group is finitely
  generated. This is Noetherianity of `ℤ` transported through `Additive`.
* `Group.fg_of_fg_ker_of_fg_range`: an extension of finitely generated groups is finitely
  generated — if the kernel and the range of `φ : G →* H` are finitely generated then so is `G`.
  Unlike the previous one this needs no commutativity, and it is `@[to_additive]`.
* `CommGroup.finite_modPow`: **the group of `n`-th power classes of a finitely generated
  commutative group is finite**, i.e. `G ⧸ Gⁿ` is finite.

`CommGroup.finite_modPow` is the group-theoretic heart of the weak Mordell–Weil theorem: with
`G = E(K)` and `n = 2` it is the statement `E(K)/2E(K)` finite that
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 asks for, once the Kummer argument has bounded
`E(K)/2E(K)` inside a group known to be finitely generated. The other two are what make the
`S`-unit group finitely generated, the second input that argument needs; the `S`-class group, the
first, is `IsDedekindDomain.integerClassGroupEquiv`.

Three supporting results are exported alongside them. `Module.finite_int_additive` and
`Group.fg_of_module_finite_int` are the two directions of the translation between "finitely
generated as a group" and "finitely generated as a `ℤ`-module"; they are stated separately
because the proofs below pass through `Additive G` in both directions and Mathlib's
`Module.Finite.iff_addGroup_fg` is phrased for an `AddCommGroup`.
`CommGroup.finite_of_fg_of_pow_eq_one` — a finitely generated commutative group of finite
exponent is finite — is the step that makes `CommGroup.finite_modPow` work, and is the form to
use when the exponent bound is already in hand rather than obtained from a quotient.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` lines
99–170 at the roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll), the source the
roadmap's §Provenance names for the Layer 6 Mordell–Weil lane. Following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.

Note for a future Mathlib bump: that source is being upstreamed piecemeal by its author —
`Mathlib/GroupTheory/IndexNSmul.lean` at our pin is his — so check whether these have landed
before extending this file.
-/

public section

/-- A finitely generated commutative group is a finitely generated `ℤ`-module. -/
theorem Module.finite_int_additive (G : Type*) [CommGroup G] [Group.FG G] :
    Module.Finite ℤ (Additive G) :=
  Module.Finite.iff_addGroup_fg.mpr (AddGroup.fg_iff_mul_fg.mpr ‹_›)

/-- A commutative group that is finitely generated as a `ℤ`-module is finitely generated as a
group; the converse direction of `Module.finite_int_additive`. -/
theorem Group.fg_of_module_finite_int {G : Type*} [CommGroup G]
    (h : Module.Finite ℤ (Additive G)) : Group.FG G :=
  AddGroup.fg_iff_mul_fg.mp (Module.Finite.iff_addGroup_fg.mp h)

/-- A subgroup of a finitely generated commutative group is finitely generated, as `ℤ` is a
Noetherian ring. (The proof passes through `Additive G`, so `to_additive` cannot translate it; an
additive version would have to be stated by hand.) -/
theorem Subgroup.fg_of_commGroup_fg {G : Type*} [CommGroup G] [Group.FG G] (H : Subgroup G) :
    Group.FG H :=
  have : Module.Finite ℤ (Additive G) := Module.finite_int_additive G
  Group.fg_of_module_finite_int <| Module.Finite.iff_fg.mpr <|
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

/-- A finitely generated commutative group of finite exponent is finite. -/
theorem CommGroup.finite_of_fg_of_pow_eq_one {G : Type*} [CommGroup G] [Group.FG G] (n : ℕ)
    [NeZero n] (hn : ∀ x : G, x ^ n = 1) : Finite G := by
  -- bounded exponent makes `G` a module over `ZMod n`, and a finite ring with a finitely
  -- generated module over it has a finite module
  let _ : Module (ZMod n) (Additive G) := AddCommGroup.zmodModule (n := n) hn
  have h₁ : Module.Finite ℤ (Additive G) :=
    Module.Finite.iff_addGroup_fg.mpr (by rwa [AddGroup.fg_iff_mul_fg])
  have h₂ : Module.Finite (ZMod n) (Additive G) :=
    Module.Finite.of_restrictScalars_finite ℤ (ZMod n) (Additive G)
  have := Module.finite_of_finite (ZMod n) (M := Additive G)
  exact Finite.of_equiv _ (Additive.toMul (α := G))

/-- **The group of `n`-th power classes of a finitely generated commutative group is finite.**
With `G = E(K)` and `n = 2` this is the finiteness of `E(K)/2E(K)` that weak Mordell–Weil
asserts. -/
theorem CommGroup.finite_modPow {G : Type*} [CommGroup G] [Group.FG G] (n : ℕ) [NeZero n] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) := by
  have : Group.FG (G ⧸ (powMonoidHom n : G →* G).range) :=
    Group.fg_of_surjective (QuotientGroup.mk'_surjective _)
  refine finite_of_fg_of_pow_eq_one n fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | H g => exact (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩

end
