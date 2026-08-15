/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Consequences of the index formula

The preimage `H.comap f` of a finite-index subgroup along a group homomorphism again has finite
index: its index is the relative index of `H` in the range of `f`, which is finite. Adjoining
the centre to a finite-index subgroup also keeps the index finite, since it only enlarges the
subgroup.

Because the order of a subgroup divides the order of the group -- with the index as cofactor --
invertibility of the order of a finite group in a semiring passes to every subgroup.

Adjoining the centre is also quantified: when the centre is `{1, a}` with `a ∉ Γ`, the subgroup
`Γ` has relative index exactly `2` in `Γ.withCenter`, so `Γ.index = 2 * Γ.withCenter.index`.

## Main results

* `Subgroup.relIndex_withCenter_eq_two`, `Subgroup.index_eq_two_mul_index_withCenter`: the
  relative index `2` and the index doubling, for a two-element centre not contained in `Γ`.
-/

public section

namespace Subgroup

/-- The preimage of a finite-index subgroup under a group homomorphism has finite index. -/
@[to_additive]
instance instFiniteIndexComap {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) [H.FiniteIndex]
    (f : G' →* G) : (H.comap f).FiniteIndex :=
  ⟨by rw [index_comap]; exact FiniteIndex.index_ne_zero⟩

/-- `Γ` with the centre of the ambient group adjoined. For `Γ ≤ SL(2, ℤ)` the centre is
`{±I}`, which acts trivially on `ℍ`; it is the cosets of `Γ·{±I}` — not those of `Γ` itself —
that name the distinct translates of `𝒟` tiling a `Γ` fundamental domain, since `q` and `-q`
would otherwise be counted as two cosets carrying the same translate. The two subgroups agree
exactly when `-I ∈ Γ`. -/
def withCenter {G : Type*} [Group G] (Γ : Subgroup G) : Subgroup G :=
  Γ ⊔ Subgroup.center G

/-- Unfolding: `Γ.withCenter` is the supremum of `Γ` with the centre. -/
theorem withCenter_def {G : Type*} [Group G] (Γ : Subgroup G) :
    Γ.withCenter = Γ ⊔ Subgroup.center G := (rfl)

/-- `Γ` sits inside `Γ` with the centre adjoined. -/
lemma le_withCenter {G : Type*} [Group G] (Γ : Subgroup G) : Γ ≤ Γ.withCenter :=
  le_sup_left

instance instFiniteIndexWithCenter {G : Type*} [Group G] (Γ : Subgroup G)
    [Γ.FiniteIndex] : Γ.withCenter.FiniteIndex :=
  Subgroup.finiteIndex_of_le Γ.le_withCenter

variable {G : Type*} [Group G] {Γ : Subgroup G} {a : G}

/-- **When the centre is `{1, a}` and `a ∉ Γ`, `Γ` has relative index exactly `2` in
`Γ.withCenter`.** Only this branch is proved here; the complementary `a ∈ Γ` case, in which the
two subgroups coincide, is an unformalised remark.

For `Γ ≤ SL(2, ℤ)` the centre is `{±I}` and `a = -I`, so this is the quantitative form of the
dichotomy recorded on `Subgroup.withCenter`: cosets of `Γ` count each translate of `𝒟` twice
unless `-I ∈ Γ` already.

`a` is not assumed to be an involution — that follows, since `a * a` lies in the centre and
`a * a = a` would force `a = 1 ∈ Γ`. -/
theorem relIndex_withCenter_eq_two (ha : a ∈ Subgroup.center G) (haΓ : a ∉ Γ)
    (hcenter : ∀ c ∈ Subgroup.center G, c = 1 ∨ c = a) : Γ.relIndex Γ.withCenter = 2 := by
  have ha2 : a * a = 1 := by
    rcases hcenter _ ((Subgroup.center G).mul_mem ha ha) with h | h
    · exact h
    · exact absurd (mul_eq_left.mp h ▸ Γ.one_mem) haΓ
  refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
    ⟨a, Subgroup.withCenter_def Γ ▸ Subgroup.mem_sup_right ha, haΓ, fun b hb ↦ ?_⟩
  -- `withCenter` is a supremum with a normal subgroup, so its elements factor as `g * c`
  obtain ⟨g, hg, c, hc, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right.mp (Subgroup.withCenter_def Γ ▸ hb)
  rcases hcenter c hc with rfl | rfl
  · exact Or.inr (by simpa using hg)
  · exact Or.inl (by simpa [mul_assoc, ha2] using hg)

/-- **When the centre is `{1, a}` and `a ∉ Γ`, the index of `Γ` is twice that of
`Γ.withCenter`.** The counting form of
`Subgroup.relIndex_withCenter_eq_two`: it is `Γ.withCenter`, not `Γ`, whose cosets index the
distinct translates, so a count over `Γ`-cosets is twice the geometric one. -/
theorem index_eq_two_mul_index_withCenter (ha : a ∈ Subgroup.center G) (haΓ : a ∉ Γ)
    (hcenter : ∀ c ∈ Subgroup.center G, c = 1 ∨ c = a) : Γ.index = 2 * Γ.withCenter.index := by
  rw [← Subgroup.relIndex_mul_index Γ.le_withCenter, relIndex_withCenter_eq_two ha haΓ hcenter]

end Subgroup

namespace TauCeti

/-- If the order of a finite group is invertible in `k`, then so is the order of any subgroup,
because the two differ by the index. -/
theorem isUnit_natCard_subgroup {k : Type*} {G : Type*} [Semiring k] [Group G]
    (S : Subgroup G) (hG : IsUnit (Nat.card G : k)) : IsUnit (Nat.card S : k) := by
  have h : IsUnit ((Nat.card S : k) * (S.index : k)) := by
    rwa [← Nat.cast_mul, S.card_mul_index]
  exact ((Nat.cast_commute _ _).isUnit_mul_iff.mp h).1

end TauCeti
