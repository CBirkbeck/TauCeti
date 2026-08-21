/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma1
public import TauCeti.NumberTheory.HeckeRing.Associativity

/-!
# The Hecke ring acting on functions by slash sums

`heckeSlashSum` attaches an operator on `ℍ → ℂ` to a single double coset. This file extends
that assignment `ℤ`-linearly to the whole Hecke ring `𝕋 Δ Γ ℤ`, giving the action through
which the abstract ring acts on spaces of modular forms.

## Main definitions

* `heckeSlashSumRing`: the `Finsupp.sum` extension of `heckeSlashSum` to `𝕋 Δ Γ ℤ`.

## Main results

* `heckeSlashSumRing_zero`, `heckeSlashSumRing_single`, `heckeSlashSumRing_add`,
  `heckeSlashSumRing_one`: the computation rules, giving the value on `0`, on a basis
  element, on a sum, and on the ring identity.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn
open scoped MatrixGroups ModularForm HeckeCosetModule

namespace HeckeRing.GL2

@[expose] public section

variable {G : Type*} [Group G] {Δ : Submonoid G} {Γ : Subgroup G}

/-- **The Hecke ring acting by slash sums**: the `ℤ`-linear extension of `heckeSlashSum` from a
single double coset to a formal `ℤ`-combination of them. -/
noncomputable def heckeSlashSumRing {N : ℕ} [NeZero N] (k : ℤ)
    (T : 𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  T.sum fun D c ↦ (c : ℂ) • heckeSlashSum k D f

@[simp] lemma heckeSlashSumRing_zero {N : ℕ} [NeZero N] (k : ℤ) (f : ℍ → ℂ) :
    heckeSlashSumRing (N := N) k 0 f = 0 :=
  Finsupp.sum_zero_index

/-- The action on a basis element is the scaled slash sum of that double coset. -/
@[simp] lemma heckeSlashSumRing_single {N : ℕ} [NeZero N] (k : ℤ)
    (D : HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)))
    (c : ℤ) (f : ℍ → ℂ) :
    heckeSlashSumRing (N := N) k (HeckeCosetModule.single ℤ D c) f =
      (c : ℂ) • heckeSlashSum k D f :=
  HeckeCosetModule.sum_single_index ℤ (by simp)

/-- The action is additive in the ring element. -/
@[simp] lemma heckeSlashSumRing_add {N : ℕ} [NeZero N] (k : ℤ)
    (T₁ T₂ : 𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ) (f : ℍ → ℂ) :
    heckeSlashSumRing (N := N) k (T₁ + T₂) f =
      heckeSlashSumRing (N := N) k T₁ f + heckeSlashSumRing (N := N) k T₂ f :=
  Finsupp.sum_add_index' (by simp) (by intro a b₁ b₂; push_cast; rw [add_smul])

/-- The identity of the Hecke ring acts by the slash sum of the identity double coset. -/
@[simp] lemma heckeSlashSumRing_one {N : ℕ} [NeZero N] (k : ℤ) (f : ℍ → ℂ) :
    heckeSlashSumRing (N := N) k 1 f =
      heckeSlashSum k (1 : HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ))
        ((Gamma1 N).map (mapGL ℚ))) f := by
  change heckeSlashSumRing (N := N) k (HeckeCosetModule.single ℤ 1 1) f = _
  rw [heckeSlashSumRing_single]
  norm_num

end

end HeckeRing.GL2
