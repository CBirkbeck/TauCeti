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

end

end HeckeRing.GL2
