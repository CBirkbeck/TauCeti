/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma1
public import TauCeti.NumberTheory.HeckeRing.Associativity

/-!
# The Hecke ring acting on cusp forms

`heckeSlashGamma1CuspFormEnd` attaches a `ℂ`-linear endomorphism of `S_k(Γ₁(N))` to a single
double coset. This file extends that assignment `ℤ`-linearly to the whole Hecke ring
`𝕋 Δ₀(N) Γ₁(N) ℤ`, so that the abstract ring acts on the space of cusp forms.

The extension is additive in the ring element, which is packaged as
`heckeSlashGamma1CuspRingHom`. Multiplicativity — Shimura's Proposition 3.37 — is *not* proved
here, so this is deliberately an `AddMonoidHom` and not yet a `RingHom`.

## Main definitions

* `heckeSlashGamma1CuspRingEnd`: the `Finsupp.sum` extension of `heckeSlashGamma1CuspFormEnd`.
* `heckeSlashGamma1CuspRingHom`: the same map bundled as an additive monoid homomorphism.

## Main results

* `heckeSlashGamma1CuspRingEnd_zero`, `heckeSlashGamma1CuspRingEnd_single`,
  `heckeSlashGamma1CuspRingEnd_add`, `heckeSlashGamma1CuspRingEnd_one`: the computation rules,
  giving the value on `0`, on a basis element, on a sum, and on the ring identity.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn
open scoped MatrixGroups ModularForm HeckeCosetModule

namespace HeckeRing.GL2

@[expose] public section

variable {N : ℕ} [NeZero N] (k : ℤ)

/-- **The Hecke ring acting on cusp forms**: the `ℤ`-linear extension of
`heckeSlashGamma1CuspFormEnd` from a single double coset to a formal `ℤ`-combination of
them. -/
noncomputable def heckeSlashGamma1CuspRingEnd
    (T : 𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ) :
    Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  T.sum fun D c ↦ c • heckeSlashGamma1CuspFormEnd k D

@[simp] lemma heckeSlashGamma1CuspRingEnd_zero :
    heckeSlashGamma1CuspRingEnd (N := N) k 0 = 0 :=
  Finsupp.sum_zero_index

/-- The action on a basis element is the scaled operator of that double coset. -/
@[simp] lemma heckeSlashGamma1CuspRingEnd_single
    (D : HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)))
    (c : ℤ) :
    heckeSlashGamma1CuspRingEnd (N := N) k (HeckeCosetModule.single ℤ D c) =
      c • heckeSlashGamma1CuspFormEnd k D :=
  HeckeCosetModule.sum_single_index ℤ (by simp)

/-- The action is additive in the ring element. -/
@[simp] lemma heckeSlashGamma1CuspRingEnd_add
    (T₁ T₂ : 𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ) :
    heckeSlashGamma1CuspRingEnd (N := N) k (T₁ + T₂) =
      heckeSlashGamma1CuspRingEnd (N := N) k T₁ + heckeSlashGamma1CuspRingEnd (N := N) k T₂ :=
  Finsupp.sum_add_index' (by simp) (by intro a b₁ b₂; rw [add_smul])

/-- The identity of the Hecke ring acts by the operator of the identity double coset. -/
@[simp] lemma heckeSlashGamma1CuspRingEnd_one :
    heckeSlashGamma1CuspRingEnd (N := N) k 1 =
      heckeSlashGamma1CuspFormEnd k (1 : HeckeCoset (Delta0 N)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))) := by
  change heckeSlashGamma1CuspRingEnd (N := N) k (HeckeCosetModule.single ℤ 1 1) = _
  rw [heckeSlashGamma1CuspRingEnd_single]
  norm_num

/-- **The additive action of the Hecke ring on cusp forms.** Multiplicativity is Shimura's
Proposition 3.37 and is not available yet, so the ring acts additively here rather than by a
`RingHom`. -/
noncomputable def heckeSlashGamma1CuspRingHom :
    𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ →+
      Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := heckeSlashGamma1CuspRingEnd k
  map_zero' := heckeSlashGamma1CuspRingEnd_zero k
  map_add' := heckeSlashGamma1CuspRingEnd_add k

@[simp] lemma heckeSlashGamma1CuspRingHom_apply
    (T : 𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ) :
    heckeSlashGamma1CuspRingHom (N := N) k T = heckeSlashGamma1CuspRingEnd (N := N) k T := (rfl)

end

end HeckeRing.GL2
