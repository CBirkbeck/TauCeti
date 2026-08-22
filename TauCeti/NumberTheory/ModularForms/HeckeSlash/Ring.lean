/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma1
public import TauCeti.NumberTheory.HeckeRing.Associativity

/-!
# The Hecke ring acting on modular forms

`heckeSlashGamma1ModularFormEnd` attaches a `ℂ`-linear endomorphism of `M_k(Γ₁(N))` to a single
double coset. This file extends that assignment `ℤ`-linearly to the whole Hecke ring
`𝕋 Δ₀(N) Γ₁(N) ℤ`, so that the abstract ring acts on the space of modular forms.

The extension is additive in the ring element, which is packaged as `heckeSlashGamma1RingHom`.
Multiplicativity — Shimura's Proposition 3.37, the identification of the convolution structure
constants with the reindexing of an iterated slash sum — is *not* proved here, so this is
deliberately an `AddMonoidHom` and not yet the roadmap's `RingHom`.

## Main definitions

* `heckeSlashGamma1RingEnd`: the `Finsupp.sum` extension of `heckeSlashGamma1ModularFormEnd`.
* `heckeSlashGamma1RingHom`: the same map bundled as an additive monoid homomorphism.

## Main results

* `heckeSlashGamma1RingEnd_zero`, `heckeSlashGamma1RingEnd_single`,
  `heckeSlashGamma1RingEnd_add`, `heckeSlashGamma1RingEnd_one`: the computation rules, giving
  the value on `0`, on a basis element, on a sum, and on the ring identity.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn
open scoped MatrixGroups ModularForm HeckeCosetModule

namespace HeckeRing.GL2

@[expose] public section

variable {N : ℕ} [NeZero N] (k : ℤ)

/-- **The Hecke ring acting on modular forms**: the `ℤ`-linear extension of
`heckeSlashGamma1ModularFormEnd` from a single double coset to a formal `ℤ`-combination of
them. -/
noncomputable def heckeSlashGamma1RingEnd
    (T : 𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ) :
    Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  T.sum fun D c ↦ c • heckeSlashGamma1ModularFormEnd k D

@[simp] lemma heckeSlashGamma1RingEnd_zero :
    heckeSlashGamma1RingEnd (N := N) k 0 = 0 :=
  Finsupp.sum_zero_index

/-- The action on a basis element is the scaled operator of that double coset. -/
@[simp] lemma heckeSlashGamma1RingEnd_single
    (D : HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)))
    (c : ℤ) :
    heckeSlashGamma1RingEnd (N := N) k (HeckeCosetModule.single ℤ D c) =
      c • heckeSlashGamma1ModularFormEnd k D :=
  HeckeCosetModule.sum_single_index ℤ (by simp)

/-- The action is additive in the ring element. -/
@[simp] lemma heckeSlashGamma1RingEnd_add
    (T₁ T₂ : 𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ) :
    heckeSlashGamma1RingEnd (N := N) k (T₁ + T₂) =
      heckeSlashGamma1RingEnd (N := N) k T₁ + heckeSlashGamma1RingEnd (N := N) k T₂ :=
  Finsupp.sum_add_index' (by simp) (by intro a b₁ b₂; rw [add_smul])

/-- The identity of the Hecke ring acts by the operator of the identity double coset. -/
@[simp] lemma heckeSlashGamma1RingEnd_one :
    heckeSlashGamma1RingEnd (N := N) k 1 =
      heckeSlashGamma1ModularFormEnd k (1 : HeckeCoset (Delta0 N)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))) := by
  change heckeSlashGamma1RingEnd (N := N) k (HeckeCosetModule.single ℤ 1 1) = _
  rw [heckeSlashGamma1RingEnd_single]
  norm_num

/-- **The additive action of the Hecke ring on modular forms.** Multiplicativity is Shimura's
Proposition 3.37 and is not available yet, so the ring acts additively here rather than by the
`RingHom` the theory ultimately wants. -/
noncomputable def heckeSlashGamma1RingHom :
    𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ →+
      Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := heckeSlashGamma1RingEnd k
  map_zero' := heckeSlashGamma1RingEnd_zero k
  map_add' := heckeSlashGamma1RingEnd_add k

@[simp] lemma heckeSlashGamma1RingHom_apply
    (T : 𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ) :
    heckeSlashGamma1RingHom (N := N) k T = heckeSlashGamma1RingEnd (N := N) k T := (rfl)

end

end HeckeRing.GL2
