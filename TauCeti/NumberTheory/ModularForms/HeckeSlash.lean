/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.TransposeAntiInvolution
public import TauCeti.NumberTheory.HeckeRing.LeftCosetModule.Basic
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# The slash action of a double coset

A Hecke operator acts on a function `f : ℍ → ℂ` by slashing it against representatives of the
double coset and summing. This file defines that sum and records that it is `ℂ`-linear in `f`.

## The transpose, and why it is here

The Hecke ring is built from the decomposition of `HδH` into **right** cosets `σᵢδH`
(`DoubleCoset.DecompQuotient`), but the slash action is a right action, so a sum over right
cosets is not slash-invariant. Shimura's Prop 3.30 sums instead over **left** coset
representatives, and the two are exchanged by transposition: if `HδH = ⊔ᵢ (σᵢδ)H` then
`HδH = ⊔ᵢ H(δᵀσᵢᵀ)`, because transposition is an anti-automorphism preserving `SL₂(ℤ)` and
fixing every double coset. So the representative used here is `(σᵢδ)ᵀ`, which is `tRep`.

Transposition is available as the anti-involution of `GLn/TransposeAntiInvolution.lean`, the
same one that proves the Hecke ring commutative; this file only needs that it preserves
`SL_n(ℤ)` and `Δ`.

## Positive determinants throughout

Every representative lies in `Δ = posDetInt 2`, so its determinant is positive, and that is what
makes the sum `ℂ`-linear: on the positive branch the slash action's conjugation `σ` is trivial
and scalars commute past it (`ModularForm.rat_smul_slash_of_det_pos`). Over a general
`GL(2, ℚ)`-element the twist is complex conjugation and linearity would fail.

## Main definitions

* `HeckeRing.GL2.tRep`: the transposed representative `(σᵢ δ)ᵀ`.
* `HeckeRing.GL2.heckeSlash`: `T_k(D) f = ∑ᵢ f ∣[k] (σᵢ δ)ᵀ`.

## Main results

* `HeckeRing.GL2.det_tRep_pos`: the representatives have positive determinant.
* `HeckeRing.GL2.heckeSlash_add`, `heckeSlash_zero`, `heckeSlash_smul`: `ℂ`-linearity.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck): `tRep`,
`heckeSlash` and the `heckeSlash_add` / `heckeSlash_zero` / `heckeSlash_smul` group. Restated
against TauCeti's `SLnZ`/`posDetInt` Hecke pair and `transposeGLEquiv` rather than AINTLIB's
`GL_pair`/`GL_transposeEquiv`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4, Proposition 3.30.
-/

public section

open Matrix UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

/-- The transposed right-coset representative `(σᵢ δ)ᵀ = δᵀ σᵢᵀ`, where `δ` is the chosen
representative of the double coset `D` and `σᵢ` runs over its right-coset decomposition. -/
noncomputable def tRep (i : DecompQuotient (SLnZ 2) (SLnZ 2) ((D.out : GL (Fin 2) ℚ))) :
    GL (Fin 2) ℚ :=
  (transposeGLEquiv 2 ((i.out : GL (Fin 2) ℚ) * (D.out : GL (Fin 2) ℚ))).unop

/-- Each representative lies in `Δ`: `σᵢ ∈ SL₂(ℤ) ≤ Δ`, `δ ∈ Δ`, and transposition preserves
`Δ`. -/
lemma tRep_mem_posDetInt (i : DecompQuotient (SLnZ 2) (SLnZ 2) ((D.out : GL (Fin 2) ℚ))) :
    tRep D i ∈ posDetInt 2 :=
  transposeGLEquiv_mem_posDetInt 2
    ((posDetInt 2).mul_mem (SLnZ_le_posDetInt 2 i.out.2) (D.out).2)

/-- The representatives have positive determinant — the hypothesis every slash lemma below
needs. -/
lemma det_tRep_pos (i : DecompQuotient (SLnZ 2) (SLnZ 2) ((D.out : GL (Fin 2) ℚ))) :
    0 < (tRep D i : Matrix (Fin 2) (Fin 2) ℚ).det :=
  ((mem_posDetInt_iff 2).mp (tRep_mem_posDetInt D i)).2

/-- **The slash action of a double coset**: `T_k(D) f = ∑ᵢ f ∣[k] (σᵢ δ)ᵀ`, the sum over the
transposed representatives of the right-coset decomposition of `HδH` (Shimura Prop 3.30). -/
noncomputable def heckeSlash (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : DecompQuotient (SLnZ 2) (SLnZ 2) ((D.out : GL (Fin 2) ℚ)), f ∣[k] tRep D i

/-- Defining equation for `heckeSlash`. -/
lemma heckeSlash_def (f : ℍ → ℂ) :
    heckeSlash k D f =
      ∑ i : DecompQuotient (SLnZ 2) (SLnZ 2) ((D.out : GL (Fin 2) ℚ)), f ∣[k] tRep D i := (rfl)

/-- The slash action of a double coset is additive. -/
lemma heckeSlash_add (f g : ℍ → ℂ) :
    heckeSlash k D (f + g) = heckeSlash k D f + heckeSlash k D g := by
  simp [heckeSlash, Finset.sum_add_distrib]

/-- The slash action of a double coset kills the zero function. -/
@[simp]
lemma heckeSlash_zero : heckeSlash k D 0 = 0 := by
  simp [heckeSlash]

/-- **The slash action of a double coset is `ℂ`-linear.** Each summand has positive
determinant, so `ModularForm.rat_smul_slash_of_det_pos` applies and the scalar passes through
with no `σ` twist. -/
lemma heckeSlash_smul {α : Type*} [DistribSMul α ℂ] [IsScalarTower α ℂ ℂ] (c : α)
    (f : ℍ → ℂ) : heckeSlash k D (c • f) = c • heckeSlash k D f := by
  rw [heckeSlash_def, heckeSlash_def, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    ModularForm.rat_smul_slash_of_det_pos k (det_tRep_pos D i) f c

end HeckeRing.GL2
