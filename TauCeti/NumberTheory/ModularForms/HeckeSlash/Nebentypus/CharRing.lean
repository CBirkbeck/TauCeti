/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Composition

/-!
# The Hecke ring acts on the `χ`-invariant functions, multiplicatively on basis elements

`HeckeSlash/Nebentypus/Ring.lean` extends the twisted slash sum `ℤ`-linearly over the Hecke ring,
but on the wrong carrier: `twistedHeckeSlashRingLinearMap` lands in `Module.End ℂ (ℍ → ℂ)`, and
its docstring records that multiplicativity is not available there. `Nebentypus/Invariance.lean`
then supplies the missing ingredient — the twisted sum preserves `functionCharSpace`, so each
double coset restricts to `twistedHeckeSlashSumCharEnd` — and `Nebentypus/Composition.lean` proves
that *on that carrier* the per-coset operators multiply.

This file draws the consequence: the `ℤ`-linear extension is taken on the character space, and the
multiplicativity of `Nebentypus/Composition.lean` is read on the basis elements of the Hecke ring.

## Why the character space is the right carrier

Multiplicativity is false on `ℍ → ℂ`. The composite of two twisted sums collapses to the sum of a
single double coset only for a `χ`-eigenfunction — `twistedHeckeSlashSum_mem_functionCharSpace` is
what makes the inner sum eligible for the outer one — so the equation cannot be stated, let alone
proved, before the carrier is cut down. That is exactly the relation `functionCharSpace` names, and
it is why this file exists as the successor of `Nebentypus/Ring.lean` rather than as part of it:
`Nebentypus/Ring.lean` sits below `Nebentypus/Invariance.lean` in the import graph and cannot see
the restricted operator.

## The order is reversed, and that is not an accident

`Module.End` multiplies by composition while the slash acts on the right, so the basis element
`D₁` of the *left* factor becomes the operator applied *first*. On these elements the map is an
anti-homomorphism, not a homomorphism — the same order that
`heckeSlashGamma1RingModularFormLinearMap_mul_single_single` records for the untwisted `Γ₁(N)`
operators, of which this is the nebentypus-weighted counterpart.

## What is still absent

Full multiplicativity — Shimura's Proposition 3.37, and hence the ring homomorphism
`𝕋 Δ₀(N) Γ₀(N) ℤ →+* Module.End ℂ (functionCharSpace k χ)` — is *not* proved here. It needs the
structure constants of a product that spreads over several double cosets with multiplicity,
whereas the input available on `main`, `twistedHeckeSlashSumCharEnd_mul_of_doubleCoset_eq_mul`,
assumes the product collapses to a single coset `D₃` without right-coset collisions. What is below
is the part that follows from what is on hand, stated with those hypotheses carried explicitly.

## Main definitions

* `HeckeRing.GL2.twistedHeckeSlashRingCharLinearMap`: the `ℤ`-linear extension of
  `twistedHeckeSlashSumCharEnd` to the Hecke ring, valued in `Module.End ℂ (functionCharSpace k χ)`.

## Main results

* `HeckeRing.GL2.twistedHeckeSlashRingCharLinearMap_single`: the value on a basis element is the
  scaled twisted operator of that double coset. With `map_zero`/`map_add` this determines the map.
* `HeckeRing.GL2.twistedHeckeSlashRingCharLinearMap_mul_single_single`: **the Hecke ring acts
  multiplicatively on the character space**, where the product of two double cosets is again a
  single double coset.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`, Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`), whose
`twistedHeckeSumFunction` (line 842) is the extension below and whose `twistedHeckeSumFunction_mul`
(line 917) is its multiplicativity.

Two departures. The source states multiplicativity for arbitrary ring elements, reaching it
through its own fibre-counting chain (`gamma0_mulMap_eq_of_rightCoset` through
`twistedHeckeSlashGen_comp`, lines 601-801); that chain is not on `main`, so the statement here is
the basis-element form its generator-level input supports, carrying the collapse hypotheses. And
the names, the double-coset indexing and the `HeckeCosetModule.single` spelling are `main`'s, not
the source's; the statement shape is `main`'s own untwisted
`heckeSlashGamma1RingModularFormLinearMap_mul_single_single`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4 (the action of the Hecke ring on automorphic forms).
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn
open scoped MatrixGroups ModularForm Pointwise HeckeCosetModule

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) [NeZero N]

/-- The `ℤ`-linear extension of `twistedHeckeSlashSumCharEnd` to formal `ℤ`-combinations of double
cosets of `Γ₀(N)`, on the carrier the twisted sum actually preserves.

This is `twistedHeckeSlashRingLinearMap` with `Module.End ℂ (ℍ → ℂ)` replaced by
`Module.End ℂ (functionCharSpace k χ)`; the two are not interchangeable, since the
multiplicativity below is available only on the smaller carrier. -/
noncomputable def twistedHeckeSlashRingCharLinearMap :
    𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ →ₗ[ℤ] Module.End ℂ (functionCharSpace k χ) :=
  -- Eta-expanded for the same reason as `twistedHeckeSlashRingLinearMap`: `[NeZero N]` is
  -- introduced after the double coset, so the partial application still expects the instance.
  Finsupp.linearCombination ℤ fun D ↦ twistedHeckeSlashSumCharEnd k χ D

/-- The value on a basis element is the scaled twisted operator of that double coset. -/
@[simp] lemma twistedHeckeSlashRingCharLinearMap_single
    (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))) (c : ℤ) :
    twistedHeckeSlashRingCharLinearMap k χ (HeckeCosetModule.single ℤ D c) =
      c • twistedHeckeSlashSumCharEnd k χ D :=
  -- As in `twistedHeckeSlashRingLinearMap_single`: `Finsupp.linearCombination_single` does not
  -- apply, since `HeckeCosetModule.single` is a separate, non-exposed `def`.
  (Finsupp.linearCombination_apply (R := ℤ)
    (v := fun D ↦ twistedHeckeSlashSumCharEnd k χ D) _).trans
    (HeckeCosetModule.sum_single_index ℤ (zero_smul _ _))

section Free

variable (D₁ D₂ : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))
  {ι κ : Type*} (a : ι → GL (Fin 2) ℚ) (b : κ → GL (Fin 2) ℚ)
  (hcover₁ : doubleCoset (D₁.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
    ((Gamma0 N).map (mapGL ℚ)) =
    ⋃ i, MulOpposite.op (a i) • (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) :
      Set (GL (Fin 2) ℚ)))
  (hinj₁ : Function.Injective fun i ↦ MulOpposite.op (a i) •
    (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)))
  (hcover₂ : doubleCoset (D₂.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
    ((Gamma0 N).map (mapGL ℚ)) =
    ⋃ j, MulOpposite.op (b j) • (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) :
      Set (GL (Fin 2) ℚ)))
  (hinj₂ : Function.Injective fun j ↦ MulOpposite.op (b j) •
    (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)))
  [Finite ι] [Finite κ]
  (D₃ : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

include hcover₁ hinj₁ hcover₂ hinj₂ in
/-- **The Hecke ring acts multiplicatively on the character space**, where the product of two
double cosets is again a single double coset.

This is the ring-level reading of `twistedHeckeSlashSumCharEnd_mul_of_doubleCoset_eq_mul`: the two
criteria line up, one on each side, with `HeckeCosetModule.mul_single_single_of_mulMap_eq`
supplying the product in the Hecke ring and the composition theorem supplying it in `Module.End`.

Note the order — `D₁` sits on the left in the Hecke ring and acts second on the right-hand side;
see the module docstring. -/
theorem twistedHeckeSlashRingCharLinearMap_mul_single_single
    (hD₃ : doubleCoset (D₃.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) =
      doubleCoset (D₁.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
          ((Gamma0 N).map (mapGL ℚ)) *
        doubleCoset (D₂.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
          ((Gamma0 N).map (mapGL ℚ)))
    (hinj₃ : Function.Injective fun p : ι × κ ↦ MulOpposite.op (a p.1 * b p.2) •
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)))
    (hmulMap : ∀ p, HeckeCoset.mulMap ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) D₁.rep D₂.rep p = D₃)
    (hmul : multiplicity ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) (D₁.rep : GL (Fin 2) ℚ) (D₂.rep : GL (Fin 2) ℚ)
      (D₃.rep : GL (Fin 2) ℚ) ≤ 1) : twistedHeckeSlashRingCharLinearMap k χ
        (HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1) =
      twistedHeckeSlashRingCharLinearMap k χ (HeckeCosetModule.single ℤ D₂ 1) *
        twistedHeckeSlashRingCharLinearMap k χ (HeckeCosetModule.single ℤ D₁ 1) := by
  have hprod : HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1
      = HeckeCosetModule.single ℤ D₃ 1 :=
    HeckeCosetModule.mul_single_single_of_mulMap_eq ℤ D₁ D₂ D₃ hmulMap hmul
  rw [hprod, twistedHeckeSlashRingCharLinearMap_single, twistedHeckeSlashRingCharLinearMap_single,
    twistedHeckeSlashRingCharLinearMap_single, one_smul, one_smul, one_smul]
  exact (twistedHeckeSlashSumCharEnd_mul_of_doubleCoset_eq_mul k χ D₁ D₂ a b
    hcover₁ hinj₁ hcover₂ hinj₂ D₃ hD₃ hinj₃).symm

end Free

end HeckeRing.GL2

end
