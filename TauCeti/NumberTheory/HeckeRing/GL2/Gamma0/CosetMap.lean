/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.Basic
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DoubleCoset

/-!
# Comparing the `Γ₀(N)` and level-one double cosets

**Shimura, Propositions 3.30 and 3.31.** Since `Γ₀(N) ≤ SL₂(ℤ)` and `Δ₀(N) ≤ Δ`, sending
`Γ₀(N) α Γ₀(N)` to `SL₂(ℤ) α SL₂(ℤ)` is well defined on double cosets:

```lean
noncomputable def toLevelOneCoset :
    HeckeCoset (Delta0 N) (Gamma0Image N) (Gamma0Image N) →
      HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)
```

and it is **injective on the cosets whose determinant is coprime to the level**
(`toLevelOneCoset_injOn_coprimeDet`). Injectivity is the content: two `Γ₀(N)`-double cosets
with the same level-one double coset are recovered from it by intersecting with `Δ₀(N)`, which
is exactly `doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0Image`.

This is what identifies the good-prime part of `R(Γ₀(N), Δ₀(N))` with the level-one Hecke ring,
and so the step by which `T_n` for `gcd(n, N) = 1` inherits its level-one behaviour.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Props.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), the `cosetMap`
and `shimura_prop_3_31` section. The bespoke `Delta0_inclusion` there is `Submonoid.inclusion`
here, and AINTLIB's `HeckePair` bundle is Mathlib's `HeckeCoset`.

## Main definitions

* `HeckeRing.GL2.CoprimeDet`: an element of `Δ₀(N)` whose integral representative has
  determinant coprime to `N`.
* `HeckeRing.GL2.toLevelOneCoset`: the map `Γ₀(N) α Γ₀(N) ↦ SL₂(ℤ) α SL₂(ℤ)`.

## Main results

* `HeckeRing.GL2.toLevelOneCoset_mk`: its computation rule on a representative.
* `HeckeRing.GL2.toLevelOneCoset_injOn_coprimeDet`: **Shimura, Proposition 3.31** — it is
  injective on coprime-determinant double cosets.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Propositions 3.30 and 3.31.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- An element of `Δ₀(N)` has **coprime determinant** when every integral matrix representing
it has determinant coprime to `N`.

Quantifying over all representatives rather than choosing one keeps the predicate free of a
choice; the representative is unique anyway, since `ℤ → ℚ` is injective. -/
def CoprimeDet (g : Delta0 N) : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
    (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) →
      Int.gcd A.det N = 1

/-- **Shimura, Proposition 3.30.** Passing from a `Γ₀(N)`-double coset to the level-one double
coset of the same element is well defined: `Γ₀(N) ≤ SL₂(ℤ)`, so `Γ₀(N) a Γ₀(N) = Γ₀(N) b Γ₀(N)`
forces `SL₂(ℤ) a SL₂(ℤ) = SL₂(ℤ) b SL₂(ℤ)`. -/
noncomputable def toLevelOneCoset :
    HeckeCoset (Delta0 N) (Gamma0Image N) (Gamma0Image N) →
      HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2) :=
  Quotient.lift
    (fun g ↦ HeckeCoset.mk (SLnZ 2) (SLnZ 2) (Submonoid.inclusion (Delta0_le_posDetInt N) g))
    (fun a b hab ↦ by
      -- the setoid relation on `HeckeCoset` *is* equality of the double cosets
      have hab' : DoubleCoset.doubleCoset (a : GL (Fin 2) ℚ) (Gamma0Image N) (Gamma0Image N) =
          DoubleCoset.doubleCoset (b : GL (Fin 2) ℚ) (Gamma0Image N) (Gamma0Image N) := hab
      refine HeckeCoset.eq_iff.mpr (DoubleCoset.doubleCoset_eq_of_mem ?_).symm
      -- `b` lies in the `Γ₀(N)`-double coset of `a`, hence in its level-one one
      exact doubleCoset_Gamma0Image_le_doubleCoset_SLnZ N (a : GL (Fin 2) ℚ)
        (hab' ▸ DoubleCoset.mem_doubleCoset_self _ _ _))

/-- The computation rule for `toLevelOneCoset`: it keeps the representative and forgets the
level. -/
@[simp] lemma toLevelOneCoset_mk (g : Delta0 N) :
    toLevelOneCoset N (HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) g) =
      HeckeCoset.mk (SLnZ 2) (SLnZ 2) (Submonoid.inclusion (Delta0_le_posDetInt N) g) := (rfl)

/-- **Shimura, Proposition 3.31.** `toLevelOneCoset` is injective on the double cosets whose
determinant is coprime to `N`: the level-one double coset determines the `Γ₀(N)` one, because
intersecting it with `Δ₀(N)` returns the latter. -/
theorem toLevelOneCoset_injOn_coprimeDet {a b : Delta0 N} (ha : CoprimeDet N a)
    (hb : CoprimeDet N b)
    (h : toLevelOneCoset N (HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) a) =
      toLevelOneCoset N (HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) b)) :
    HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) a =
      HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) b := by
  obtain ⟨Aa, hAa, -, hAaN, -⟩ := (mem_Delta0_iff N).mp a.2
  obtain ⟨Ab, hAb, -, hAbN, -⟩ := (mem_Delta0_iff N).mp b.2
  rw [toLevelOneCoset_mk, toLevelOneCoset_mk, HeckeCoset.eq_iff,
    Submonoid.coe_inclusion, Submonoid.coe_inclusion] at h
  refine HeckeCoset.eq_iff.mpr ?_
  -- each `Γ₀(N)`-double coset is its level-one one cut down to `Δ₀(N)`, and those agree
  rw [← doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0Image N _ a.2 Aa hAa (ha Aa hAa),
    ← doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0Image N _ b.2 Ab hAb (hb Ab hAb), h]

end HeckeRing.GL2
