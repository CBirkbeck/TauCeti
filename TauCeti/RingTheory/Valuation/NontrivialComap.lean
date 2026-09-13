/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Nontriviality survives restriction along an algebraic extension

A valuation of `L` restricts along `algebraMap K L` to a valuation of `K`, and this file records
that the restriction of a nontrivial valuation is again nontrivial as soon as `L` is algebraic
over `K`.

Algebraicity is what makes this true, and it is sharp: for a transcendental extension the
restriction can collapse. The trivial valuation on `K` inside a valuation of `K(t)` that sees only
the `t`-adic order is the standard example.

## Main results

* `Valuation.isNontrivial_comap_algebraMap`: the restriction of a nontrivial valuation along an
  algebraic extension of fields is nontrivial.

## References

* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005], §3.2.

## Provenance

Not ported. Mathlib's `Valuation.RankOne.isNontrivial_restrict` is a different statement — it
restricts the *value group* of a valuation to its value subgroup, leaving the domain alone —
and nothing in `Mathlib/RingTheory/Valuation/` restricts a valuation along a ring map and
concludes nontriviality.
-/

public section

namespace Valuation

variable {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ₀]

/-- **The restriction of a nontrivial valuation along an algebraic extension is nontrivial.** -/
theorem isNontrivial_comap_algebraMap [Algebra.IsAlgebraic K L] (v : Valuation L Γ₀)
    [v.IsNontrivial] : (v.comap (algebraMap K L)).IsNontrivial := by
  by_contra hcon
  -- a trivial restriction puts `K` inside the valuation ring
  have htriv : ∀ k : K, v (algebraMap K L k) ≤ 1 := by
    intro k
    by_contra hk
    exact hcon ⟨k, by
      rcases eq_or_ne k 0 with rfl | hk0
      · simp at hk
      · exact ⟨by simpa using fun h ↦ hk (by simp [h]), fun h ↦ hk (le_of_eq h)⟩⟩
  have hmem : ∀ k : K, algebraMap K L k ∈ v.integer := fun k ↦ htriv k
  let _ : Algebra K v.integer := ((algebraMap K L).codRestrict _ hmem).toAlgebra
  have _ : IsScalarTower K v.integer L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- every element is integral over `K`, hence over the valuation ring, hence of value `≤ 1`
  have hle : ∀ x : L, v x ≤ 1 := fun x ↦
    (Valuation.Integers.isIntegral_iff_v_le_one (Valuation.integer.integers v)).1
      (Algebra.IsIntegral.isIntegral (R := K) x).tower_top
  -- the same at inverses forces every nonzero element to have value exactly `1`
  obtain ⟨x, hx0, hx1⟩ := ‹v.IsNontrivial›.exists_val_nontrivial
  refine hx1 (le_antisymm (hle x) ?_)
  have h1 : v x⁻¹ ≤ 1 := hle x⁻¹
  rw [map_inv₀] at h1
  exact (inv_le_one₀ (zero_lt_iff.mpr hx0)).mp h1

end Valuation

end
