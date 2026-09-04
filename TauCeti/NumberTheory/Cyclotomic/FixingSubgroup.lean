/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# The automorphisms fixing the roots of unity

For a primitive `m`-th root of unity `ζ` in `M`, an automorphism of `M / K` fixes every `m`-th root
of unity exactly when the cyclotomic character sends it to `1`. So `Gal(M/K(μ_m))` is the kernel of
`IsPrimitiveRoot.autToPow`.

## Main results

* `IsPrimitiveRoot.autToPow_eq_one_iff`: `autToPow K hζ x = 1 ↔ x ζ = ζ`.
* `IsPrimitiveRoot.fixingSubgroup_adjoin_setOf_pow_eq_one`: the fixers of `K(μ_m)` are that kernel.
-/

public section

open IntermediateField

namespace IsPrimitiveRoot

variable {K M : Type*} [Field K] [Field M] [Algebra K M] {m : ℕ} [NeZero m] {ζ : M}

/-- **The cyclotomic character detects fixing `ζ`.** `autToPow` sends `x` to `1` exactly when `x`
fixes the chosen primitive root, since `autToPow` is defined by the power to which `x` sends it. -/
theorem autToPow_eq_one_iff (hζ : IsPrimitiveRoot ζ m) (x : M ≃ₐ[K] M) :
    hζ.autToPow K x = 1 ↔ x ζ = ζ := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)) with hm | hm
  · -- `m = 1` forces `ζ = 1`, and `(ZMod 1)ˣ` is trivial, so both sides always hold
    have hζ1 : ζ = 1 := by simpa [← hm] using hζ.pow_eq_one
    have : Subsingleton (ZMod m)ˣ := by rw [← hm]; infer_instance
    exact ⟨fun _ ↦ by simp [hζ1], fun _ ↦ Subsingleton.elim _ _⟩
  · have : Fact (1 < m) := ⟨hm⟩
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have hspec := hζ.autToPow_spec (R := K) x
      rw [h, Units.val_one, ZMod.val_one, pow_one] at hspec
      exact hspec.symm
    · have hspec := hζ.autToPow_spec (R := K) x
      rw [h] at hspec
      have hval : (hζ.autToPow K x : ZMod m).val = 1 := by
        refine hζ.pow_inj (ZMod.val_lt _) hm ?_
        rw [hspec, pow_one]
      exact Units.ext (ZMod.val_injective m (by rw [hval, Units.val_one, ZMod.val_one]))

/-- **The fixers of `K(μ_m)` are the kernel of the cyclotomic character.**

Both directions run through the single element `ζ`: fixing every `m`-th root of unity in particular
fixes `ζ`, and fixing `ζ` fixes every root because each one is a power of `ζ`. -/
theorem fixingSubgroup_adjoin_setOf_pow_eq_one (hζ : IsPrimitiveRoot ζ m) :
    (adjoin K {b : M | b ^ m = 1}).fixingSubgroup = (hζ.autToPow K).ker := by
  ext x
  rw [MonoidHom.mem_ker, hζ.autToPow_eq_one_iff, IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨fun hx ↦ hx ζ (subset_adjoin K _ hζ.pow_eq_one), fun hx y hy ↦ ?_⟩
  -- `x` fixes each root, so it fixes the field they generate
  have hle : adjoin K {b : M | b ^ m = 1} ≤ fixedField (Subgroup.zpowers x) := by
    refine adjoin_le_iff.mpr fun b hb ↦ ?_
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one (Set.mem_ofPred_eq ▸ hb)
    simp only [SetLike.mem_coe, mem_fixedField_iff]
    intro g hg
    have hstab : x ∈ MulAction.stabilizer (M ≃ₐ[K] M) (ζ ^ i) := by
      simpa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, map_pow] using congrArg (· ^ i) hx
    simpa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] using
      Subgroup.zpowers_le.mpr hstab hg
  have hfix := hle hy
  simp only [mem_fixedField_iff] at hfix
  exact hfix x (Subgroup.mem_zpowers x)

end IsPrimitiveRoot
