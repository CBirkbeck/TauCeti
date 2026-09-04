/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The automorphisms fixing the roots of unity

`Gal(M/K(μ_m))` is the kernel of the cyclotomic character `IsPrimitiveRoot.autToPow`.

## Main results

* `IsPrimitiveRoot.fixingSubgroup_adjoin_setOfPred_pow_eq_one`
-/

public section

open IntermediateField

/-- **The fixers of `K(μ_m)` are the kernel of the cyclotomic character.**

Use it to move between a condition on `Gal(M/K(μ_m))` and one on the cyclotomic character, which
is the form a Galois splitting presents. -/
theorem IsPrimitiveRoot.fixingSubgroup_adjoin_setOfPred_pow_eq_one {K M : Type*} [Field K] [Field M]
    [Algebra K M] {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m) :
    (adjoin K {b : M | b ^ m = 1}).fixingSubgroup = (hζ.autToPow K).ker := by
  ext x
  rw [MonoidHom.mem_ker, hζ.autToPow_eq_one_iff, IntermediateField.mem_fixingSubgroup_iff]
  simp only [← AlgEquiv.smul_def]
  rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
  refine ⟨fun h ↦ by simpa [AlgEquiv.smul_def] using h ζ hζ.pow_eq_one, fun h b hb ↦ ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one (Set.mem_ofPred_eq ▸ hb)
  simp [h]
