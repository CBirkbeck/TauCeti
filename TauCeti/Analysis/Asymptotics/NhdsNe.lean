/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Extending a big-`O` bound from `𝓝[≠] a` to `𝓝 a`

A bound `f =O[𝓝[≠] a] g` constrains nothing at `a` itself, so it does not extend to `𝓝 a` in
general: if `‖g a‖ = 0 < ‖f a‖`, no constant works there. The hypothesis `‖f a‖ = 0` is exactly
what closes that gap, and this file records the resulting extension.

Mathlib has the special case `g = 1` (`Asymptotics.isBigO_one_nhds_ne_iff`,
`Mathlib/Analysis/Asymptotics/Lemmas.lean:120`), stated as an `iff` and needing no hypothesis at
`a`, because there the bounding function has norm `1` at every point. For a general `g` the
hypothesis is not removable — but it is only the punctured-to-unpunctured direction that needs
it. The converse direction is free and unconditional: `nhdsWithin_le_nhds` gives `𝓝[≠] a ≤ 𝓝 a`,
so `IsBigO.mono` restricts any bound on `𝓝 a` back to the punctured filter.

## Main results

* `Asymptotics.IsBigO.of_nhds_ne_of_norm_eq_zero`: a big-`O` bound on `𝓝[≠] a` extends to `𝓝 a`,
  given `‖f a‖ = 0`.

## References

Generalised from the AINTLIB `LeanModularForms` project
([github.com/CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), commit `2baa76f74`,
Apache 2.0), the declaration `isBigO_nhds_of_isBigO_punctured` in
`projects/LeanModularForms/LeanModularForms/Modularforms/DimGenCongLevels/NormTransfer.lean:84-96`,
which is stated for `f : ℂ → ℂ` against `g : ℂ → ℝ` at the point `0`.
-/

public section

open Filter Topology

namespace Asymptotics

variable {α E F : Type*} [TopologicalSpace α] [Norm E] [SeminormedAddCommGroup F]
  {f : α → E} {g : α → F} {a : α}

/-- **A big-`O` bound on `𝓝[≠] a` extends to `𝓝 a` when `‖f a‖ = 0`.** The constant supplied on
the punctured neighbourhood already works at `a`, since the left-hand side there is `0` and the
right-hand side is a nonnegative multiple of a norm.

The hypothesis cannot be dropped: where `‖g a‖ = 0 < ‖f a‖` the conclusion fails at `a` for every
constant. It is an equation between real numbers — it constrains `‖f a‖` alone and asks for no
zero on `E`, which is why `E` is assumed nothing beyond `[Norm E]`. There is deliberately no
`f a = 0` variant: at this generality that does not typecheck. -/
theorem IsBigO.of_nhds_ne_of_norm_eq_zero (hO : f =O[𝓝[≠] a] g) (hf : ‖f a‖ = 0) :
    f =O[𝓝 a] g := by
  obtain ⟨C, hC0, hC⟩ := hO.exists_nonneg
  -- the bound holds at `a` for free, so Mathlib's insertion combinator puts the point back
  have hpt : ‖f a‖ ≤ C * ‖g a‖ := hf ▸ mul_nonneg hC0 (norm_nonneg _)
  simpa using (hC.insert (s := {a}ᶜ) hpt).isBigO

end Asymptotics

end
