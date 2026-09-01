/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CharRing

/-!
# The identity double coset acts as the identity

`Nebentypus/CharRing.lean` extends the twisted slash sum `ℤ`-linearly over the Hecke ring, giving
`twistedHeckeSlashRingCharLinearMap`. This file evaluates that extension at `1`.

The Hecke ring's unit is the basis element of the identity double coset
(`HeckeCosetModule.one_def`), so the value at `1` is the twisted operator of
`(1 : HeckeCoset (Delta0 N) Γ₀(N) Γ₀(N))`. That operator is the identity: the double coset
`Γ₀(N) · 1 · Γ₀(N)` is the single right coset `Γ₀(N)`, so the sum has one summand, and on the
character space that summand's nebentypus weight is exactly the inverse of the character the
slash produces. The two cancel.

## Why this is not the ring homomorphism

`twistedHeckeSlashRingCharLinearMap` is `ℤ`-linear, not known to be multiplicative: promoting it
to a ring homomorphism additionally needs `map_mul`, which rests on the multiplicity count for a
product of double cosets and is not available here. `map_one` does not, and is proved outright
below. The two halves are independent, and this is the one that is unconditional.

## Main results

* `HeckeRing.GL2.twistedHeckeSlashSum_identity_coset`: the twisted slash sum over the identity
  double coset returns a `χ`-invariant function unchanged.
* `HeckeRing.GL2.twistedHeckeSlashSumCharEnd_one`: hence the endomorphism of the character space
  attached to the identity double coset is `1`.
* `HeckeRing.GL2.twistedHeckeSlashRingCharLinearMap_one`: hence the `ℤ`-linear extension sends
  `1` to `1`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`, Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`), whose
`twistedHeckeSlashGen_identity_coset` (line 935), `twistedHeckeOperatorFunction_one` (line 972)
and `twistedHeckeSumFunction_one` (line 977) are the three statements below. The double-coset
indexing, the `HeckeCosetModule.single` spelling and the `functionCharSpace` carrier are this
repository's.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn
open scoped MatrixGroups ModularForm HeckeCosetModule

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) [NeZero N]

/-- **The identity double coset acts as the identity on the character space.**

The index of the sum is a singleton, because `Γ₀(N) · 1 · Γ₀(N)` is one right coset, and the
single summand is `χ(a)⁻¹ • (f ∣[k] a)` at a representative `a ∈ Γ₀(N)`, which is `f` by the
nebentypus relation defining `functionCharSpace`.

The `χ`-invariance hypothesis is essential and not an artefact: on a general `f : ℍ → ℂ` the
weighted sum depends on the chosen representatives, as `twistedHeckeSlashSum`'s own docstring
records. -/
theorem twistedHeckeSlashSum_identity_coset (f : ℍ → ℂ) (hf : f ∈ functionCharSpace k χ) :
    twistedHeckeSlashSum k χ 1 f = f := by
  sorry

/-- **The endomorphism of the character space attached to the identity double coset is the
identity.** This is `twistedHeckeSlashSum_identity_coset` read through the restriction of
`Nebentypus/Invariance.lean`, where the `χ`-invariance hypothesis is carried by the carrier. -/
@[simp] theorem twistedHeckeSlashSumCharEnd_one :
    twistedHeckeSlashSumCharEnd k χ 1 = 1 := by
  sorry

/-- **The `ℤ`-linear extension sends `1` to `1`** — the `map_one` half of the twisted Hecke ring
homomorphism, which unlike `map_mul` needs no multiplicity count. -/
@[simp] theorem twistedHeckeSlashRingCharLinearMap_one :
    twistedHeckeSlashRingCharLinearMap k χ 1 = 1 := by
  sorry

end HeckeRing.GL2

end
