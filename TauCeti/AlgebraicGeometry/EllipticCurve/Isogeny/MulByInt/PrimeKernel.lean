/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Kernel
public import Mathlib.Algebra.Module.ZMod

/-!
# The kernel of `[n]` is a `ZMod n`-module

`ker [n]` is the `n`-torsion subgroup, and Mathlib makes the `n`-torsion of an additive group a
`ZMod n`-module; transporting that along the equality is all there is to it. Nothing about `n`
beyond its not vanishing enters, so that is where the structure is built; for a prime `ℓ` the
non-vanishing hypothesis is supplied by primality rather than assumed, and the module structure is
the general one read at `n = ℓ`.

Nothing here assumes anything about the base field beyond its being a field — no algebraic
closure, and no condition on the characteristic. Those enter only when the kernel's cardinality is
computed, which is why they are not imposed at this layer.

## Main definitions

* `TauCeti.Isogeny.kerZModModule`: the `ZMod n`-module structure on `ker [n]`. It is a global
  instance, so typeclass synthesis supplies it and a consumer writing
  `Module.finrank (ZMod n) (mulByIntIsogenyOfNeZero W hn).ker` never names it.
* `TauCeti.Isogeny.mulByPrimeIsogeny`: multiplication by a prime `ℓ`, with the division
  polynomial's non-vanishing supplied by primality rather than assumed.

## Main results

* `TauCeti.Isogeny.ker_mulByPrimeIsogeny_eq_torsionBy`: its kernel is the `ℓ`-torsion subgroup.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

variable {n : ℕ}

/-- **The `ZMod n`-module structure on `ker [n]`**, transported from Mathlib's `n`-torsion
module structure along `ker_mulByIntIsogeny_eq_torsionBy`. It is a global instance, so typeclass
synthesis supplies it and a consumer writing
`Module.finrank (ZMod n) (mulByIntIsogenyOfNeZero W hn).ker` never names it. -/
noncomputable instance kerZModModule (hn : (n : ℤ) ≠ 0) :
    Module (ZMod n) (mulByIntIsogenyOfNeZero W hn).ker :=
  ker_mulByIntIsogeny_eq_torsionBy W _ ▸ AddSubgroup.torsionBy.zmodModule

variable {l : ℕ} [hl : Fact l.Prime]

variable (l) in
/-- **Multiplication by a prime `ℓ`**: primality supplies the non-vanishing hypothesis the
division-polynomial construction asks for, so no such hypothesis is exposed here. The
`ZMod ℓ`-module structure on its kernel is `kerZModModule` read at `n = ℓ`; nothing further is
needed for primes. -/
noncomputable abbrev mulByPrimeIsogeny : Isogeny W W :=
  mulByIntIsogenyOfNeZero W (Int.natCast_ne_zero.mpr hl.out.ne_zero)

/-- **`ker [ℓ]` is the `ℓ`-torsion subgroup**, the prime reading of
`ker_mulByIntIsogeny_eq_torsionBy`: a consumer phrased on `AddSubgroup.torsionBy` gets there
without unfolding the abbreviation or rebuilding its non-vanishing argument. -/
theorem ker_mulByPrimeIsogeny_eq_torsionBy :
    (mulByPrimeIsogeny W l).ker = AddSubgroup.torsionBy (W⁄F).toAffine.Point (l : ℤ) :=
  ker_mulByIntIsogeny_eq_torsionBy W _

end TauCeti.Isogeny

end
