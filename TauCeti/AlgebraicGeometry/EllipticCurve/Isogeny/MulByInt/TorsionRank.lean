/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard
public import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
# The `ℓ`-torsion is a two-dimensional `ZMod ℓ`-vector space

For a prime `ℓ` invertible in an algebraically closed base field, `ker [ℓ]` is free of rank two
over `ZMod ℓ`. Every point of the kernel is killed by `ℓ`, which makes it a `ZMod ℓ`-module, and
`ZMod ℓ` is a field, so the kernel is a vector space whose cardinality `ℓ ²` reads off its
dimension.

Rank two is what lets an endomorphism act on the torsion as a `2 × 2` matrix over `ZMod ℓ`, which
is the form the degree and the trace are read off in.

## Main definitions

* `TauCeti.Isogeny.mulByPrimeIsogeny`: multiplication by a prime `ℓ`, with the division
  polynomial's non-vanishing supplied by primality rather than assumed.
* `TauCeti.Isogeny.kerZModModule`: the `ZMod ℓ`-module structure on `ker [ℓ]`, an instance.

## Main results

* `TauCeti.Isogeny.nsmul_eq_zero_of_mem_ker_mulByPrimeIsogeny`: the kernel is killed by `ℓ`.
* `TauCeti.Isogeny.finrank_ker_mulByPrimeIsogeny`: it has dimension two.
* `TauCeti.Isogeny.nonempty_linearEquiv_ker_mulByPrimeIsogeny`: hence `E[ℓ] ≅ (ZMod ℓ) ²`.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md` — "**`ell-torsion-rank`**". This file is **not** that
target and does not discharge it: the roadmap states the torsion structure for every `N`, over a
separably closed field, as an additive equivalence on the intrinsic `Submodule.torsionBy ℤ`, and
what is proved here is the prime case over an algebraically closed field, phrased on the kernel of
the isogeny `[ℓ]`. It is a prerequisite of the roadmap's stated theorem rather than the theorem
itself, in the sense of `DivisionPolynomial/Descent.lean`'s roadmap note.

The prime case is nevertheless the whole of what the Hasse route consumes: the symplectic
multiplier `Aᵀ J A = (deg A) • J` is requested one prime at a time, so no prime-power or
Chinese-remainder structure theorem enters that route. Reaching the roadmap target itself needs the
general-`N` statement and a descent from algebraically to separably closed, neither of which is
attempted here.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
  [IsAlgClosed F] {l : ℕ} [hl : Fact l.Prime]

variable (l) in
omit [IsAlgClosed F] in
/-- **Multiplication by a prime `ℓ`**: primality supplies the non-vanishing hypothesis the
division-polynomial construction asks for, so no such hypothesis is exposed here. -/
noncomputable abbrev mulByPrimeIsogeny : Isogeny W W :=
  mulByIntIsogenyOfNeZero W (Int.natCast_ne_zero.mpr hl.out.ne_zero)

omit [IsAlgClosed F] in
/-- Every point of `ker [ℓ]` is killed by `ℓ`. -/
@[simp]
theorem nsmul_eq_zero_of_mem_ker_mulByPrimeIsogeny (x : (mulByPrimeIsogeny W l).ker) :
    l • x = 0 := by
  have hx : ((l : ℤ)) • (x : (W⁄F).toAffine.Point) = 0 :=
    (mem_ker_mulByIntIsogeny_iff W _).1 x.2
  have : ((l : ℤ)) • x = 0 := Subtype.ext (by simpa using hx)
  simpa using this

variable (l) in
omit [IsAlgClosed F] in
/-- **The `ZMod ℓ`-module structure on `ker [ℓ]`**, from every point being killed by `ℓ`. -/
noncomputable instance kerZModModule : Module (ZMod l) (mulByPrimeIsogeny W l).ker :=
  AddCommGroup.zmodModule (nsmul_eq_zero_of_mem_ker_mulByPrimeIsogeny W)

/-- **`E[ℓ]` is two-dimensional over `ZMod ℓ`.** -/
@[simp]
theorem finrank_ker_mulByPrimeIsogeny (hchar : (l : F) ≠ 0) :
    Module.finrank (ZMod l) (mulByPrimeIsogeny W l).ker = 2 := by
  classical
  let _ : Fintype (mulByPrimeIsogeny W l).ker := Fintype.ofFinite _
  have hcard : Fintype.card (mulByPrimeIsogeny W l).ker = l ^ 2 := by
    have h2 : Nat.card (mulByPrimeIsogeny W l).ker = ((l : ℤ)).natAbs ^ 2 :=
      card_ker_mulByIntIsogeny W (by simpa using hchar)
    rwa [Nat.card_eq_fintype_card, Int.natAbs_natCast] at h2
  have hpow := Module.card_eq_pow_finrank (K := ZMod l) (V := (mulByPrimeIsogeny W l).ker)
  rw [hcard, ZMod.card] at hpow
  exact (Nat.pow_right_injective hl.out.two_le hpow).symm

/-- **`E[ℓ] ≅ (ZMod ℓ)²`**: the `ℓ`-torsion is free of rank two. -/
theorem nonempty_linearEquiv_ker_mulByPrimeIsogeny (hchar : (l : F) ≠ 0) :
    Nonempty ((mulByPrimeIsogeny W l).ker ≃ₗ[ZMod l] (Fin 2 → ZMod l)) := by
  have : Module.Finite (ZMod l) (mulByPrimeIsogeny W l).ker := Module.Finite.of_finite
  exact FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (by simpa using finrank_ker_mulByPrimeIsogeny W hchar)

end TauCeti.Isogeny

end
