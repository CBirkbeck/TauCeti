/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Complements on the ideal class group

Two facts about Mathlib's `ClassGroup R` that its own file does not carry.

## Main results

* `ClassGroup.mk_toPrincipalIdeal`: a principal fractional ideal has trivial class. This is the
  `simp` form of `ClassGroup.mk_eq_one_iff` for the one witness that arises in practice, and it
  holds over any domain.
* `IsDedekindDomain.HeightOneSpectrum.classGroupMk`: the class `[v]` of a height one prime of a
  Dedekind domain, with `classGroupMk_eq_mk` identifying it with the class of `v.asIdeal` seen as
  an invertible fractional ideal of any fraction field.

Both are stated at the weakest hypotheses their proofs need — `ClassGroup.mk_toPrincipalIdeal`
over `[IsDomain R]`, since nothing in it is Dedekind-specific — and neither mentions Weil
divisors, so consumers in `RingTheory` and `NumberTheory` can reach them. The Weil-divisor side,
which needs the factorization API, lives in
`TauCeti.AlgebraicGeometry.WeilDivisor.FractionalIdealDivisor.ClassGroup`.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

/-- A principal fractional ideal has trivial ideal class. -/
@[simp]
lemma ClassGroup.mk_toPrincipalIdeal {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K x) = 1 :=
  ClassGroup.mk_eq_one_iff.mpr
    ⟨⟨(x : K), by rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]⟩⟩

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The class of a height one prime `v` in the ideal class group of `R`. -/
noncomputable def IsDedekindDomain.HeightOneSpectrum.classGroupMk (v : HeightOneSpectrum R) :
    ClassGroup R :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

/-- The class of `v` is the class of `v.asIdeal` viewed as an invertible fractional ideal of a
fraction field `K`. -/
lemma IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) :
    v.classGroupMk = ClassGroup.mk K (Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)) := by
  rw [HeightOneSpectrum.classGroupMk, ← ClassGroup.mk_mk0 K]
  exact congrArg _ (Units.ext (FractionalIdeal.coe_mk0 K _))

end
