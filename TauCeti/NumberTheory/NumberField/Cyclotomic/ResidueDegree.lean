/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
public import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup

-- Roadmap source: `TauCetiRoadmap/NumberFieldArithmetic/README.md` @ `2172af4ad0d3`, Layer 2.6,
-- the cyclotomic Frobenius identification, read as a splitting law. It is also the tool the
-- Layer 8.3 worked example `4.0.125.1` = ℚ(ζ₅) needs, where the Frobenius data is recorded as
-- `f(p) = orderOf (p : ZMod 5)ˣ`. The credit sits outside the module docstring deliberately.

/-!
# The residue degree in a cyclotomic extension

The classical cyclotomic splitting law: at a prime `𝔭` not dividing `m`, the residue degree of a
prime of `F` above `𝔭` is the multiplicative order of `𝔑𝔭` modulo `m`. Over `ℚ` this is the
familiar statement that `f(p)` is the order of `p` in `(ZMod m)ˣ` — so `p` splits completely
exactly when `p ≡ 1 (mod m)`, and is inert exactly when `p` generates `(ZMod m)ˣ`.

## Both halves are already here

Nothing in this file is a new computation. It joins two facts that were proved separately:

* `Ideal.orderOf_eq_inertiaDeg_of_isArithFrobAt` — the order of a Frobenius element at an
  unramified prime is the residue degree;
* `AlgHom.IsArithFrobAt.autToPow_eq_absNorm` — the cyclotomic character sends such a Frobenius
  to `𝔑𝔭 mod m`.

The only step between them is that the cyclotomic character is *injective*
(`IsPrimitiveRoot.autToPow_injective`), so it preserves orders. That is what turns an identity
about a group element into a computation in `(ZMod m)ˣ`.

The second statement is phrased so the caller supplies the unit `u : (ZMod m)ˣ` together with
the proof that it reduces to `𝔑𝔭`. This avoids building a unit out of a coprimality hypothesis
inside the statement, and lets a caller pass whichever presentation it already holds — over `ℚ`,
typically `ZMod.unitOfCoprime p`.

## Main results

* `TauCeti.NumberField.inertiaDeg_eq_orderOf_autToPow`: the residue degree is the order of the
  cyclotomic character at a Frobenius.
* `TauCeti.NumberField.inertiaDeg_eq_orderOf_of_coe_eq_absNorm`: equivalently, the order of
  `𝔑𝔭` in `(ZMod m)ˣ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §10.
-/

public section

open IsDedekindDomain NumberField

open scoped NumberField

namespace TauCeti.NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F]
  [Algebra K F] [IsGalois K F]

/-- **The residue degree is the order of the cyclotomic character at a Frobenius.** The character
is injective, so it preserves the order of the Frobenius element, which is the residue degree. -/
theorem inertiaDeg_eq_orderOf_autToPow {m : ℕ} [NeZero m] {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    [IsCyclotomicExtension {m} K F]
    (Q : Ideal (𝓞 F)) [Q.IsPrime] (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q]
    {σ : F ≃ₐ[K] F} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    Q.inertiaDeg (𝓞 K) = orderOf (hζ.autToPow K σ) := by
  rw [orderOf_injective _ (hζ.autToPow_injective K),
    Ideal.orderOf_eq_inertiaDeg_of_isArithFrobAt Q hQ hσ]

/-- **The cyclotomic splitting law.** At a prime `𝔭` not dividing `m`, the residue degree of `Q`
above `𝔭` is the multiplicative order of `𝔑𝔭` in `(ZMod m)ˣ`.

The unit `u` is supplied by the caller along with the proof that it reduces to `𝔑𝔭`; over `ℚ`
this is `ZMod.unitOfCoprime p`. -/
theorem inertiaDeg_eq_orderOf_of_coe_eq_absNorm {m : ℕ} [NeZero m] {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) [IsCyclotomicExtension {m} K F]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q]
    {σ : F ≃ₐ[K] F} (hσ : IsArithFrobAt (𝓞 K) σ Q)
    (u : (ZMod m)ˣ) (hu : (u : ZMod m) = Ideal.absNorm 𝔭.asIdeal) :
    Q.inertiaDeg (𝓞 K) = orderOf u := by
  -- A unit of `ZMod m` is determined by its value, so `u` is the character at `σ`.
  have hueq : u = hζ.autToPow K σ :=
    Units.ext (by rw [hu, hσ.autToPow_eq_absNorm hζ 𝔭 hm Q])
  rw [hueq, inertiaDeg_eq_orderOf_autToPow hζ Q hQ hσ]

end TauCeti.NumberField

end
