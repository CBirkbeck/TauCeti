/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.Associativity

/-!
# Multiplicativity of a linear extension is a basis-level condition

A `Z`-linear map out of the Hecke ring is determined by its values on the basis elements
`single Z D 1`, one for each double coset. This file records that the same is true of its
*multiplicativity*: `F (x * y) = F x * F y` for all `x` and `y` follows from the special case
where both arguments are basis elements, and likewise for the reversed identity
`F (x * y) = F y * F x`.

That is not automatic. Multiplicativity is a statement about a pair of arguments, so reducing it
to basis elements needs the convolution to be biadditive and to commute with the scalars on both
flanks — the first two facts are `HeckeCosetModule.mul_add` and `HeckeCosetModule.add_mul`, and
the third comes from `HeckeCosetModule.single_mul_single`, which exhibits
`single Z D₁ a * single Z D₂ b` as `a • b •` the structure constants and hence as
`a • b • (single Z D₁ 1 * single Z D₂ 1)`.

## Why the reversed identity is stated too

The Hecke ring acts on modular forms through the slash, which is a *right* action, while
`Module.End` multiplies by composition. Every extension of a coset action over the Hecke ring is
therefore an anti-homomorphism rather than a homomorphism — see
`HeckeRing.GL2.twistedHeckeSlashRingCharLinearMap_mul_single_single`, whose conclusion puts the
two factors in the opposite order. Both directions are recorded so that neither consumer has to
route through `MulOpposite`.

## What this does and does not close

`Nebentypus/Composition.lean` already proves the basis-element identity for the twisted
character-space extension, under hypotheses on the double-coset product, and its own
documentation calls that "the generator-level input that a multiplicativity proof ... would
consume; it does not itself close that gap, which concerns arbitrary Hecke-ring elements". This
file supplies the missing implication in general, so what remains of that gap is entirely the
double-coset combinatorics: an unconditional basis-element identity, with no ring theory left
around it.

## Main results

* `HeckeCosetModule.map_mul_of_single_single`: a linear map that is multiplicative on basis
  elements is multiplicative.
* `HeckeCosetModule.map_mul_rev_of_single_single`: the same with the factors on the right-hand
  side in the opposite order, the shape a right action produces.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1 (the Hecke ring as a free module on the double cosets).
-/

public section

namespace HeckeCosetModule

variable {G : Type*} [Group G] {Δ : Submonoid G} {H : Subgroup G} [IsHeckeTriple Δ H H]

section Semiring

variable {Z : Type*} [Semiring Z] {A : Type*} [Semiring A] [Module Z A]
  [IsScalarTower Z A A] [SMulCommClass Z A A]

/-- The product of two basis elements is the product of the two *unit* basis elements, scaled by
the two coefficients. This is `single_mul_single` with the structure constants eliminated between
the general and the unit case, which is the form the reductions below consume. -/
private lemma single_mul_single_eq_smul_smul (D₁ D₂ : HeckeCoset Δ H H) (a b : Z) :
    single Z D₁ a * single Z D₂ b = a • b • (single Z D₁ 1 * single Z D₂ 1) := by
  rw [single_mul_single, single_mul_single, one_smul, one_smul]

/-- **Multiplicativity is a basis-level condition.** A `Z`-linear map out of the Hecke ring that
is multiplicative on the basis elements `single Z D 1` is multiplicative.

The convolution is biadditive, so both sides are biadditive in `(x, y)` and the identity
propagates from the basis by `HeckeCosetModule.induction_linear` in each argument; the
coefficients come out through `single_mul_single` and go back in by linearity of `F`. -/
theorem map_mul_of_single_single (F : 𝕋 Δ H Z →ₗ[Z] A)
    (h : ∀ D₁ D₂ : HeckeCoset Δ H H,
      F (single Z D₁ 1 * single Z D₂ 1) = F (single Z D₁ 1) * F (single Z D₂ 1))
    (x y : 𝕋 Δ H Z) : F (x * y) = F x * F y := by
  induction x using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd x₁ x₂ h₁ h₂ => rw [_root_.add_mul, map_add, map_add, h₁, h₂, _root_.add_mul]
  | hsingle D₁ a =>
    induction y using HeckeCosetModule.induction_linear with
    | h0 => simp
    | hadd y₁ y₂ h₁ h₂ => rw [_root_.mul_add, map_add, map_add, h₁, h₂, _root_.mul_add]
    | hsingle D₂ b =>
      rw [single_mul_single_eq_smul_smul, map_smul, map_smul, h, ← smul_single_one Z D₁ a,
        ← smul_single_one Z D₂ b, map_smul, map_smul, smul_mul_assoc, mul_smul_comm]

end Semiring

section CommSemiring

variable {Z : Type*} [CommSemiring Z] {A : Type*} [Semiring A] [Module Z A]
  [IsScalarTower Z A A] [SMulCommClass Z A A]

/-- **Anti-multiplicativity is a basis-level condition.** The reversed counterpart of
`HeckeCosetModule.map_mul_of_single_single`: a `Z`-linear map out of the Hecke ring that sends a
product of basis elements to the composite of their images *in the opposite order* does so on all
of the ring.

This is the direction the slash action produces: it is a right action, `Module.End` multiplies by
composition, and so the left factor of the Hecke-ring product is the operator applied first.

Unlike the unreversed statement this one needs the coefficients to commute, and not for a
technical reason: reversing the two factors exchanges their coefficients, so the two sides carry
`a • b •` and `b • a •` respectively. The same asymmetry is already visible one level down, where
`HeckeCosetModule.smul_mul` holds on the left flank of the convolution over any coefficient
semiring and fails on the right flank over a noncommutative one. -/
theorem map_mul_rev_of_single_single (F : 𝕋 Δ H Z →ₗ[Z] A)
    (h : ∀ D₁ D₂ : HeckeCoset Δ H H,
      F (single Z D₁ 1 * single Z D₂ 1) = F (single Z D₂ 1) * F (single Z D₁ 1))
    (x y : 𝕋 Δ H Z) : F (x * y) = F y * F x := by
  induction x using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd x₁ x₂ h₁ h₂ => rw [_root_.add_mul, map_add, map_add, h₁, h₂, _root_.mul_add]
  | hsingle D₁ a =>
    induction y using HeckeCosetModule.induction_linear with
    | h0 => simp
    | hadd y₁ y₂ h₁ h₂ => rw [_root_.mul_add, map_add, map_add, h₁, h₂, _root_.add_mul]
    | hsingle D₂ b =>
      rw [single_mul_single_eq_smul_smul, map_smul, map_smul, h, ← smul_single_one Z D₁ a,
        ← smul_single_one Z D₂ b, map_smul, map_smul, smul_mul_assoc, mul_smul_comm,
        smul_smul, smul_smul, mul_comm a b]

end CommSemiring

end HeckeCosetModule

end
