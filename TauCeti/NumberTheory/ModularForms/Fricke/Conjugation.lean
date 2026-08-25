/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.NumberTheory.ModularForms.Fricke.Matrix

/-!
# Conjugating `Γ₀(N)` and `Γ₁(N)` by the Fricke matrix

For `N ≠ 0` and `σ = !![a, b; c, d] ∈ Γ₀(N)`, so `N ∣ c`, conjugating by the Fricke matrix
`W = !![0, -1; N, 0]` of `TauCeti/NumberTheory/ModularForms/Fricke/Matrix.lean` gives

`W · σ · W⁻¹ = !![d, -c/N; -N·b, a]`,

which is again integral, again of determinant one, and again in `Γ₀(N)`. This file builds the
right-hand side as an honest `SL(2, ℤ)` matrix — `frickeConjSL` — reading it off the entries of
`σ`, so that it is defined at every level; records that it stays inside `Γ₀(N)` and inside
`Γ₁(N)`, again at every level; and proves, for `N ≠ 0`, the two matrix identities that move `W`
past `σ` and are what make `frickeConjSL σ` the conjugate `W · σ · W⁻¹`.

`frickeConjSL` is defined directly by its entries rather than as a product `W * σ * W⁻¹`: the
latter lives in `GL (Fin 2) K` and is only *incidentally* integral, so reading an `SL(2, ℤ)`
element back out of it would need the divisibility argument anyway. Defining it by entries and
proving the product identities afterwards keeps the divisibility in one place.

## Level

`N ≠ 0` is what makes `W` invertible, and so what makes conjugation by `W` mean anything. It is
needed for the *conjugation*, though, not for the entry formula, so it is stated where `W`
itself appears: as `[NeZero (N : K)]` on the two normalization identities over `K`, which are
the statements that actually call `frickeConjSL σ` a conjugate. The `ℤ`-valued declarations
below carry no level hypothesis — the matrix `!![d, -c'; -N·b, a]` has determinant `1` and lies
in both congruence subgroups for every `N`, `c = N · (c / N)` holding at `N = 0` as well, both
sides being zero.

Level zero is genuinely degenerate, and the declarations below are worded so that nothing
claims otherwise: `Γ₀(0)` is the upper-triangular subgroup, the quotient `c / N` is `0`, and the
formula collapses to `!![a, b; 0, d] ↦ !![d, 0; 0, a]`, which forgets `b`. That is a
well-defined `SL(2, ℤ)`-valued map, just not a conjugation — and since `frickeGL K 0` does not
exist, no identity here asserts that it is one.

## Base field

The conjugation identities are stated over an arbitrary field `K` in which `N` is invertible,
matching the parameterization of `frickeGL`. The weight-`k` slash action needs them over `ℝ`
while the `GL (Fin 2) ℚ` Hecke-ring stack needs them over `ℚ`; stating them over `K` serves both
directly, with no transport lemma between the two, since `Matrix.SpecialLinearGroup.mapGL` is
itself defined at an arbitrary algebra.

## Main definitions

* `TauCeti.frickeConjSL`: the matrix `!![d, -c/N; -N·b, a]` as an element of `SL(2, ℤ)`;
  for `N ≠ 0` it is the conjugate `W · σ · W⁻¹`.

## Main results

* `TauCeti.coe_frickeConjSL`: the entries of `frickeConjSL σ`, namely `!![d, -c/N; -N·b, a]`.
* `TauCeti.frickeConjSL_mem_Gamma0`, `TauCeti.frickeConjSL_mem_Gamma1`: that formula preserves
  both congruence subgroups, at every level.
* `TauCeti.frickeGL_mul_mapGL`, `TauCeti.mapGL_mul_frickeGL`: for `N ≠ 0`, the two
  normalization identities `W · σ = (W σ W⁻¹) · W` and `σ · W = W · (W σ W⁻¹)` in
  `GL (Fin 2) K`. These are the statements that exhibit `W` as normalizing `Γ₀(N)`.

## Relation to the Atkin–Lehner anti-involution

`TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/AtkinLehner.lean` also carries `Γ₀(N)` into itself,
so the two results look superficially alike. They are different maps. That one is
`g ↦ w · gᵀ · w⁻¹` for the diagonal `w = natDiagGL 2 ![1, N]`: it transposes, and it is an
*anti*-homomorphism, bundled as `HeckeRing.GL2.atkinLehnerAntiInvolution_bar` on the Hecke ring
`Δ₀(N)`. `frickeConjSL` is plain conjugation by `!![0, -1; N, 0]`, with no transpose, and lives
on `Γ₀(N)` itself. The two *matrices* are already distinguished in `Fricke/Matrix.lean`; this is
the corresponding note for the two conjugation maps.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Fricke.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `340875adfb2`, Apache-2.0, Chris Birkbeck), realizing part of Layer 6 of the ModularForms
roadmap. AINTLIB names the divisibility witness `botLeftDiv` and keeps it private; it is private
here too, and `coe_frickeConjSL` writes the quotient `c / N` out instead, so the public API is
the matrix formula alone. AINTLIB obtains the witness as the `Exists.choose` of the `Γ₀(N)`
divisibility, which makes it and `frickeConjSL` `noncomputable` and their entries opaque; here it
is the honest quotient `c / N`, exact because `N ∣ c`, so both definitions are computable and
reduce entrywise. AINTLIB states the two normalization identities over `ℚ` and then transports
each along `ℚ → ℝ` by hand, in `glMap_frickeGL_mul_mapGL` and `mapGL_mul_glMap_frickeGL`; stating
them over `K` as below makes both transports the corresponding instance, so those two lemmas have
no counterpart here.

The diamond-character companion `Gamma0MapUnits_frickeConjSL` is deliberately *not* ported: it
is stated in terms of AINTLIB's `Gamma0MapUnits`, the unit-valued refinement of mathlib's
`CongruenceSubgroup.Gamma0Map`, which TauCeti does not have. It belongs with that definition
rather than here, and nothing in this file needs it.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ}

/-- For `σ ∈ Γ₀(N)` with lower-left entry `c`, the integer `c'` such that `c = N · c'`. It is
this quotient, not `c` itself, that appears as an entry of the Fricke conjugate.

An implementation detail: the public `coe_frickeConjSL` writes `c / N` out. -/
private def lowerLeftDiv (σ : ↥(Gamma0 N)) : ℤ :=
  (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (N : ℤ)

/-- The defining property of `lowerLeftDiv`: the lower-left entry of `σ` is `N · lowerLeftDiv σ`.
This is the only place the `Γ₀(N)` divisibility is used. -/
private theorem lowerLeftDiv_spec (σ : ↥(Gamma0 N)) :
    (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = N * lowerLeftDiv σ :=
  (Int.mul_ediv_cancel'
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp σ.property))).symm

/-- The Fricke conjugate of `σ = !![a, b; N·c', d] ∈ Γ₀(N)`, as an element of `SL(2, ℤ)`: the
matrix `!![d, -c'; -N·b, a]`.

For `N ≠ 0` this is `W · σ · W⁻¹`, and equally `W⁻¹ · σ · W` since `W² = (-N) • 1` is central;
that is the content of `frickeGL_mul_mapGL` and `mapGL_mul_frickeGL`, which carry the
invertibility hypothesis. At `N = 0` the formula still defines a matrix, but a degenerate one;
see the `Level` section of the module docstring. -/
public def frickeConjSL (σ : ↥(Gamma0 N)) : SL(2, ℤ) :=
  ⟨!![(σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -lowerLeftDiv σ;
      -(N : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0], by
    have hc := lowerLeftDiv_spec σ
    set M := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hM
    have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      have := σ.1.prop
      rwa [det_fin_two] at this
    rw [det_fin_two_of]
    linear_combination hdet + M 0 1 * hc⟩

/-- The underlying matrix of `frickeConjSL σ`, with the exact quotient `c / N` of the lower-left
entry `c` written out. -/
@[simp]
public theorem coe_frickeConjSL (σ : ↥(Gamma0 N)) :
    (frickeConjSL σ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (N : ℤ));
         -(N : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0] := by
  simp [frickeConjSL, lowerLeftDiv]

/-- **`frickeConjSL` preserves `Γ₀(N)`**: its lower-left entry `-N·b` is visibly divisible by
`N`. This is a statement about the entry formula, so it holds at every level; for `N ≠ 0`, where
`frickeConjSL σ` really is `W · σ · W⁻¹`, it says that `W` normalizes `Γ₀(N)`. -/
public theorem frickeConjSL_mem_Gamma0 (σ : ↥(Gamma0 N)) :
    frickeConjSL σ ∈ Gamma0 N := by
  rw [Gamma0_mem, coe_frickeConjSL]
  simp

/-- **`frickeConjSL` preserves `Γ₁(N)`**: the entry formula swaps the two diagonal entries, so
both remain `≡ 1 (mod N)`. As for `Γ₀(N)` this holds at every level, and for `N ≠ 0` it says
that `W` normalizes `Γ₁(N)`. -/
public theorem frickeConjSL_mem_Gamma1 (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N) :
    frickeConjSL ⟨σ, Gamma1_in_Gamma0 N hσ⟩ ∈ Gamma1 N := by
  obtain ⟨ha, hd, -⟩ := (Gamma1_mem N σ).mp hσ
  rw [Gamma1_mem, coe_frickeConjSL]
  exact ⟨by simpa using hd, by simpa using ha, by simp⟩

section Field

variable (K : Type*) [Field K]

/-- The lower-left entry of `σ ∈ Γ₀(N)`, read in `K`, is `N` times `lowerLeftDiv σ`. The
`K`-valued form of `lowerLeftDiv_spec`, which is what the entrywise computations below
consume. -/
private theorem lowerLeftDiv_spec_field (σ : ↥(Gamma0 N)) :
    ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : K) = (N : K) * (lowerLeftDiv σ : K) := by
  exact_mod_cast congrArg (Int.cast : ℤ → K) (lowerLeftDiv_spec σ)

variable [NeZero (N : K)]

/-- **The normalization identity** `W · σ = (W σ W⁻¹) · W` in `GL (Fin 2) K`, for `σ ∈ Γ₀(N)`.
This is the form that moves `W` from the left of `σ` to its right, which is what a slash-action
computation needs. -/
public theorem frickeGL_mul_mapGL (σ : ↥(Gamma0 N)) :
    frickeGL K N * mapGL K (σ : SL(2, ℤ)) = mapGL K (frickeConjSL σ) * frickeGL K N := by
  apply Units.ext
  have hc := lowerLeftDiv_spec_field K σ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_frickeGL, coe_frickeConjSL, lowerLeftDiv,
      hc] <;>
    ring

/-- `W²` commutes with everything in `GL (Fin 2) K`: it is the scalar matrix `(-N) • 1`. -/
private theorem frickeGL_sq_mul_comm (A : GL (Fin 2) K) :
    frickeGL K N ^ 2 * A = A * frickeGL K N ^ 2 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_frickeGL_sq]
  simp

/-- **The mirror normalization identity** `σ · W = W · (W σ W⁻¹)` in `GL (Fin 2) K`, for
`σ ∈ Γ₀(N)`; equivalently `frickeConjSL σ = W⁻¹ · σ · W`.

This is `frickeGL_mul_mapGL` carried across `W²`, rather than a second entrywise computation:
`(σ · W) · W = σ · W² = W² · σ = W · (W · σ) = W · (W σ W⁻¹) · W`, and `W` cancels on the
right. -/
public theorem mapGL_mul_frickeGL (σ : ↥(Gamma0 N)) :
    mapGL K (σ : SL(2, ℤ)) * frickeGL K N = frickeGL K N * mapGL K (frickeConjSL σ) := by
  refine mul_right_cancel (b := frickeGL K N) ?_
  calc mapGL K (σ : SL(2, ℤ)) * frickeGL K N * frickeGL K N
      = frickeGL K N ^ 2 * mapGL K (σ : SL(2, ℤ)) := by
        rw [mul_assoc, ← sq, ← frickeGL_sq_mul_comm]
    _ = frickeGL K N * (frickeGL K N * mapGL K (σ : SL(2, ℤ))) := by rw [sq, mul_assoc]
    _ = frickeGL K N * (mapGL K (frickeConjSL σ) * frickeGL K N) := by
        rw [frickeGL_mul_mapGL]
    _ = frickeGL K N * mapGL K (frickeConjSL σ) * frickeGL K N := (mul_assoc _ _ _).symm

end Field

end TauCeti
