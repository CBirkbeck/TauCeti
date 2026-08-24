/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The Fricke matrix

The Fricke matrix `W = !![0, -1; N, 0]`, as an element of `GL (Fin 2) ℚ`. Its determinant is
`N`, which is nonzero exactly under the standing `[NeZero N]` hypothesis, so `W` is a unit.

This file is only the matrix; the Fricke *operator* on `M_k(Γ₁(N))` — slashing by `W`, with
the normalizing scalar that makes it an involution — is built on top of it.

## Main definitions

* `TauCeti.frickeGL`: the Fricke matrix as an element of `GL (Fin 2) ℚ`.

## Main results

* `TauCeti.coe_frickeGL_inv`: `W⁻¹ = !![0, 1/N; -1, 0]`.
* `TauCeti.coe_frickeGL_sq`: `W² = (-N) • 1` as matrices.
* `TauCeti.frickeGL_det_pos`: the determinant is positive. This is about the single matrix `W`,
  deliberately not a general statement about `SL`-type elements.

## Relation to the Atkin–Lehner anti-involution

Both this matrix and the conjugating matrix of
`TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/AtkinLehner.lean` are called "Atkin–Lehner" in the
literature, and they are **different matrices**. That file conjugates by `natDiagGL 2 ![1, N]`,
the diagonal rescaling repairing the transpose's failure to preserve `Γ₀(N)`; its docstring
already records that it is *not* `!![0, -1; N, 0]`. This file is the latter.

At `N = 1` the Fricke matrix coincides numerically with the level-one `S = !![0, -1; 1, 0]` of
`TauCeti/NumberTheory/ModularForms/STransform.lean` and with `TauCeti.SU2.weylMatrix`. Those are
different objects in different settings — neither is an element of `GL (Fin 2) ℚ` carrying a
determinant-`N` normalization — so `frickeGL` is not a restatement of either.

Ported from the AINTLIB `LeanModularForms` project
(`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Fricke.lean`, Chris Birkbeck,
Apache-2.0, <https://github.com/CBirkbeck/AINTLIB>), realizing part of Layer 6 of the
ModularForms roadmap.
-/

open Matrix

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- The Fricke matrix `W = !![0, -1; N, 0]` as an element of `GL (Fin 2) ℚ`, of determinant
`N`. -/
public noncomputable def frickeGL (N : ℕ) [NeZero N] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℚ), 0]
    (by rw [det_fin_two_of]; simpa using NeZero.ne (N : ℚ))

/-- The underlying matrix of `frickeGL N`. -/
@[simp]
public theorem coe_frickeGL :
    (↑(frickeGL N) : Matrix (Fin 2) (Fin 2) ℚ) = !![0, -1; (N : ℚ), 0] := by
  simp [frickeGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]

-- No separate determinant lemma is provided: `coe_frickeGL` already exposes the underlying
-- matrix, from which the value `N` and its matrix form both follow.
/-- The determinant of `frickeGL N` is positive. This is about the single matrix `W`; it is
deliberately not a general statement about determinants of `SL`-type elements. -/
public theorem frickeGL_det_pos : 0 < (frickeGL N).det.val := by
  have : (frickeGL N).det.val = (N : ℚ) := by simp
  rw [this]
  exact_mod_cast NeZero.pos N

/-- `W⁻¹ = !![0, 1/N; -1, 0]`.

Deliberately not `@[simp]`: `Matrix.coe_units_inv` is itself `simp`, so simp rewrites this
left-hand side to `(!![0, -1; N, 0])⁻¹` and it is not in simp-normal form. -/
public theorem coe_frickeGL_inv :
    (↑(frickeGL N)⁻¹ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1 / (N : ℚ); -1, 0] := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, coe_frickeGL, Matrix.adjugate_fin_two_of,
    Ring.inverse_eq_inv]
  simp [Matrix.det_fin_two_of, NeZero.ne (N : ℚ)]

/-- `W² = (-N) • 1` as matrices. This is the entrywise identity the Fricke operator's
involution property consumes; it is not itself a statement that `W²` is central in `GL`.

Deliberately not `@[simp]`: `Units.val_mul` is `simp`, so simp already carries this left-hand
side all the way to the entry-level normal form `!![-N, 0; 0, -N]`. The lemma exists for the
`(-N) • 1` packaging, which is not that normal form, so tagging it would put a non-normal
left-hand side in the simp set. -/
public theorem coe_frickeGL_sq :
    (↑(frickeGL N * frickeGL N) : Matrix (Fin 2) (Fin 2) ℚ) =
      (-(N : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  rw [Units.val_mul, coe_frickeGL, Matrix.mul_fin_two]
  simp [Matrix.one_fin_two]

end TauCeti
