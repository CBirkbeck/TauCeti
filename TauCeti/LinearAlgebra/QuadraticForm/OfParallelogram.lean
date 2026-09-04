/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# A function satisfying the parallelogram law is a quadratic form

Let `M` and `N` be additive commutative groups and `f : M → N` satisfy the **parallelogram law**

```
f (x + y) + f (x - y) = 2 • f x + 2 • f y.
```

Then `f` is a quadratic form: its polarisation `QuadraticMap.polar f x y = f (x + y) - f x - f y`
is biadditive, and `f (n • x) = n ^ 2 • f x`. This file proves that, and packages it as a
`QuadraticMap ℤ M N`. Both `f 0 = 0` and evenness of `f` come free from the law rather than being
assumed.

Mathlib has the converse direction — `QuadraticMap.polar_add_left` and friends read biadditivity
*off* a `QuadraticMap`, and `LinearMap.BilinMap.toQuadraticMap` builds one from a bilinear map —
but nothing in the other direction from the parallelogram law alone. Its `parallelogram_law` and
`parallelogram_law_with_norm` are statements about inner product spaces, and the Jordan–von Neumann
construction in `Analysis/InnerProductSpace/OfNorm.lean` recovers an inner product from a *norm* on
a real or complex space, using continuity. Neither applies to a function on a bare abelian group.

## The torsion hypothesis is necessary, not defensive

`N` is assumed `IsAddTorsionFree`. The derivation of the three-variable identity
`map_add_add_of_parallelogram` produces it doubled — four instances of the parallelogram law
combine to `2 • LHS = 2 • RHS` — and halving is the only step that needs anything of `N`.

It cannot be dropped. With `M = N = ZMod 2` *every* function satisfies the parallelogram law,
because `x - y = x + y` and `2 • z = 0` there; the constant function `1` is then one that satisfies
it while failing even `f 0 = 0`, which every quadratic form obeys. So the hypothesis is what makes
the conclusion true, not merely what makes this proof work.

## Main results

* `TauCeti.QuadraticMap.map_zero_of_parallelogram` and
  `TauCeti.QuadraticMap.map_neg_of_parallelogram`: `f 0 = 0` and `f (-x) = f x` come free from the
  law; neither has to be assumed.
* `TauCeti.QuadraticMap.map_add_add_of_parallelogram`: the three-variable identity
  `f (x + y + z) + f x + f y + f z = f (x + y) + f (y + z) + f (x + z)`. This is the whole
  content — biadditivity is a rearrangement of it.
* `TauCeti.QuadraticMap.polar_add_left_of_parallelogram` and `polar_add_right_of_parallelogram`:
  the polarisation is biadditive.
* `TauCeti.QuadraticMap.map_zsmul_of_parallelogram`: `f (n • x) = n ^ 2 • f x` for `n : ℤ`,
  written `(n * n) • f x` to match `QuadraticMap`'s `toFun_smul` field.
* `TauCeti.QuadraticMap.ofParallelogram`: the resulting `QuadraticMap ℤ M N`, whose companion
  bilinear map is the polarisation.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 names "the Néron–Tate bilinear pairing" as a
milestone, and the pairing is exactly the polarisation of the canonical height, which is known to
satisfy the parallelogram law (`WeierstrassCurve.Affine.Point.canonicalHeight_parallelogram_law`)
before it is known to be quadratic. The same shape recurs for the degree form on `End E` behind the
Hasse bound (§Layer 3, AEC V.1.2). Stated here for a general abelian group so that neither
application carries its own copy.
-/

public section

namespace TauCeti

namespace QuadraticMap

open _root_.QuadraticMap

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [IsAddTorsionFree N] {f : M → N}
  (hf : ∀ x y : M, f (x + y) + f (x - y) = 2 • f x + 2 • f y)

include hf

/-- The parallelogram law at `x = y = 0` forces `f 0 = 0`. -/
theorem map_zero_of_parallelogram : f 0 = 0 := by
  have h := hf 0 0
  simp only [add_zero, sub_zero] at h
  refine smul_right_injective N (r := (2 : ℤ)) (by norm_num) ?_
  change (2 : ℤ) • f 0 = (2 : ℤ) • 0
  linear_combination (norm := module) -h

/-- The parallelogram law at `x = 0` forces `f` to be even. -/
theorem map_neg_of_parallelogram (x : M) : f (-x) = f x := by
  have h := hf 0 x
  rw [zero_add, zero_sub, map_zero_of_parallelogram hf] at h
  linear_combination (norm := module) h

/-- **The three-variable identity.** A quadratic form satisfies
`f (x + y + z) = f (x + y) + f (y + z) + f (x + z) - f x - f y - f z`, and the parallelogram law
already implies it. Biadditivity of the polarisation is a rearrangement of this, so it is the
substantive step. -/
theorem map_add_add_of_parallelogram (x y z : M) :
    f (x + y + z) + f x + f y + f z = f (x + y) + f (y + z) + f (x + z) := by
  -- Four instances of the law. `x + z - y` and `x - (y - z)` are the same point, which is what
  -- lets the two occurrences of `f` at that point cancel; halving at the end is the only place
  -- torsion-freeness is used.
  have h1 := hf (x + y) z
  have h2 := hf x (y - z)
  have h3 := hf y z
  have h4 := hf (x + z) y
  rw [show x + y - z = x + (y - z) by abel] at h1
  rw [show x - (y - z) = x + z - y by abel] at h2
  rw [show x + z + y = x + y + z by abel] at h4
  refine smul_right_injective N (r := (2 : ℤ)) (by norm_num) ?_
  change (2 : ℤ) • (f (x + y + z) + f x + f y + f z)
      = (2 : ℤ) • (f (x + y) + f (y + z) + f (x + z))
  linear_combination (norm := module) h1 + h4 - h2 - (2 : ℤ) • h3

/-- **The polarisation is additive in its left argument.** -/
theorem polar_add_left_of_parallelogram (x x' y : M) :
    polar f (x + x') y = polar f x y + polar f x' y := by
  simp only [polar]
  linear_combination (norm := module) map_add_add_of_parallelogram hf x x' y

/-- **The polarisation is additive in its right argument**, by symmetry. -/
theorem polar_add_right_of_parallelogram (x y y' : M) :
    polar f x (y + y') = polar f x y + polar f x y' := by
  rw [polar_comm, polar_comm f x y, polar_comm f x y']
  exact polar_add_left_of_parallelogram hf y y' x

/-- Quadraticity for a natural multiple. Stated with an **integer** scalar on the right so that
the induction step is a `ring` identity in `ℤ`: over `ℕ` it would read
`(n + 2) ^ 2 = 2 (n + 1) ^ 2 + 2 - n ^ 2`, and truncated subtraction is not a ring. -/
private theorem map_nsmul_of_parallelogram (n : ℕ) (x : M) :
    f (n • x) = ((n : ℤ) * n) • f x := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using map_zero_of_parallelogram hf
  | one => simp
  | more n ih ih' =>
    -- the parallelogram law at `((n + 1) • x, x)` expresses the value at `(n + 2) • x`
    have h := hf ((n + 1) • x) x
    rw [← succ_nsmul x (n + 1), show (n + 1) • x - x = n • x by
      rw [succ_nsmul, add_sub_cancel_right], ih, ih'] at h
    push_cast at h ⊢
    linear_combination (norm := module) h

/-- **Quadraticity**: `f (n • x) = n ^ 2 • f x`, written `(n * n) • f x` to match the
`toFun_smul` field of `QuadraticMap`. The negative case is the natural one composed with
`map_neg_of_parallelogram`. -/
theorem map_zsmul_of_parallelogram (n : ℤ) (x : M) : f (n • x) = (n * n) • f x := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [natCast_zsmul, map_nsmul_of_parallelogram hf]
  · rw [neg_zsmul, natCast_zsmul, map_neg_of_parallelogram hf,
      map_nsmul_of_parallelogram hf, neg_mul_neg]

/-- The polarisation, as an additive homomorphism in its right argument. -/
def polarAddHomRight (x : M) : M →+ N :=
  AddMonoidHom.mk' (polar f x) fun a b ↦ polar_add_right_of_parallelogram hf x a b

/-- **The polarisation as a `ℤ`-bilinear map.** Additivity is all that has to be supplied:
`M` and `N` are abelian groups, so an additive map between them is automatically `ℤ`-linear. -/
noncomputable def polarBilinInt : LinearMap.BilinMap ℤ M N :=
  (AddMonoidHom.mk' (fun x ↦ (polarAddHomRight hf x).toIntLinearMap)
    fun a b ↦ by
      ext y
      exact polar_add_left_of_parallelogram hf a b y).toIntLinearMap

@[simp]
theorem polarBilinInt_apply (x y : M) : polarBilinInt hf x y = polar f x y := by
  -- not `rfl`: an *exported* `rfl` theorem needs every definition it unfolds to be `@[expose]`d,
  -- and a tactic proof exports a proof term instead of a defeq obligation
  simp [polarBilinInt, polarAddHomRight]

/-- **A function satisfying the parallelogram law is a quadratic form**, with the polarisation as
its companion bilinear map. -/
noncomputable def ofParallelogram : _root_.QuadraticMap ℤ M N where
  toFun := f
  toFun_smul := map_zsmul_of_parallelogram hf
  exists_companion' := ⟨polarBilinInt hf, fun x y ↦ by
    rw [polarBilinInt_apply, polar]
    abel⟩

@[simp]
theorem ofParallelogram_apply (x : M) : ofParallelogram hf x = f x := by
  simp [ofParallelogram]

end QuadraticMap

end TauCeti
