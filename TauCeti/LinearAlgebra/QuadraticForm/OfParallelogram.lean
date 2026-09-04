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

## The hypothesis is exactly the absence of `2`-torsion

`htwo : IsSMulRegular N 2` says that doubling is injective on `N`, and that is precisely what the
proofs consume. The three-variable identity `map_add_add_of_parallelogram` comes out **doubled** —
four instances of the parallelogram law combine to `2 • LHS = 2 • RHS` — and halving is the only
step in the file that uses anything of `N` at all.

It is deliberately *not* `IsAddTorsionFree N`, which is strictly stronger and would exclude
codomains where the construction is perfectly valid: `IsSMulRegular (ZMod 3) 2` holds even though
`ZMod 3` has `3`-torsion.

Nor can it be dropped. With `M = N = ZMod 2` *every* function satisfies the parallelogram law,
because `x - y = x + y` and `2 • z = 0` there; the constant function `1` is then one that satisfies
it while failing even `f 0 = 0`, which every quadratic form obeys — and correspondingly
`¬ IsSMulRegular (ZMod 2) 2`. So the hypothesis is what makes the conclusion true, not merely what
makes this proof work.

For a torsion-free codomain it is one term: `smul_right_injective N two_ne_zero` supplies it for
`N = ℝ`, the canonical height's target, and for `N = ℤ`, the degree form's.

## Main results

* `TauCeti.QuadraticMap.map_zero_of_parallelogram` and
  `TauCeti.QuadraticMap.map_neg_of_parallelogram`: `f 0 = 0` and `f (-x) = f x` come free from the
  law; neither has to be assumed.
* `TauCeti.QuadraticMap.map_add_add_of_parallelogram`: the three-variable identity
  `f (x + y + z) + f x + f y + f z = f (x + y) + f (y + z) + f (x + z)`. This is the whole
  content — biadditivity is a rearrangement of it.
* `TauCeti.QuadraticMap.polar_add_left_of_parallelogram` and
  `polar_zsmul_left_of_parallelogram`: the polarisation is additive and `ℤ`-linear on the left.
  Additivity on the right is not restated — it is `QuadraticMap.polar_add_right` of the packaged
  map below.
* `TauCeti.QuadraticMap.map_zsmul_of_parallelogram`: `f (n • x) = n ^ 2 • f x` for `n : ℤ`,
  written `(n * n) • f x` to match `QuadraticMap`'s `toFun_smul` field.
* `TauCeti.QuadraticMap.ofParallelogram`: the resulting `QuadraticMap ℤ M N`, built with
  `QuadraticMap.ofPolar`. Its companion bilinear map is `QuadraticMap.polarBilin` of it, which is
  the polarisation.

## Where this is used

Two constructions in arithmetic geometry arrive at a function *known to satisfy the parallelogram
law* and want it as a quadratic form.

The canonical height of an elliptic curve is one: `canonicalHeight_parallelogram_law` establishes
the law exactly, and the Néron–Tate height pairing is then the polarisation supplied here — the
bilinear map whose Gram determinant on a basis is the regulator. The degree form on `End E` is the
other, where the polarisation is the trace form and its non-negativity gives the Hasse bound by
Cauchy–Schwarz (Silverman, *AEC*, V.1.2).

Both take values in a torsion-free group — `ℝ` and `ℤ` respectively — so both satisfy the
hypothesis below with room to spare. Stated for a general abelian group so that neither carries
its own copy.
-/

public section

namespace TauCeti

namespace QuadraticMap

open _root_.QuadraticMap

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] {f : M → N}
  (htwo : IsSMulRegular N (2 : ℕ))
  (hf : ∀ x y : M, f (x + y) + f (x - y) = 2 • f x + 2 • f y)

include htwo hf

/-- The parallelogram law at `x = y = 0` forces `f 0 = 0`. -/
theorem map_zero_of_parallelogram : f 0 = 0 := by
  have h := hf 0 0
  simp only [add_zero, sub_zero] at h
  apply htwo
  linear_combination (norm := module) -h

/-- The parallelogram law at `x = 0` forces `f` to be even. -/
theorem map_neg_of_parallelogram (x : M) : f (-x) = f x := by
  have h := hf 0 x
  rw [zero_add, zero_sub, map_zero_of_parallelogram htwo hf] at h
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
  have p1 := hf (x + y) z
  have p2 := hf x (y - z)
  have p3 := hf y z
  have p4 := hf (x + z) y
  -- `f` is an arbitrary function, so `abel` cannot normalise *under* it: the arguments have to be
  -- rewritten explicitly before the four instances share syntactic subterms and can be combined.
  rw [show x + y - z = x + (y - z) by abel] at p1
  rw [show x - (y - z) = x + z - y by abel] at p2
  rw [show x + z + y = x + y + z by abel] at p4
  apply htwo
  linear_combination (norm := module) p1 + p4 - p2 - (2 : ℤ) • p3

/-- **The polarisation is additive in its left argument.** -/
theorem polar_add_left_of_parallelogram (x x' y : M) :
    polar f (x + x') y = polar f x y + polar f x' y := by
  simp only [polar]
  linear_combination (norm := module) map_add_add_of_parallelogram htwo hf x x' y

/-- **The polarisation is `ℤ`-linear in its left argument.** No new content: an additive map
between abelian groups is automatically `ℤ`-linear, and this is that fact applied to
`polar_add_left_of_parallelogram`. It is the last input `QuadraticMap.ofPolar` asks for.

Additivity on the *right* is not stated separately: it is `QuadraticMap.polar_add_right` of the
packaged `ofParallelogram` below. -/
theorem polar_zsmul_left_of_parallelogram (a : ℤ) (x y : M) :
    polar f (a • x) y = a • polar f x y :=
  AddMonoidHom.map_zsmul
    (AddMonoidHom.mk' (polar f · y) fun p q ↦ polar_add_left_of_parallelogram htwo hf p q y) a x

/-- Quadraticity for a natural multiple. Stated with an **integer** scalar on the right so that
the induction step is a `ring` identity in `ℤ`: over `ℕ` it would read
`(n + 2) ^ 2 = 2 (n + 1) ^ 2 + 2 - n ^ 2`, and truncated subtraction is not a ring. -/
private theorem map_nsmul_of_parallelogram (n : ℕ) (x : M) :
    f (n • x) = ((n : ℤ) * n) • f x := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using map_zero_of_parallelogram htwo hf
  | one => simp
  | more n ih ih' =>
    -- the parallelogram law at `((n + 1) • x, x)` expresses the value at `(n + 2) • x`
    have h := hf ((n + 1) • x) x
    -- again the arguments of `f`, not the ambient expression, are what must be reshaped
    rw [← succ_nsmul x (n + 1), show (n + 1) • x - x = n • x by
      rw [succ_nsmul, add_sub_cancel_right], ih, ih'] at h
    push_cast at h ⊢
    linear_combination (norm := module) h

/-- **Quadraticity**: `f (n • x) = n ^ 2 • f x`, written `(n * n) • f x` to match the
`toFun_smul` field of `QuadraticMap`. The negative case is the natural one composed with
`map_neg_of_parallelogram`. -/
theorem map_zsmul_of_parallelogram (n : ℤ) (x : M) : f (n • x) = (n * n) • f x := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [natCast_zsmul, map_nsmul_of_parallelogram htwo hf]
  · rw [neg_zsmul, natCast_zsmul, map_neg_of_parallelogram htwo hf,
      map_nsmul_of_parallelogram htwo hf, neg_mul_neg]

/-- **A function satisfying the parallelogram law is a quadratic form.**

Built with Mathlib's `QuadraticMap.ofPolar`, which asks for exactly the three facts above and
assembles the companion bilinear map itself; `QuadraticMap.polarBilin` of the result is that map,
so there is no separate bilinear-map definition here. -/
noncomputable def ofParallelogram : _root_.QuadraticMap ℤ M N :=
  .ofPolar f (map_zsmul_of_parallelogram htwo hf) (polar_add_left_of_parallelogram htwo hf)
    (polar_zsmul_left_of_parallelogram htwo hf)

/-- `ofParallelogram` coerces back to the function it was built from. Stated at the level of
functions, not just pointwise: `QuadraticMap.polar` takes the *function* as its argument, so this
is the form needed to rewrite `polar ⇑(ofParallelogram htwo hf)` to `polar f` and reach Mathlib's
polar API — checked downstream rather than assumed. -/
@[simp]
theorem coe_ofParallelogram : (ofParallelogram htwo hf : M → N) = f := by
  unfold ofParallelogram
  rfl

@[simp]
theorem ofParallelogram_apply (x : M) : ofParallelogram htwo hf x = f x := by
  simp

end QuadraticMap

end TauCeti
