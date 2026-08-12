/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# The invariant of an elliptic net

An elliptic net `W : ℤ → R` carries, for each `s`, a quantity that does not depend on `n`:
the ratio of

* `IsEllipticNet.invarNum W s n
    = (W (n + 2s) * W (n - s)² + W (n + s)² * W (n - 2s)) * W s² + W n³ * W (2s)²`, and
* `IsEllipticNet.invarDenom W s n = W (n + s) * W n * W (n - s)`.

`R` is only a commutative ring, so the ratio itself need not exist; the statement is therefore the
cross-multiplied one,

`invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m`,

which is `IsEllipticNet.invarNum_mul_invarDenom`. Over a field, on any set of indices where
`invarDenom W s ·` is nonvanishing, it says exactly that `n ↦ invarNum/invarDenom` is constant
there: the hypothesis is `IsEllipticNet W`, and cancelling the identity at a pair `m, n` needs both
`invarDenom W s m` and `invarDenom W s n` to be nonzero, not just one of them. When `W` is the
division-polynomial sequence of a Weierstrass curve, that constant is a coordinate of the point
being multiplied — which is what makes the invariant the bridge between the elliptic-net identities
and the curve.

## Main definitions

* `IsEllipticNet.invarNum` and `IsEllipticNet.invarDenom` are defined for an **arbitrary**
  sequence `W : ℤ → R` — no hypothesis on `W`, and nothing about Weierstrass curves. It is the
  *theorem* that asks `W` to be an elliptic net (or, in the primed form, asks the relator to
  vanish); the file proves that direction only, and states no converse.
* `IsEllipticNet.invarNum_def`, `IsEllipticNet.invarDenom_def`: the defining formulas, as public
  equation lemmas. The definition bodies are not exposed, so these are how a consumer computes
  with them.

## Main results

* `IsEllipticNet.invarNum_mul_invarDenom_of_rel`: the invariance identity, from the vanishing of
  the elliptic relator `IsEllipticNet.rel` alone. Stated this way rather than from
  `IsEllipticNet W` because only four instances of the relator are used, and consumers that have
  the relator vanishing for other reasons can apply it directly.
* `IsEllipticNet.invarNum_mul_invarDenom`: the same for an elliptic net.
* `IsEllipticNet.map_invarNum`, `IsEllipticNet.map_invarDenom`: both are natural in `R`. These are
  deliberately not `@[simp]` — the `_def` equations are, and `simp` derives naturality from them.

## Implementation notes

The numerator is *not* symmetric in the two terms it pairs, and the `W s ^ 2` and `W (2 * s) ^ 2`
weights are not decoration: they are what makes the identity hold over a ring with zero divisors,
where one cannot divide through.

## Provenance

Ported from J. Xu's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declarations `invarNum`, `invarDenom` and
`invar_of_net`. That file's header reads `Authors: Junyan Xu`; following this repository's
convention for adapted material the upstream authorship is credited here rather than in the
copyright header.

The same three declarations sit in **Mathlib PR #13057** (open, last updated 2024-07-31), which is
the upstreaming of that AINTLIB file; this port uses that PR's naming
(`invarNum_mul_invarDenom`, from its sibling PR #13155) rather than the source's `invar_of_net`,
so that deduplication when it lands is a deletion rather than a rename. It could not be copied
from #13057 unchanged: that PR predates Mathlib's rename of the elliptic-net API, and is written
against `net`/`addMulSub`/`rel₄`, which are now `IsEllipticNet.rel`, `IsEllipticNet.atom` and
`IsEllipticNet.atomRel`. The definitions are otherwise character-for-character identical, so the
restatement here is purely the rename.
-/

public section

namespace IsEllipticNet

variable {R S : Type*} [CommRing R] [CommRing S] (W : ℤ → R)

/-- The numerator of the invariant of an elliptic net: for each `s`, the ratio
`invarNum W s n / invarDenom W s n` does not depend on `n`
(`invarNum_mul_invarDenom`, cross-multiplied so as to make sense over any commutative ring). -/
def invarNum (s n : ℤ) : R :=
  (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
    + W n ^ 3 * W (2 * s) ^ 2

/-- The defining formula for `invarNum`. The definition body is not exposed, so this equation
lemma is how a consumer computes with it. -/
@[simp]
theorem invarNum_def (s n : ℤ) : invarNum W s n =
    (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
      + W n ^ 3 * W (2 * s) ^ 2 := (rfl)

/-- The denominator of the invariant of an elliptic net, `W (n + s) * W n * W (n - s)`. -/
def invarDenom (s n : ℤ) : R := W (n + s) * W n * W (n - s)

/-- The defining formula for `invarDenom`. The definition body is not exposed, so this equation
lemma is how a consumer computes with it. -/
@[simp]
theorem invarDenom_def (s n : ℤ) : invarDenom W s n = W (n + s) * W n * W (n - s) := (rfl)

variable {W} in
/-- **The invariant of an elliptic net does not depend on `n`**, in the cross-multiplied form that
makes sense over a commutative ring.

Only four instances of the relator are used, so the hypothesis is its vanishing rather than
`IsEllipticNet W`; `invarNum_mul_invarDenom` is the packaged version. -/
theorem invarNum_mul_invarDenom_of_rel (hrel : ∀ p q r s, rel W p q r s = 0) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m := by
  simp_rw [invarNum, invarDenom]
  linear_combination (norm := (simp_rw [rel]; ring_nf))
    hrel m n s 0 * W m * W n * W (2 * s) ^ 2
      - (hrel m n s s * W (m - s) * W (n - s)
        + hrel (m - s) (n - s) s s * W (m + s) * W (n + s)
        - hrel (n + s) n (n - s) (m - n) * W (m - n) * W (2 * s)) * W s ^ 2

variable {W} in
/-- **The invariant of an elliptic net does not depend on `n`.** -/
theorem invarNum_mul_invarDenom (h : IsEllipticNet W) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m :=
  invarNum_mul_invarDenom_of_rel h s m n

variable {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)

/-- The numerator of the invariant is natural in the coefficient ring.

Not `@[simp]`: with `invarNum_def` tagged, `simp` derives this from it together with `map_add`,
`map_mul`, `map_pow` and `Function.comp_apply`, so tagging it too is a `simpNF` duplicate. It
stays as a named fact for use by hand. -/
theorem map_invarNum (s n : ℤ) : f (invarNum W s n) = invarNum (f ∘ W) s n := by
  simp only [invarNum, map_add, map_mul, map_pow, Function.comp_apply]

/-- The denominator of the invariant is natural in the coefficient ring.

Not `@[simp]`, for the same reason as `map_invarNum`: `invarDenom_def` and `map_mul` derive it. -/
theorem map_invarDenom (s n : ℤ) : f (invarDenom W s n) = invarDenom (f ∘ W) s n := by
  simp only [invarDenom, map_mul, Function.comp_apply]

end IsEllipticNet
