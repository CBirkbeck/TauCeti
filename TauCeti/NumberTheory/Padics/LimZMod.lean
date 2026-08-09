/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Ring.Pi

/-!
# The `p`-adic integers as the projective limit of the `ZMod` tower

`ℤ_[p]` is the projective limit of `… → ZMod (p ^ (n + 1)) → ZMod (p ^ n) → …` along the
canonical reductions. Mathlib supplies the universal property of `ℤ_[p]` — `PadicInt.lift`,
`PadicInt.lift_spec` and `PadicInt.ext_of_toZModPow` — but not the limit itself as an object,
so the isomorphism cannot be stated without first naming the limit.

`compatSubring p` is that object: the compatible sequences, as a subring of `Π n, ZMod (p ^ n)`.
Its element type is definitionally the projective-limit subtype

`{f : Π n, ZMod (p ^ n) // ∀ n, ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p ^ n))
  (f (n + 1)) = f n}`,

so `mem_compatSubring` is `Iff.rfl` and a compatible sequence may be handed to
`compatSubring p` directly.

## Main definitions

* `PadicInt.compatSubring`: the subring of compatible sequences in `Π n, ZMod (p ^ n)`.
* `PadicInt.compatProj`: the `n`-th projection out of it, as a ring hom.

## Main results

* `PadicInt.equivLimZMod`: `ℤ_[p] ≃+* compatSubring p`.
* `PadicInt.compat_of_adjacentCompat`: adjacent compatibility gives compatibility for all
  `k₁ ≤ k₂`, which is what `PadicInt.lift` requires of the projection family.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
pinned by `TauCetiRoadmap/EllipticCurves` at `dev/hasse-weil @ 513e83879e2f`), file
`HasseWeil/TateModule/PadicLimZMod.lean`, declarations `limZModCast`,
`adjacentCompat_of_compat`, `compat_of_adjacentCompat`, `compatSubring`, `mem_compatSubring`,
`compatProj`, `compatProj_compat`, `limZModToPadic`, `padicToLimZMod`, `compatProj_apply`,
`padicToLimZMod_val`, `toZModPow_limZModToPadic` and `padicIntEquivLimZMod` (© Chris Birkbeck).
Following this repository's convention for adapted material, the upstream authorship is
credited here rather than in the copyright header.

Changes in porting: the prime is `p` rather than `ℓ`, and the declarations live in Mathlib's
`PadicInt` namespace rather than a project-specific one, since nothing here is about elliptic
curves — the source needs this for the Tate module (Silverman III.7), but the statement is
about `ℤ_[p]` alone. The source's `padicIntEquivLimZMod` is `equivLimZMod` here, the `PadicInt`
prefix being supplied by the namespace.
-/

public section

namespace PadicInt

variable (p : ℕ) [Fact p.Prime]

/-- The connecting reduction `ZMod (p ^ (n + 1)) →+* ZMod (p ^ n)` of the tower. -/
abbrev limZModCast (n : ℕ) : ZMod (p ^ (n + 1)) →+* ZMod (p ^ n) :=
  ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p ^ n))

omit [Fact p.Prime] in
/-- Compatibility for all `k₁ ≤ k₂` implies compatibility of adjacent terms. -/
theorem adjacentCompat_of_compat {f : ∀ n : ℕ, ZMod (p ^ n)}
    (h : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁)) (f k₂) = f k₁) (n : ℕ) :
    limZModCast p n (f (n + 1)) = f n :=
  h n (n + 1) n.le_succ

omit [Fact p.Prime] in
/-- Compatibility of adjacent terms implies compatibility for all `k₁ ≤ k₂`. -/
theorem compat_of_adjacentCompat {f : ∀ n : ℕ, ZMod (p ^ n)}
    (h : ∀ n, limZModCast p n (f (n + 1)) = f n) (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁)) (f k₂) = f k₁ := by
  -- Telescope down the tower: each step composes one connecting reduction onto the cast.
  induction k₂, hk using Nat.le_induction with
  | base => simp [ZMod.castHom_self]
  | succ k₂ hk ih =>
    have hstep : ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁))
        (limZModCast p k₂ (f (k₂ + 1))) = f k₁ := by rw [h k₂]; exact ih
    rw [← hstep, limZModCast, ← RingHom.comp_apply, ZMod.castHom_comp]

/-- The subring of compatible sequences in `Π n, ZMod (p ^ n)` — the projective limit of the
`ZMod` tower. Its element type is definitionally the subtype of sequences satisfying the
displayed compatibility condition, so `mem_compatSubring` is `Iff.rfl`. -/
def compatSubring : Subring (∀ n : ℕ, ZMod (p ^ n)) where
  carrier := {f | ∀ n, ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p ^ n)) (f (n + 1)) = f n}
  mul_mem' {f g} hf hg n := by simp only [Pi.mul_apply, map_mul, hf n, hg n]
  one_mem' n := by simp only [Pi.one_apply, map_one]
  add_mem' {f g} hf hg n := by simp only [Pi.add_apply, map_add, hf n, hg n]
  zero_mem' n := by simp only [Pi.zero_apply, map_zero]
  neg_mem' {f} hf n := by simp only [Pi.neg_apply, map_neg, hf n]

omit [Fact p.Prime] in
@[simp] theorem mem_compatSubring (f : ∀ n : ℕ, ZMod (p ^ n)) :
    f ∈ compatSubring p ↔
      ∀ n, ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p ^ n)) (f (n + 1)) = f n := Iff.rfl

/-- The `n`-th projection out of the limit, as a ring hom. -/
def compatProj (n : ℕ) : compatSubring p →+* ZMod (p ^ n) :=
  (Pi.evalRingHom (fun n : ℕ => ZMod (p ^ n)) n).comp (compatSubring p).subtype

omit [Fact p.Prime] in
/-- The projections commute with the tower's connecting maps, which is the hypothesis
`PadicInt.lift` requires. -/
theorem compatProj_compat (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁))).comp (compatProj p k₂) = compatProj p k₁ := by
  ext x
  simpa only [RingHom.comp_apply, compatProj, Pi.evalRingHom_apply, RingHom.coe_comp,
    Function.comp_apply, Subring.coe_subtype]
    using compat_of_adjacentCompat p x.property k₁ k₂ hk

/-- The map out of the limit into `ℤ_[p]`, from the universal property. -/
noncomputable def limZModToPadic : compatSubring p →+* ℤ_[p] :=
  PadicInt.lift (f := compatProj p) (compatProj_compat p)

/-- The map into the limit: `z ↦ (n ↦ toZModPow n z)`. -/
noncomputable def padicToLimZMod : ℤ_[p] →+* compatSubring p :=
  RingHom.codRestrict (RingHom.pi fun n : ℕ => PadicInt.toZModPow n) (compatSubring p)
    fun z n => RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) n.le_succ) z

omit [Fact p.Prime] in
@[simp] theorem compatProj_apply (n : ℕ) (x : compatSubring p) : compatProj p n x = x.val n :=
  (rfl)

@[simp] theorem padicToLimZMod_val (z : ℤ_[p]) (n : ℕ) :
    (padicToLimZMod p z).val n = PadicInt.toZModPow n z :=
  (rfl)

@[simp] theorem toZModPow_limZModToPadic (n : ℕ) (x : compatSubring p) :
    PadicInt.toZModPow n (limZModToPadic p x) = x.val n := by
  simpa [limZModToPadic, compatProj]
    using RingHom.congr_fun (PadicInt.lift_spec (f := compatProj p) (compatProj_compat p) n) x

/-- **`ℤ_[p]` is the projective limit of the `ZMod` tower.** -/
noncomputable def equivLimZMod : ℤ_[p] ≃+* compatSubring p :=
  RingEquiv.ofRingHom (padicToLimZMod p) (limZModToPadic p)
    (by ext x n; simp)
    (by ext z; exact PadicInt.ext_of_toZModPow.mp fun n => by simp)

end PadicInt
