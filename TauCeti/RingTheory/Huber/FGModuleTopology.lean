/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-!
# The topology induced by the `ϖⁿ • M₀` basis on a module over a Tate ring

Let `A` be a Tate ring, `A₀` a ring of definition, `ϖ ∈ A₀` a pseudouniformiser, and `M₀` an
`A₀`-submodule of an `A`-module `M` with `A · M₀ = M`. This file exhibits the family `ϖⁿ • M₀`
as a `SubmodulesBasis`, which is Mathlib's machinery for turning such a family into a topology;
`SubmodulesBasis.topology` and `.nonarchimedean` then apply.

**What is proved here is the basis, not an identification.** Wedhorn's Remark 6.19 says this
family is a fundamental system of neighbourhoods of `0` for *the* topology of his Proposition
6.18(1), and 6.18(1) asserts that topology is the unique complete first-countable `A`-module
topology. Neither the uniqueness nor the identification is proved below, so nothing here may be
called *the* canonical topology yet.

**The hypotheses are weaker than Wedhorn's, deliberately.** Remark 6.19 assumes `A` noetherian
and `M₀` finitely generated; no declaration below uses either — only `A · M₀ = M`. Finite
generation first does work one layer up, where a single exponent has to serve a whole submodule.

## Main results

* `TauCeti.Huber.PairOfDefinition.pow_add_smul_mem`: `M₀` absorbs further powers of `ϖ`.
* `TauCeti.Huber.PairOfDefinition.exists_pow_smul_mem`: a power of `ϖ` carries any element of
  the `A`-span of `M₀` into `M₀`.
* `TauCeti.Huber.PairOfDefinition.powSmulFamily_submodulesBasis`: the family is a
  `SubmodulesBasis`.
* `TauCeti.Huber.PairOfDefinition.mem_powSmulFamily`: the membership characterisation, and the
  route by which any other module reasons about the family at all.

## Implementation notes

The neighbourhoods are `A₀`-submodules, not `A`-submodules, so `SubmodulesBasis` is instantiated
at `R := P.ringOfDefinition`: `M` carries its `A₀`-module structure by restriction of scalars
along `A₀ → A`, which typeclass inference supplies unaided.

`powSmulFamily` is a plain `def`, not `@[expose]`d, so its body is visible only inside this
file. Every proof below therefore sees through it, but no other module does; `mem_powSmulFamily`
and `powSmulFamily_def` are the intended routes out, and reaching for `@[expose]` instead would
make an implementation composite public without leaving any API behind.

The family is `ϖⁿ • M₀` rather than `Iⁿ • M₀` for the ideal of definition `I`. That is Wedhorn's
own indexing, and it is what the proofs below run on: both `exists_pow_smul_mem` and
`powSmulFamily_smul` consume the pseudouniformiser's own neighbourhood basis,
`TauCeti.Huber.IsPseudoUniformizer.hasBasis_nhds_zero`. This is a choice of presentation and not
a constraint — nothing here shows an `I`-indexed family would fail.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 6.18 and
  Remark 6.19.
-/

public section

open Filter
open scoped Topology Pointwise

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M]

omit [IsTopologicalRing A] in
/-- **Wedhorn's Remark 6.19 family**: the `A₀`-submodules `ϖⁿ • M₀` of `M`. -/
def powSmulFamily (P : PairOfDefinition A) {s : A} (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (n : ℕ) : Submodule P.ringOfDefinition M :=
  ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n) • M₀

omit [IsTopologicalRing A] in
/-- **Unfolding lemma for the family.** The definition is not `@[expose]`d, so a downstream file
that needs to see `ϖⁿ • M₀` as a pointwise scalar multiple — to destructure a membership, or to
feed `Submodule.smul_mem_pointwise_smul` — rewrites with this first. -/
theorem powSmulFamily_def (P : PairOfDefinition A) {s : A} (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (n : ℕ) :
    P.powSmulFamily hs0 M₀ n = ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n) • M₀ := (rfl)

omit [IsTopologicalRing A] in
/-- **Membership in the family.** This is the characterisation a consumer should use: it
introduces and eliminates `x ∈ ϖⁿ • M₀` without ever unfolding `powSmulFamily`, whose body is
not exposed outside this file. -/
@[simp]
theorem mem_powSmulFamily (P : PairOfDefinition A) {s : A} (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (n : ℕ) {x : M} :
    x ∈ P.powSmulFamily hs0 M₀ n ↔
      ∃ y ∈ M₀, ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n) • y = x := by
  rw [powSmulFamily_def]
  exact Submodule.mem_smul_pointwise_iff_exists _ _ _

omit [IsTopologicalRing A] in
/-- The family is antitone, which is the `inter` half of `SubmodulesBasis`. -/
theorem powSmulFamily_antitone (P : PairOfDefinition A) {s : A} (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) : Antitone (P.powSmulFamily hs0 M₀) := by
  intro i j hij
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨((⟨s, hs0⟩ : P.ringOfDefinition) ^ d) • y, M₀.smul_mem _ hy, ?_⟩
  simp [smul_smul, ← pow_add, Nat.add_comm]

/-- Some power of a topologically nilpotent `s` carries any `c : A` into the ring of
definition — the ring of definition is open, and `sⁿ c → 0`. -/
theorem exists_pow_mul_mem (P : PairOfDefinition A) {s : A} (hs : IsTopologicallyNilpotent s)
    (c : A) : ∃ i : ℕ, s ^ i * c ∈ P.ringOfDefinition :=
  ((hs.mul_const c).eventually
    (P.isOpen_ringOfDefinition.mem_nhds (by simp))).exists

omit [IsTopologicalRing A] in
/-- `M₀` absorbs further powers of `s`: raising the exponent cannot leave it, because the extra
factor is itself a scalar from `A₀`. -/
theorem pow_add_smul_mem (P : PairOfDefinition A) {s : A} (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (j k : ℕ) (z : M) (hz : s ^ k • z ∈ M₀) :
    s ^ (j + k) • z ∈ M₀ := by
  have he : s ^ (j + k) • z = (⟨s, hs0⟩ : P.ringOfDefinition) ^ j • (s ^ k • z) := by
    rw [Subring.smul_def, ← smul_assoc, smul_eq_mul]
    congr 1
    push_cast
    rw [pow_add]
  rw [he]; exact M₀.smul_mem _ hz

/-- **A power of `s` carries any element of `M = A · M₀` into `M₀`.** This is where the
hypothesis `A · M₀ = M` is spent, and it is what makes the `smul` condition of
`SubmodulesBasis` an identity inside `A₀`. -/
theorem exists_pow_smul_mem (P : PairOfDefinition A) {s : A} (hs : IsTopologicallyNilpotent s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M) {m : M}
    (hm : m ∈ Submodule.span A (M₀ : Set M)) :
    ∃ k : ℕ, s ^ k • m ∈ M₀ := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨kx, hkx⟩ := ihx; obtain ⟨ky, hky⟩ := ihy
      refine ⟨max kx ky, ?_⟩
      have hx' : s ^ (max kx ky) • x ∈ M₀ := by
        have he : max kx ky = (max kx ky - kx) + kx := by omega
        rw [he]; exact P.pow_add_smul_mem hs0 M₀ _ _ _ hkx
      have hy' : s ^ (max kx ky) • y ∈ M₀ := by
        have he : max kx ky = (max kx ky - ky) + ky := by omega
        rw [he]; exact P.pow_add_smul_mem hs0 M₀ _ _ _ hky
      rw [smul_add]; exact M₀.add_mem hx' hy'
  | smul c x _ ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨i, hi⟩ := P.exists_pow_mul_mem hs c
      refine ⟨i + k, ?_⟩
      have he : s ^ (i + k) • (c • x) = (⟨s ^ i * c, hi⟩ : P.ringOfDefinition) • (s ^ k • x) := by
        rw [smul_smul, Subring.smul_def, ← smul_assoc, smul_eq_mul]
        congr 1
        push_cast
        rw [pow_add]; ring
      rw [he]; exact M₀.smul_mem _ hk

/-- **The `smul` half of `SubmodulesBasis`**: every scalar close enough to `0` in `A₀` carries a
given `m` into `ϖⁿ • M₀`.

`m` is carried into `M₀` by `ϖᵏ` for some `k` (`exists_pow_smul_mem`), and `ϖⁿ⁺ᵏ A₀` is a
neighbourhood of `0`; the two combine by arithmetic inside `A₀`. -/
theorem powSmulFamily_smul (P : PairOfDefinition A) {s : A} (hs : IsPseudoUniformizer s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M)
    (hspan : Submodule.span A (M₀ : Set M) = ⊤) (m : M) (n : ℕ) :
    ∀ᶠ a in 𝓝 (0 : P.ringOfDefinition), a • m ∈ P.powSmulFamily hs0 M₀ n := by
  obtain ⟨k, hk⟩ := P.exists_pow_smul_mem hs.isTopologicallyNilpotent hs0 M₀
    (hspan ▸ Submodule.mem_top)
  have hnhd : ∀ᶠ a : P.ringOfDefinition in 𝓝 0,
      (a : A) ∈ (s ^ (n + k)) • (P.ringOfDefinition : Set A) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (by simpa using (hs.hasBasis_nhds_zero P).mem_of_mem (i := n + k) trivial)
  filter_upwards [hnhd] with a ha
  obtain ⟨b, hb, hab⟩ := ha
  have hmem : (⟨b, hb⟩ : P.ringOfDefinition) • (s ^ k • m) ∈ M₀ := M₀.smul_mem _ hk
  have he : a • m = ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n) •
      ((⟨b, hb⟩ : P.ringOfDefinition) • (s ^ k • m)) := by
    have hscal : ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n • (⟨b, hb⟩ : P.ringOfDefinition)) •
        (s ^ k) = (a : A) := by
      rw [smul_eq_mul, Subring.smul_def, smul_eq_mul]
      push_cast
      rw [← hab, pow_add]; ring
    rw [← smul_assoc, ← smul_assoc, hscal]
    -- both sides are now the same `A₀`-action applied to the same element; the `A₀`-action on
    -- `M` is restriction of scalars along `A₀ → A`, so this last step is definitional.
    rfl
  rw [he]
  exact Submodule.smul_mem_pointwise_smul _ _ _ hmem

/-- **The `ϖⁿ • M₀` family is a `SubmodulesBasis`**, for a pseudouniformiser `ϖ` in a ring of
definition `A₀` and an `A₀`-submodule `M₀` spanning `M` over `A`.

`SubmodulesBasis.topology` then makes `M` a topological `A₀`-module for which this family is a
neighbourhood basis of `0`, and `SubmodulesBasis.nonarchimedean` makes it a nonarchimedean
additive group.

This is the basis half of Wedhorn's Remark 6.19. He states it for `A` noetherian and `M₀`
finitely generated, and identifies the resulting topology with the one of his Proposition
6.18(1); neither hypothesis is used here, and no such identification is proved here. -/
theorem powSmulFamily_submodulesBasis (P : PairOfDefinition A) {s : A} (hs : IsPseudoUniformizer s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M)
    (hspan : Submodule.span A (M₀ : Set M) = ⊤) :
    SubmodulesBasis (P.powSmulFamily hs0 M₀) where
  inter i j :=
    ⟨max i j, le_inf (P.powSmulFamily_antitone hs0 M₀ (le_max_left i j))
      (P.powSmulFamily_antitone hs0 M₀ (le_max_right i j))⟩
  smul m i := P.powSmulFamily_smul hs hs0 M₀ hspan m i

end TauCeti.Huber.PairOfDefinition
