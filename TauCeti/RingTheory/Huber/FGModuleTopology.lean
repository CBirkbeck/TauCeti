/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-!
# The canonical topology on a finitely generated module over a Tate ring

Wedhorn's Remark 6.19: let `A` be a Tate ring, `A₀` a ring of definition, `ϖ ∈ A₀` a
pseudouniformiser, and `M₀` an `A₀`-submodule of an `A`-module `M` with `A · M₀ = M`. Then the
family `ϖⁿ • M₀` is a fundamental system of open neighbourhoods of `0` for the topology of
Wedhorn's Proposition 6.18(1).

This file exhibits that family as a `SubmodulesBasis`, which is Mathlib's machinery for turning
such a family into a topology; `SubmodulesBasis.topology` and `.nonarchimedean` then apply.

## Main results

* `TauCeti.Huber.PairOfDefinition.exists_pow_smul_mem`: a power of `ϖ` carries any element of
  `M` into `M₀`. This is where `A · M₀ = M` is spent.
* `TauCeti.Huber.PairOfDefinition.fgFamily_submodulesBasis`: the family is a `SubmodulesBasis`.

## Implementation notes

The neighbourhoods are `A₀`-submodules, not `A`-submodules, so `SubmodulesBasis` is instantiated
at `R := P.ringOfDefinition`: `M` carries its `A₀`-module structure by restriction of scalars
along `A₀ → A`, which typeclass inference supplies unaided.

The family is `ϖⁿ • M₀` rather than `Iⁿ • M₀` for the ideal of definition `I`. That is Wedhorn's
own indexing, and it is forced: the `smul` condition needs `Iⁿ · ϖᵏ` to contain a neighbourhood
of `0`, which holds only when `I = ϖA₀` — exactly the hypothesis Remark 6.19 runs under.

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
def fgFamily (P : PairOfDefinition A) {s : A} (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (n : ℕ) : Submodule P.ringOfDefinition M :=
  ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n) • M₀

omit [IsTopologicalRing A] in
/-- The family is antitone, which is the `inter` half of `SubmodulesBasis`. -/
theorem fgFamily_antitone (P : PairOfDefinition A) {s : A} (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) : Antitone (P.fgFamily hs0 M₀) := by
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

/-- **A power of `s` carries any element of `M = A · M₀` into `M₀`.** This is where the
hypothesis `A · M₀ = M` is spent, and it is what makes the `smul` condition of
`SubmodulesBasis` an identity inside `A₀`. -/
theorem exists_pow_smul_mem (P : PairOfDefinition A) {s : A} (hs : IsTopologicallyNilpotent s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M)
    (hspan : Submodule.span A (M₀ : Set M) = ⊤) (m : M) :
    ∃ k : ℕ, s ^ k • m ∈ M₀ := by
  have key : ∀ (j k : ℕ) (z : M), s ^ k • z ∈ M₀ → s ^ (j + k) • z ∈ M₀ := by
    intro j k z hz
    have he : s ^ (j + k) • z = (⟨s, hs0⟩ : P.ringOfDefinition) ^ j • (s ^ k • z) := by
      rw [← smul_assoc]
      congr 1
      change s ^ (j + k) = (((⟨s, hs0⟩ : P.ringOfDefinition) ^ j : P.ringOfDefinition) : A) * s ^ k
      push_cast
      rw [pow_add]
    rw [he]; exact M₀.smul_mem _ hz
  have hm : m ∈ Submodule.span A (M₀ : Set M) := hspan ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨kx, hkx⟩ := ihx; obtain ⟨ky, hky⟩ := ihy
      refine ⟨max kx ky, ?_⟩
      have hx' : s ^ (max kx ky) • x ∈ M₀ := by
        have he : max kx ky = (max kx ky - kx) + kx := by omega
        rw [he]; exact key _ _ _ hkx
      have hy' : s ^ (max kx ky) • y ∈ M₀ := by
        have he : max kx ky = (max kx ky - ky) + ky := by omega
        rw [he]; exact key _ _ _ hky
      rw [smul_add]; exact M₀.add_mem hx' hy'
  | smul c x _ ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨i, hi⟩ := P.exists_pow_mul_mem hs c
      refine ⟨i + k, ?_⟩
      have he : s ^ (i + k) • (c • x) = (⟨s ^ i * c, hi⟩ : P.ringOfDefinition) • (s ^ k • x) := by
        rw [smul_smul, ← smul_assoc]
        congr 1
        change s ^ (i + k) * c = (((⟨s ^ i * c, hi⟩ : P.ringOfDefinition)) : A) * s ^ k
        push_cast
        rw [pow_add]; ring
      rw [he]; exact M₀.smul_mem _ hk

/-- **The `smul` half of `SubmodulesBasis`**: every scalar close enough to `0` in `A₀` carries a
given `m` into `ϖⁿ • M₀`.

`m` is carried into `M₀` by `ϖᵏ` for some `k` (`exists_pow_smul_mem`), and `ϖⁿ⁺ᵏ A₀` is a
neighbourhood of `0`; the two combine by arithmetic inside `A₀`. -/
theorem fgFamily_smul (P : PairOfDefinition A) {s : A} (hs : IsPseudoUniformizer s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M)
    (hspan : Submodule.span A (M₀ : Set M) = ⊤) (m : M) (n : ℕ) :
    ∀ᶠ a in 𝓝 (0 : P.ringOfDefinition), a • m ∈ P.fgFamily hs0 M₀ n := by
  obtain ⟨k, hk⟩ := P.exists_pow_smul_mem hs.isTopologicallyNilpotent hs0 M₀ hspan m
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
      change ((((⟨s, hs0⟩ : P.ringOfDefinition) ^ n * ⟨b, hb⟩ : P.ringOfDefinition)) : A)
          * s ^ k = (a : A)
      push_cast
      rw [← hab, pow_add]; ring
    rw [← smul_assoc, ← smul_assoc, hscal]
    rfl
  rw [he]
  exact Submodule.smul_mem_pointwise_smul _ _ _ hmem

/-- **Wedhorn Remark 6.19.** For a pseudouniformiser `ϖ` in a ring of definition `A₀`, and a
finitely generated `A₀`-submodule `M₀` spanning `M` over `A`, the family `ϖⁿ • M₀` is a
`SubmodulesBasis`.

`SubmodulesBasis.topology` is then the topology of Wedhorn's Proposition 6.18(1), and
`SubmodulesBasis.nonarchimedean` makes `M` a nonarchimedean additive group for it. -/
theorem fgFamily_submodulesBasis (P : PairOfDefinition A) {s : A} (hs : IsPseudoUniformizer s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M)
    (hspan : Submodule.span A (M₀ : Set M) = ⊤) :
    SubmodulesBasis (P.fgFamily hs0 M₀) where
  inter i j :=
    ⟨max i j, le_inf (P.fgFamily_antitone hs0 M₀ (le_max_left i j))
      (P.fgFamily_antitone hs0 M₀ (le_max_right i j))⟩
  smul m i := P.fgFamily_smul hs hs0 M₀ hspan m i

end TauCeti.Huber.PairOfDefinition
