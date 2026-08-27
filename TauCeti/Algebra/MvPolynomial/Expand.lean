/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Finiteness of `MvPolynomial.expand` and of `MvPolynomial.map`

The polynomial ring `R[X_i]` is a finite module over its image under `MvPolynomial.expand n`
(the subring `R[X_i ^ n]`), spanned by the monomials whose exponents are all below `n`; and
`MvPolynomial.map f` is a finite ring map whenever `f` is. Composed, they say that
`k'[X_1, …, X_r]` is a finite module over `k[X_1 ^ q, …, X_r ^ q]` for a finite extension
`k' / k` — the finiteness that Stacks 10.161.13 (tag 032O) records as "`R'[x^{1/q}]` is finite
over `R[x]`" and that the purely inseparable half of normalization-finiteness rests on.

Also here is the coefficient-level Frobenius computation behind Stacks' "some details omitted":
if every coefficient of `g` acquires a `q`-th root in `S`, then `g(X ^ q)` becomes a `q`-th power
in `S[X_i]`.

## Main results

* `TauCeti.MvPolynomial.span_monomial_lt_eq_top`: over the image of `expand n`, the monomials
  with all exponents below `n` span the polynomial ring.
* `TauCeti.MvPolynomial.finite_expand`: `expand n` is a finite ring map for `0 < n`.
* `TauCeti.MvPolynomial.finite_map`: `MvPolynomial.map f` is finite when `f` is.
* `TauCeti.MvPolynomial.exists_pow_eq_map_expand`: `(map f) (expand (p ^ n) g)` is a
  `p ^ n`-th power once the coefficients of `g` have `p ^ n`-th roots in `S`.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`. The mathematics is the finiteness sentence of
Stacks 10.161.13 (tag 032O), stated for `n` variables at once.
-/

public section

namespace TauCeti

/-- Source: Stacks, Lemma 10.161.13 (tag 032O), proof: "`R′[x^{1/q}]` is finite over `R[x]`" —
the inductive step of the spanning argument. Every monomial lies in the span, over the image of
`MvPolynomial.expand n`, of the monomials with all exponents below `n`: write each exponent as
`n * γ + β` with `β < n`, so that `X ^ (n • γ + β) = expand n (X ^ γ) * X ^ β`. -/
theorem MvPolynomial.monomial_mem_span_monomial_lt {σ R : Type*} [CommSemiring R] [Finite σ]
    {n : ℕ} (hn : 0 < n) (d : σ →₀ ℕ) (r : R) :
    MvPolynomial.monomial d r ∈
      Submodule.span (MvPolynomial.expand (σ := σ) (R := R) n).range
        (Set.range fun β : σ → Fin n =>
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (β i : ℕ)) (1 : R)) := by
  classical
  -- the exponent `d i` splits as `n * (d i / n) + d i % n`
  have hexp :
      n • (Finsupp.equivFunOnFinite.symm fun i => d i / n)
        + (Finsupp.equivFunOnFinite.symm fun i =>
            ((⟨d i % n, Nat.mod_lt _ hn⟩ : Fin n) : ℕ)) = d := by
    ext i
    simp [Nat.div_add_mod]
  -- the sub-`n` part is one of the generators
  have hmem :
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i =>
          ((⟨d i % n, Nat.mod_lt _ hn⟩ : Fin n) : ℕ)) (1 : R) ∈
        Submodule.span (MvPolynomial.expand (σ := σ) (R := R) n).range
          (Set.range fun β : σ → Fin n =>
            MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (β i : ℕ)) (1 : R)) :=
    Submodule.subset_span ⟨fun i => ⟨d i % n, Nat.mod_lt _ hn⟩, rfl⟩
  -- name the scalar, so that the `•`/`*` defeq check stays cheap
  obtain ⟨a, ha⟩ : ∃ a : (MvPolynomial.expand (σ := σ) (R := R) n).range,
      (a : MvPolynomial σ R)
        = (MvPolynomial.expand (σ := σ) (R := R) n)
            (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => d i / n) r) :=
    ⟨⟨_, AlgHom.mem_range_self _ _⟩, rfl⟩
  have key : (MvPolynomial.monomial d r : MvPolynomial σ R)
      = (MvPolynomial.expand (σ := σ) (R := R) n)
            (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => d i / n) r) *
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i =>
            ((⟨d i % n, Nat.mod_lt _ hn⟩ : Fin n) : ℕ)) (1 : R) := by
    rw [MvPolynomial.expand_monomial, MvPolynomial.monomial_mul_monomial, mul_one, hexp]
  rw [key, ← ha]
  exact Submodule.smul_mem _ a hmem

/-- Source: Stacks, Lemma 10.161.13 (tag 032O), proof: "`R′[x^{1/q}]` is finite over `R[x]`".
Over the image of `MvPolynomial.expand n`, the finitely many monomials with all exponents below
`n` span the whole polynomial ring. -/
theorem MvPolynomial.span_monomial_lt_eq_top {σ R : Type*} [CommSemiring R] [Finite σ] {n : ℕ}
    (hn : 0 < n) :
    Submodule.span (MvPolynomial.expand (σ := σ) (R := R) n).range
      (Set.range fun β : σ → Fin n =>
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (β i : ℕ)) (1 : R)) = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  exact MvPolynomial.induction_on' f (fun d r => MvPolynomial.monomial_mem_span_monomial_lt hn d r)
    (fun p q hp hq => Submodule.add_mem _ hp hq)

/-- Source: Stacks, Lemma 10.161.13 (tag 032O), proof: "`R′[x^{1/q}]` is finite over `R[x]`".
`MvPolynomial.expand n` is a finite ring map for `0 < n`: the polynomial ring is spanned over
`R[X_i ^ n]` by the monomials with exponents below `n`. -/
theorem MvPolynomial.finite_expand {σ R : Type*} [CommRing R] [Finite σ] {n : ℕ} (hn : 0 < n) :
    (MvPolynomial.expand (σ := σ) (R := R) n).toRingHom.Finite := by
  classical
  -- `MvPolynomial σ R` is a finite module over the subalgebra `R[X_i ^ n]`
  have hfin : Module.Finite (MvPolynomial.expand (σ := σ) (R := R) n).range
      (MvPolynomial σ R) :=
    Module.Finite.of_fg_top (Submodule.fg_def.2 ⟨_, Set.finite_range _,
      MvPolynomial.span_monomial_lt_eq_top hn⟩)
  -- Factor `expand n` as `R[X_i] ↠ R[X_i ^ n] ↪ R[X_i]`. Going through the range keeps the
  -- `Module (MvPolynomial σ R) (MvPolynomial σ R)` diamond out of the way: instance search
  -- picks `Semiring.toModule` (plain multiplication), not the `expand`-algebra the statement
  -- means, and the two are not defeq.
  have h₁ : ((MvPolynomial.expand (σ := σ) (R := R) n).rangeRestrict.toRingHom).Finite :=
    RingHom.Finite.of_surjective _ (AlgHom.rangeRestrict_surjective _)
  have h₂ : ((MvPolynomial.expand (σ := σ) (R := R) n).range.val.toRingHom).Finite := hfin
  have hfac : (MvPolynomial.expand (σ := σ) (R := R) n).toRingHom
      = ((MvPolynomial.expand (σ := σ) (R := R) n).range.val.toRingHom).comp
        ((MvPolynomial.expand (σ := σ) (R := R) n).rangeRestrict.toRingHom) := rfl
  rw [hfac]
  exact RingHom.Finite.comp h₂ h₁

/-- Source: Stacks, Lemma 10.161.13 (tag 032O), proof: "Since `R` is N-2 we see that `R′` is
finite over `R` and hence `R′[x^{1/q}]` is finite over `R[x]`". Polynomial rings preserve
module-finiteness of the coefficient map: `MvPolynomial.map f` is finite whenever `f` is. -/
theorem MvPolynomial.finite_map {σ R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.Finite) : (MvPolynomial.map (σ := σ) f).Finite := by
  classical
  let _ : Algebra R S := f.toAlgebra
  obtain ⟨t, htfin, ht⟩ := Submodule.fg_def.mp (Module.finite_def.mp hf)
  let _ : Algebra (MvPolynomial σ R) (MvPolynomial σ S) := (MvPolynomial.map (σ := σ) f).toAlgebra
  refine Module.finite_def.mpr (Submodule.fg_def.mpr
    ⟨MvPolynomial.C '' t, htfin.image _, eq_top_iff.mpr fun p _ ↦ ?_⟩)
  refine MvPolynomial.induction_on' p (fun α c ↦ ?_) (fun p q hp hq ↦ Submodule.add_mem _ hp hq)
  refine Submodule.span_induction
    (p := fun c _ ↦ MvPolynomial.monomial α c ∈
      Submodule.span (MvPolynomial σ R) (MvPolynomial.C '' t))
    ?_ ?_ ?_ ?_ (ht ▸ Submodule.mem_top : c ∈ Submodule.span R t)
  · -- a generator `x ∈ t`, as the constant `C x`, scaled by the monomial `X ^ α`
    intro x hx
    have hx' : MvPolynomial.monomial α x
        = (MvPolynomial.monomial α (1 : R)) • (MvPolynomial.C x : MvPolynomial σ S) := by
      rw [Algebra.smul_def]
      change _ = MvPolynomial.map f (MvPolynomial.monomial α 1) * MvPolynomial.C x
      rw [MvPolynomial.map_monomial, map_one, mul_comm, MvPolynomial.C_mul_monomial, mul_one]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · -- an `R`-scalar becomes the constant `C r` acting through `MvPolynomial.map f`
    intro r x _ hx
    have hr : MvPolynomial.monomial α (r • x)
        = (MvPolynomial.C r : MvPolynomial σ R) • MvPolynomial.monomial α x := by
      rw [Algebra.smul_def]
      change _ = MvPolynomial.map f (MvPolynomial.C r) * MvPolynomial.monomial α x
      rw [MvPolynomial.map_C, MvPolynomial.C_mul_monomial]
      rfl
    rw [hr]
    exact Submodule.smul_mem _ _ hx

/-- Source: Stacks, Lemma 10.161.13 (tag 032O), proof: "There exists a finite purely inseparable
field extension `L′/K` and `q = p^e` such that `L ⊂ L′(x^{1/q})`; some details omitted" — the
coefficient half of the omitted details. If every coefficient of `g` has a `p ^ n`-th root in
`S`, then `g(X ^ (p ^ n))`, read in `S[X_i]`, is a `p ^ n`-th power: with
`h = ∑ d_α X ^ α` for `d_α ^ (p ^ n) = f (coeff α g)`, Frobenius gives
`h ^ (p ^ n) = ∑ f (coeff α g) X ^ (p ^ n • α)`. -/
theorem MvPolynomial.exists_pow_eq_map_expand {σ R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) [ExpChar S p] (n : ℕ) {g : MvPolynomial σ R}
    (hg : ∀ i ∈ g.support, ∃ d : S, d ^ p ^ n = f (g.coeff i)) :
    ∃ h : MvPolynomial σ S, h ^ p ^ n = MvPolynomial.map f (MvPolynomial.expand (p ^ n) g) := by
  classical
  -- total-ise the choice of roots, so the witness is a plain sum over `g.support`
  have hg' : ∀ i : σ →₀ ℕ, ∃ d : S, i ∈ g.support → d ^ p ^ n = f (g.coeff i) := by
    intro i
    by_cases hi : i ∈ g.support
    · obtain ⟨d, hd⟩ := hg i hi
      exact ⟨d, fun _ ↦ hd⟩
    · exact ⟨0, fun h ↦ absurd h hi⟩
  choose d hd using hg'
  refine ⟨∑ α ∈ g.support, MvPolynomial.monomial α (d α), ?_⟩
  -- Frobenius is additive, so the `p ^ n`-th power is taken monomial by monomial
  rw [sum_pow_char_pow]
  conv_rhs => rw [MvPolynomial.as_sum g]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  rw [MvPolynomial.monomial_pow, hd α hα, MvPolynomial.expand_monomial,
    MvPolynomial.map_monomial]

end TauCeti
