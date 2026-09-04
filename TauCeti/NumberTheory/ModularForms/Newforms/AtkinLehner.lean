/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ConductorDichotomy
public import TauCeti.NumberTheory.ModularForms.Newforms.Basic

/-!
# A form with a periodic level-`l` descent is old

`ConductorDichotomy.lean` proves Miyake's Theorem 4.6.4: if `l ∣ N`, if `f : ℍ → ℂ` is invariant
under the weight-`k` slash action of `T`, and if the level-raise `l ^ (1 - k) • (f ∣[k] diag(l, 1))`
is a cusp form lying in the nebentypus space `S_k(N, χ)`, then *either* `χ` factors through `N / l`
and `f` is itself a cusp form of level `Γ₁(N / l)`, *or* `f` is identically zero.

Both horns say the same thing about the level-`N` form: it is old. On the first horn it is the
level-raise `V_l F` of a genuine cusp form of the proper divisor level `N / l`, and on the second
it is `0`. This file draws that conclusion, which is the step the Atkin–Lehner main lemma takes
after the dichotomy.

## Why `l ≠ 1` is the only arithmetic hypothesis

`TauCeti.cuspFormsOld` is spanned by the level-raises from **proper** divisor levels, so what the
argument needs from `l` is exactly that `N / l` is a proper divisor of `N` — that is, `l ≠ 1`,
which with `[NeZero l]` is `1 < l`. Nothing here asks `l` to be prime, and the descent itself is
supplied by the caller, so no hypothesis about the `q`-expansion of `f` appears.

## Main results

* `TauCeti.mem_cuspFormsOld_of_slash_T_eq`: a cusp form of level `Γ₁(N)` with a nebentypus,
  whose level-`l` descent is invariant under the weight-`k` slash action of `T`, is old.

## Provenance

Adapted from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Chris Birkbeck, Apache-2.0) at
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
`projects/LeanModularForms/LeanModularForms/Eigenforms/AtkinLehner.lean` — the case split of
`qSupportedOnDvd_mem_cuspFormsOld_of_char` (lines 169-192) together with its private helpers
`cuspForm_coe_eq_of_cast` and `isOldformGenerator_of_funeq`. Those two helpers are not ported:
they exist to move a `d * (N / d) = N` cast through `DFunLike.coe` and to repackage the result as
the source's `IsOldformGenerator`, and this repository's `TauCeti.cuspFormsOld` is indexed by the
divisibility `d * M ∣ N` rather than by an equation, so no cast arises and the introduction rule
`TauCeti.mem_cuspFormsOld_of_coe_eq_smul_slash_scaleGL` applies directly. The source's remaining
input, its `q`-expansion support hypothesis, is deliberately absent here: what the argument
consumes is the descent, and this statement takes it as a hypothesis.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 5.6.
* Miyake, *Modular forms*, Section 4.6 (Theorem 4.6.4 is the dichotomy consumed here).
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **A cusp form with a `T`-periodic level-`l` descent is old.** If `f ∈ S_k(N, χ)` is the
level-raise `l ^ (1 - k) • (φ ∣[k] diag(l, 1))` of a function `φ : ℍ → ℂ` invariant under the
weight-`k` slash action of `T`, and `l` is a divisor of `N` other than `1`, then `f` lies in the
old subspace `S_k(Γ₁(N))ᵒˡᵈ`.

This is the level-lowering dichotomy `TauCeti.exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero`
read for its common conclusion: on the descent horn `φ` is a cusp form of level `Γ₁(N / l)` and
`f` is its level-raise, and on the vanishing horn `φ = 0` forces `f = 0`. Both are old. -/
theorem mem_cuspFormsOld_of_slash_T_eq {l : ℕ} [NeZero l] (hl : l ≠ 1) (hlN : l ∣ N)
    (χ : DirichletCharacter ℂ N) (φ : ℍ → ℂ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (hf : ⇑f = (l : ℂ) ^ (1 - k) • (φ ∣[k] scaleGL l))
    (hT : φ ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = φ) :
    f ∈ cuspFormsOld N k := by
  have hl0 : l ≠ 0 := NeZero.ne l
  have hdvd : l * (N / l) ∣ N := (Nat.mul_div_cancel' hlN).dvd
  have hM : N / l ≠ N := Nat.ne_of_lt (Nat.div_lt_self (NeZero.pos N) (by omega))
  rcases exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero hlN k χ φ f hfχ hf hT with
    ⟨_, F, _, hF⟩ | hφ
  · exact mem_cuspFormsOld_of_coe_eq_smul_slash_scaleGL hdvd hM (by rw [hf, hF])
  · have hf0 : f = 0 := DFunLike.coe_injective <| by
      rw [hf, hφ, SlashAction.zero_slash, smul_zero, FunLike.coe_zero]
    exact hf0 ▸ (cuspFormsOld N k).zero_mem

end TauCeti

end
