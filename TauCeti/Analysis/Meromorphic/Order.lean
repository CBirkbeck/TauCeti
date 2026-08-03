/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Meromorphic.Order

/-!
# Sign of the meromorphic order of a quotient

A quotient of meromorphic functions has a pole where the numerator's order is smaller than
the denominator's: `meromorphicOrderAt_div_neg_of_meromorphicOrderAt_lt`.

Ported from the AINTLIB `LeanModularForms` project
(`Modularforms/LFunction.lean`,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), where it
supports the pole obligations of Hecke theory; the statement is general meromorphic-order
API with no number-theoretic content.
-/

public section

/-- **A quotient of meromorphic functions has a pole where the numerator's order is
smaller**: if `num` and `den` are meromorphic at `x`, the order of `den` is finite and
`order num < order den`, then `num / den` has negative meromorphic order at `x`. -/
theorem meromorphicOrderAt_div_neg_of_meromorphicOrderAt_lt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    [NormedAlgebra 𝕜 𝕜'] {num den : 𝕜 → 𝕜'} {x : 𝕜}
    (h_num : MeromorphicAt num x) (h_den : MeromorphicAt den x)
    (h_den_finite : meromorphicOrderAt den x ≠ ⊤)
    (h_lt : meromorphicOrderAt num x < meromorphicOrderAt den x) :
    meromorphicOrderAt (num / den) x < 0 := by
  have h_num_finite : meromorphicOrderAt num x ≠ ⊤ := (h_lt.trans h_den_finite.lt_top).ne
  rw [meromorphicOrderAt_div h_num h_den]
  lift meromorphicOrderAt num x to ℤ using h_num_finite with n hn
  lift meromorphicOrderAt den x to ℤ using h_den_finite with m hm
  rw [WithTop.coe_lt_coe] at h_lt
  exact_mod_cast sub_neg.mpr h_lt
