/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence

/-!
# Good Hecke eigenforms

A cusp form is a *good Hecke eigenform* when it is a simultaneous eigenvector of the Hecke
operators `T_n` for every `n` coprime to the level. This file names that condition as
`IsEigenformAwayFromLevel` and records the one fact that makes it usable: for such a form, the
`T_p` eigenvalue at a good prime is the `p`-th Fourier coefficient.

## Why "away from level"

The eigenvector condition is imposed only at `n` coprime to `N`. At the bad primes `p ∣ N` the
operator `U_p` is a different object and a form need not be an eigenvector of it, so a bare
`Eigenform` would be a promise this predicate does not keep — hence the qualified name.

## Main declarations

* `WeierstrassCurve`-style bundling is deliberately not introduced: `IsEigenformAwayFromLevel` is
  a `Prop` on an existing `CuspForm`, not a new structure. The consumers that need it need the
  predicate.

## Implementation notes

The condition is stated over `heckeTCuspNat`, the packaged operator of
`HeckeSlash/Operators.lean`, rather than over the raw double-coset endomorphism it unfolds to.
That packaging exists precisely so that statements about `T_n` have one spelling.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ} (k : ℤ)
variable [NeZero N]

/-- **A good Hecke eigenform**: `f` is a simultaneous eigenvector of every `T_n` with `n` coprime
to the level `N`. The eigenvalue system is the witness `a`. -/
def IsEigenformAwayFromLevel (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∃ a : ℕ+ → ℂ, ∀ n : ℕ+, Nat.Coprime n.val N →
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeTCuspNat k n.val f = a n • f

/-- **The `T_p` eigenvalue of a normalized good eigenform is its `p`-th Fourier coefficient.**
For `p` a prime not dividing the level and `f` normalized (`a₁(f) = 1`), the eigenvector equation
at `p` holds with the scalar named explicitly as `a_p(f)`.

This is `eq_qExpansion_coeff_of_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_eq_smul` read through
`IsEigenformAwayFromLevel`: that theorem identifies the eigenvalue of a given eigenvector equation,
and this one supplies the equation from the predicate. -/
theorem heckeTCuspNat_eq_qExpansion_coeff_smul_of_isEigenformAwayFromLevel
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : IsEigenformAwayFromLevel k f)
    (hp : p.Prime) (hpN : Nat.Coprime p N) (h1 : (qExpansion 1 f).coeff 1 = 1) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    heckeTCuspNat k p f = ((qExpansion 1 f).coeff p) • f := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a, ha⟩ := hf
  -- The witness is indexed by `ℕ+`, so `ha` speaks of `heckeTCuspNat k ↑⟨p, _⟩`. That coercion is
  -- definitionally `p` but not syntactically, so the equation is ascribed rather than rewritten.
  have heq : heckeTCuspNat k p f = a ⟨p, hp.pos⟩ • f := ha ⟨p, hp.pos⟩ hpN
  have hc : heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) f = a ⟨p, hp.pos⟩ • f := by
    rwa [heckeTCuspNat_def] at heq
  rw [heq, eq_qExpansion_coeff_of_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_eq_smul k hp hc h1]

end HeckeRing.GL2

end
