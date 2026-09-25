/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable

/-!
# Root sets: numbering the roots, the roots of a product, and removing a simple root

This file records three facts about the root set `f.rootSet E` of a polynomial `f` after base
change to a domain `E`.

First, an explicit numbering of the root set of a separable polynomial enumerates its full root
multiset: separability makes the roots simple, so the multiset is the image of the numbering.
This lets root-product formulas be expressed as finite products indexed by `Fin f.natDegree`,
without choosing a global order on the root set.

Second, the root set of a product of polynomials whose base changes to `E` are nonzero is the
union of the root sets of the factors. This is the lemma that decomposes the roots of a
polynomial along a factorisation, for instance the roots of a monic integer polynomial along its
monic irreducible factors.

Third, dividing a separable polynomial by the linear factor of one of its roots removes exactly
that root from the root set, since separability makes the root simple.

## Main results

* `Polynomial.Separable.roots_map_eq_map_numbering`: for a separable polynomial, a numbering of
  its root set enumerates its full root multiset after base change.
* `Polynomial.rootSet_mul`: the root set of a product of polynomials whose base changes to `E` are
  nonzero is the union of the root sets of the factors.
* `Polynomial.Separable.rootSet_divByMonic_X_sub_C`: for a separable polynomial with root `a`,
  the roots of `f /ₘ (X - C a)` are the roots of `f` other than `a`.
-/

public section

namespace TauCeti

open Finset Polynomial

variable {F : Type*} [CommRing F] {E : Type*} [CommRing E] [IsDomain E] [Algebra F E] {f : F[X]}

/-- A numbering of the root set of a separable polynomial enumerates the whole root multiset:
separability makes the roots simple, so the multiset is the image of the numbering. -/
theorem _root_.Polynomial.Separable.roots_map_eq_map_numbering (hsep : f.Separable)
    (e : Fin f.natDegree ≃ f.rootSet E) :
    (f.map (algebraMap F E)).roots = Multiset.map (fun i ↦ ((e i : E))) univ.val := by
  have hmem : ∀ {a : E}, a ∈ (f.map (algebraMap F E)).roots ↔ a ∈ f.rootSet E := fun {_} ↦
    Polynomial.mem_aroots'.trans Polynomial.mem_rootSet'.symm
  refine (Multiset.Nodup.ext (nodup_roots hsep.map) ?_).mpr ?_
  · exact univ.nodup.map fun i j h ↦ e.injective (Subtype.ext h)
  · intro a
    simp only [Multiset.mem_map, Finset.mem_val, mem_univ, true_and]
    exact ⟨fun ha ↦ ⟨e.symm ⟨a, hmem.mp ha⟩, by simp⟩, fun ⟨i, hi⟩ ↦ hi ▸ hmem.mpr (e i).2⟩

/-- The root set of a product of polynomials is the union of the root sets of the factors,
provided neither factor vanishes after base change to `E`. -/
@[simp]
theorem _root_.Polynomial.rootSet_mul {g : F[X]} (hf : f.map (algebraMap F E) ≠ 0)
    (hg : g.map (algebraMap F E) ≠ 0) : (f * g).rootSet E = f.rootSet E ∪ g.rootSet E := by
  ext x
  simp only [Set.mem_union, mem_rootSet', Polynomial.map_mul, map_mul, mul_eq_zero, ne_eq, hf, hg,
    or_self, not_false_eq_true, true_and]

/-- Removing the linear factor of a simple root `a` from a separable polynomial removes exactly
that root: the roots of `f /ₘ (X - C a)` in `E` are the roots of `f` other than `a`. -/
theorem _root_.Polynomial.Separable.rootSet_divByMonic_X_sub_C (hsep : f.Separable) {a : F}
    (ha : f.IsRoot a) : (f /ₘ (X - C a)).rootSet E = f.rootSet E \ {algebraMap F E a} := by
  classical
  have hfac : f.map (algebraMap F E) =
      (X - C (algebraMap F E a)) * (f /ₘ (X - C a)).map (algebraMap F E) := by
    rw [← map_X (algebraMap F E), ← map_C, ← Polynomial.map_sub, ← Polynomial.map_mul,
      mul_divByMonic_eq_iff_isRoot.mpr ha]
  -- The roots of `f` in `E` are `a` together with the roots of the quotient.
  have hroots : f.aroots E = algebraMap F E a ::ₘ (f /ₘ (X - C a)).aroots E := by
    rw [aroots_def, hfac, roots_mul (hfac ▸ hsep.map.ne_zero), roots_X_sub_C,
      Multiset.singleton_add, aroots_def]
  rw [rootSet_def, rootSet_def, hroots, Multiset.toFinset_cons, Finset.coe_insert,
    Set.insert_sdiff_self_of_notMem]
  -- Separability makes `a` a simple root, so it is not a root of the quotient.
  exact mt Multiset.mem_toFinset.mp (Multiset.nodup_cons.mp (hroots ▸ nodup_roots hsep.map)).1

end TauCeti
