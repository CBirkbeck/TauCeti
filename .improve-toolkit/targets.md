# Target table — regenerated r557, findings from main `bee7947efc` (891 total)

Filters in the order they decide: WHOLE namespace → n/n **of the file** → SUBTREE span →
**ROOT in Mathlib** → **entanglement**. Namespaces already in flight are excluded
(`WeierstrassCurve` #6065, `ContinuousLinearMap` #6082, `IsCoveringMap` and `Module.End` parked).

`ml` is Mathlib's own count in that namespace — **0 means do not root into it**, and the index
now honours `_root_.`, which it did not before r556 (3295 Mathlib declarations use it).
`ent` counts findings in the SAME FILES belonging to other namespaces.




## The filter that actually works: count the PUBLIC unflagged declarations (r575)

r574's question — "do the unflagged declarations have the namespace's type as receiver?" — cannot be
answered by pattern: Lean writes those types as notation (`A →ₐ[k] R`, `E →L[𝕜] F`), so a regex
looking for the namespace name finds nothing and reports a confident zero. That attempt was thrown
away.

What works is cheaper and exact. **A `private` unflagged declaration is not a problem** — nothing
outside the file can name it, so its namespace is no public claim, and `parallelns` already treats
private nested declarations that way (r501). **A public unflagged declaration is the problem**: root
it and you publish a namespace nobody asked for.

Validated against a known outcome: `IsCoveringMap` scores **8 public unflagged**, and those eight are
exactly what `naming` blocked #6093 for.

| namespace | flagged | unflagged | private | **public** |
|---|---:|---:|---:|---:|
| `IsCompactOperator` | 11 | 6 | 6 | **0** |
| `IsCoveringMap` | 59 | 8 | 0 | **8** |
| `Subring` | 9 | 3 | 2 | **1** |
| `FundamentalGroup` | 12 | 24 | 0 | **24** |
| `Subgroup` | 39 | 23 | 0 | **23** |
| `BilinForm` | 13 | 51 | 0 | **51** |
| `LinearPMap` | 10 | 35 | 2 | **33** |
| `Measure` | 21 | 61 | 22 | **39** |
| `Sym` | 14 | 91 | 18 | **73** |
| `AlgebraicGeometry.Scheme.Modules` | 13 | 37 | 11 | **26** |
| `ContRepresentation` | 143 | 74 | 14 | **60** |

**`IsCompactOperator` is the only candidate with zero public unflagged declarations** — 11 flagged
across 3 files, Mathlib ROOT 27, entanglement 0. It is the next target.

## Read the flagged/total ratio before selecting (r574)

**`AlgHom` is dropped as a target (audited r580).** It looked ideal — flat, 11 files, zero
entanglement — and is **35/83**: 16 unflagged private, and **32 unflagged PUBLIC** across six files
(`kernelPoint`, `descentSubgroup`, `faithfullyFlatDescentMulEquiv`, `instGroup`, `mapDomain`, …).
#6093 carried eight such declarations and they cost three blocking rubrics; relocating thirty-two
unrelated constructions to their real receivers is an API redesign, not a rooting. The branch
`improve/alghom-root` `301e050e77` exists only as a record of the extraction — **do not open it**. Building it rooted 48
declarations the linter never flagged, and two spot checks found neither has an `AlgHom` receiver:
`baseChangePointsMulEquiv` takes **no explicit arguments**, `liftEquiv_map_mul` takes a `WithConv`.
That is what `naming` blocked #6093 for, at six times the scale. **Branch built, gate-clean, and
deliberately not opened.**

The ratio alone does not decide it — `ContinuousLinearMap` was 41/63 and came back 10/10. The check
that does: **for a sample of the unflagged declarations, is the namespace's type the first explicit
argument?** If not, rooting them publishes a namespace nobody asked for, and rooting only the flagged
ones leaves the files mixed (`slice`, `parallelns`) — the dead end #6093 hit from the other side.

## The shape of what remains (measured r573)

**891 findings across 62 flagged namespaces.** The distribution decides the strategy:

| flagged declarations | namespaces |
|---|---|
| 1 | 9 |
| 2–4 | 17 |
| 5–9 | 14 |
| 10–29 | 14 |
| 30+ | 8 |

**83% of all findings (746) sit in the 22 namespaces with ten or more, and not one of those 22 is
single-file.** Only 13 namespaces are WHOLE; 43 have zero entanglement.

**There are no small clean targets left.** Filtering for the ideal small PR — WHOLE, single-file, no
subtree, a real Mathlib namespace, 1–7 declarations — returns **three** namespaces, and **all three
are entangled** (`Basis` ent 11, `Representation.IsIrreducible` ent 4, `Submonoid` ent 1). Zero
qualify.

So large multi-file subtree PRs are not a stylistic preference; after 125 merges they are what is
left. Do not spend a round hunting for a quick win — this table is the answer, and it is no.


| flagged | total | files | span | ml | ent | namespace | entangled with |
|---:|---:|---:|---:|---:|---:|---|---|
| 141 | 184 | 18 | 23 | 26 | 0 | `ContRepresentation` |  |
| 35 | 83 | 9 | 11 | 257 | 0 | `AlgHom` |  |
| 21 | 69 | 3 | 15 | 15 | 0 | `Measure` |  |
| 14 | 105 | 2 | 10 | 111 | 0 | `Sym` |  |
| 13 | 50 | 2 | 6 | 83 | 0 | `AlgebraicGeometry.Scheme.Modules` |  |
| 13 | 1021 | 5 | 82 | 11 | 0 | `UniversalEnvelopingAlgebra` |  |
| 12 | 35 | 3 | 4 | 12 | 0 | `FundamentalGroup` |  |
| 11 | 17 | 3 | 3 | 27 | 0 | `IsCompactOperator` |  |
| 10 | 40 | 2 | 5 | 169 | 0 | `LinearPMap` |  |
| 9 | 12 | 1 | 2 | 277 | 0 | `Subring` |  |
| 9 | 27 | 1 | 1 | 56 | 0 | `ClassGroup` |  |
| 9 | 46 | 6 | 7 | 426 | 0 | `MonoidAlgebra` |  |
| **8** | 8 | 1 | 1 | 55 | 0 | `BialgHom` |  |
| 41 | 54 | 3 | 3 | 0 | 0 | `AlgebraicGeometry.AbelianVariety.Hom` |  |
| 12 | 41 | 3 | 7 | 0 | 0 | `BilinForm` |  |
| 134 | 189 | 17 | 21 | 180 | 21 | `Representation` | FDRep:21 |
| 39 | 62 | 4 | 6 | 1186 | 1 | `Subgroup` | Submonoid:1 |
| 27 | 610 | 5 | 53 | 181 | 13 | `ModularForm` | CuspForm:13 |
| 21 | 22 | 4 | 4 | 27 | 23 | `FDRep` | Representation:23 |
| 18 | 45 | 3 | 3 | 38 | 12 | `CuspForm` | ModularForm:12 |

8472 Mathlib files indexed. Sorted: no entanglement first, then Mathlib-root, then size.

## r591 — the inventory refilled, and six of the cleanest-looking targets are traps

r573 concluded "zero small clean targets remain". **That is no longer true.** 99 findings cleared since
(792 total, down from 891), and `nscand.py` on `origin/main` `dfffa8afb3` now reports **13 WHOLE
namespaces** (every declaration flagged) out of 57 flagged.

But WHOLE is not sufficient — the namespace must also be **root in Mathlib**. Running `mathlibns.py`
against `.lake/packages/mathlib/Mathlib` (rev `e21ec050`, 8472 files, 7655 namespaces) splits them:

| namespace | flagged | files / subtree | Mathlib | verdict |
|---|---|---|---|---|
| **`LinearEquiv`** | **8/8** | 2 / 2 | **ROOT 530** | ⭐ **prime target** |
| `BialgHom` | 8/8 | 1 / 1 | ROOT 55 | taken — #5950 |
| `Module.End.IsSemisimple` | 5/5 | 3 / 3 | ROOT 13 | taken — #6113 |
| `SheafOfModules.LocalGeneratorsData` | 2/2 | 1 / **3** | ROOT 6 | viable, but r515: subtree spans 3 |
| `Submonoid` | 1/1 | 1 / 1 | ROOT 517 | thin — 1/2 of the file |
| `Representation.IsIrreducible` | 1/1 | 1 / 1 | ROOT 6 | thin — 1/5 of the file |
| `Basis` | 1/1 | 1 / 1 | ROOT 14 | thin — **1/12 of the file** (r512 arbitrary cut) |
| `PDE.Continuous` | 4/4 | 3 / 3 | **ABSENT** | 🔴 do not root |
| `PDE.ContinuousOn` | 4/4 | 3 / 3 | **ABSENT** | 🔴 do not root |
| `Probability.Kernel` | 3/3 | 1 / 1 | **ABSENT** | 🔴 do not root |
| `Probability.AEStronglyMeasurable` | 1/1 | 1 / 1 | **ABSENT** | 🔴 do not root |
| `Probability.MeasurableSet` | 1/1 | 1 / 1 | **ABSENT** | 🔴 do not root |
| `BilinForm.IsAlt` | 1/1 | 1 / 1 | **ABSENT** | 🔴 do not root |

### 🔴 Six of the thirteen are ABSENT — and they look like the *best* rows on the board
`PDE.Continuous` is 4/4 WHOLE and all-of-file; `Probability.Kernel` is 3/3 and all-of-file. On
`nscand` output alone they outrank everything except `LinearEquiv`. **Mathlib declares nothing in any
of them** — `Probability.Kernel` is `ProbabilityTheory.Kernel` there, `BilinForm.IsAlt` is
`LinearMap.BilinForm`. Rooting into an absent namespace *creates* a root namespace rather than
rejoining one, which is the defect `placement` blocks on.

> **`PDE.*` and `Probability.*` are TauCeti organizational namespaces, not Mathlib receivers.** The
> linter flags them because the *tail* (`Continuous`, `Kernel`) is a Mathlib root name, so the
> transformation it implies is `_root_.Continuous.foo` — dropping `PDE` as well as `TauCeti`, and
> asserting these declarations belong on Mathlib's `Continuous`. That is a placement claim about PDE
> lemmas, not a rooting. **Do not take these as rooting targets**; they likely want a human's
> grandfathering decision instead.

**Next target when a slot frees: `LinearEquiv`** — 8/8, two files, subtree two, 530 Mathlib
declarations to rejoin. Behind it, `SheafOfModules.LocalGeneratorsData` with the r515 subtree caveat.

## r603 — survey refreshed on `ed901a18b4` (781 findings): the WHOLE well is nearly dry

12 WHOLE namespaces (was 13; `Module.End.IsSemisimple` merged as #6113). Of them: **2 are mine and
staged** (`LinearEquiv`, `SheafOfModules.LocalGeneratorsData`), **1 is #5950** (`BialgHom`),
**6 are ABSENT traps**, and **3 are thin** (`Basis` 1/12 of its file, `Representation.IsIrreducible`
1/5, `Submonoid` 1/2 — all r512 arbitrary-cut risks).

### ⭐ The best remaining target is NOT whole: `Subring`
`nscand` ranks it below the WHOLE rows at **9/12**, but the file column is what matters here —
**9/9 of its file** — and `mathlibns` says **ROOT 277**. The 12 declarations:

| where | count | note |
|---|---|---|
| `Algebra/TensorProduct/Subring.lean` | 9 flagged | `tensorSquareMap{,_tmul,_eq_intTensorToRatTensor,_injective}`, `tensorSquareRange`, `mem_tensorSquareRange_iff`, `tmul_mem_tensorSquareRange`, `tensorSquareEquivRange`, `coe_tensorSquareEquivRange_apply` |
| `Algebra/TensorProduct/Subring.lean` | 2 unflagged | `intTensorToRatTensor`, `_tmul` — **both `private`**, so they do not count (r575) |
| `Algebra/Ring/Subgroup.lean` | 1 unflagged | `toAddSubgroup_closure_of_one_mem_of_mul_mem` — **public** |

So it is takeable as **10 declarations across 2 files**, and the second file is not optional: rooting
only `TensorProduct/Subring.lean` leaves one public declaration in `TauCeti.Subring` and `nsslice`
fires HALF-ROOTED. Root both files together.

### 🔴 A seventh ABSENT trap
`ModularForm.NormReduction` (5/8, 5/5 of its file — it looks clean) is **ABSENT from Mathlib**. Add it
to the never-root list beside `PDE.{Continuous, ContinuousOn}`,
`Probability.{Kernel, AEStronglyMeasurable, MeasurableSet}` and `BilinForm.IsAlt`.

Also screened: `IsQuotientCoveringMap` **ROOT 33** (2/3, one file — viable but tiny);
`Submodule.IsLattice` **ROOT 10** (3/4 but only **3/12 of its file** — r512 cut risk).

> **The namespace-at-a-time lane is running out.** After `LinearEquiv`, `LocalGeneratorsData` and
> `Subring`, what remains is the r573 shape: large multi-file namespaces (`ContRepresentation` 141/184
> over 18 files, `Representation` 134/189 over 17, `IsCoveringMap` 59/67 over 9) plus traps and thin
> single declarations. Expect the next targets to need a different strategy, not a better screen.

## r629 — survey on `origin/main` at 761 findings: the lane has reached diminishing returns

**The WHOLE set has not changed since r603** — same 12 namespaces, and `Subring` (the r603 pick, never
a WHOLE row) merged as #6178. Of the 12: `BialgHom` is #5950, `LinearEquiv` is #6188,
`SheafOfModules.LocalGeneratorsData` is the last bench branch, **6 are ABSENT traps**, and 3 are thin
1/1s with r512 cut risk. **Nothing whole remains to take.**

### The r603 method — look at the FILE column, not the namespace ratio — still finds candidates
Rows that are all-of-their-file without being whole-namespace, screened with `mathlibns` and the r575
public-unflagged filter:

| namespace | flagged | file | Mathlib | declarations / files | public unflagged | verdict |
|---|---|---|---|---|---|---|
| `ClassGroup` | 9/27 | **9/9** | ROOT 56 | 27 / **1** | **~18** | 🔴 high risk — worse than `IsCoveringMap` (8 → #6093, stuck nine rounds) |
| `QuadraticMap` | 7/56 | 7/7 | ROOT 153 | — / subtree **4** | ~49 | 🔴 too big; r515 subtree risk |
| `TopCat.Presheaf.EtaleSpace` | 5/13 | 5/5 | ROOT 5 | 13 / 1 | ~6 | ⚠️ moderate |
| `Module.Dual` | 2/9 | 2/2 | ROOT 34 | 9 / 1 | ~5 | ⚠️ moderate |
| `IsQuotientCoveringMap` | 2/3 | 2/2 | ROOT 33 | 3 / 1 | **~0** | ✅ safest — but only **2** declarations |
| `GroupExtension` | 3/38 | 3/3 | — | — | ~35 | 🔴 **r490 rejected this exact namespace at 3/37** |
| `End` | 2/13 | 2/2 | **ABSENT** | — | — | 🔴 **8th trap** — do not root |

### The strategic finding
Every remaining candidate is either **tiny** (1–3 declarations) or carries **5–18 public unflagged
declarations** — the shape that produced #6093's nine-round saga and got `AlgHom` dropped at 32.

> **The namespace-at-a-time lane is done as a source of good PRs.** It has taken 761 findings out of
> ~994 over this session and its predecessors. What is left is the r573 shape — large multi-file
> namespaces (`ContRepresentation` 141/184 over 18 files, `Representation` 134/189 over 17) — plus
> traps and singletons. **Continuing means shipping either trivial PRs or risky ones**, and that is a
> decision for a human, not a screen.

`IsQuotientCoveringMap` (2 declarations, ~0 public unflagged, ROOT 33) is the one safe pick left, and
it is small enough that its value is mostly in keeping a slot warm.

## r632 — the other lanes, screened: `deadprivate` is a TRAP and `unusedscan` is empty

r629 concluded the rooting lane is out of good targets. `improve/` is broader than rooting, and the
toolbox already carries screens for other lanes, so I ran them against `origin/main`:

| screen | rows | verdict |
|---|---|---|
| `deadprivate` | **12** | 🔴 **TRAP — see below** |
| `unusedscan` | **0** | empty (17 class-headed binders suppressed as local instances) |
| `dupbinder` | **0** | empty |
| `dupsig` | 1008 | unscreened; character-identical signatures across files are mostly legitimate |

### 🔴 `deadprivate`'s twelve rows are all deliberate
"A `private` declaration nothing references" sounds unambiguously deletable. **In a proof assistant it
is not**: a declaration whose only job is to *typecheck* is a test, and it is private precisely so it
does not pollute the API. Their own docstrings say so:

```
UnitIntervalMap.lean:70   "### Regressions: the atomic cases … These three instantiations are what
                           that buys, and they fail for any formulation that quietly assumes `μ`
                           has no atoms."
Countable.lean:217        "**Uniqueness genuinely fails at a null atom.**"
MapRestrictDensity:199    "**The density genuinely takes fractional values.**"
Rational.lean:169         "**Worked example: `[ℚ(√(8/9), √(3/4)) : ℚ] = 4`.**"
ConvexSubgroup.lean:673   "… Not `@[simp]`; see …"
VonMangoldt.lean:259      "**An exponent-two prime power whose Artin class has order four.**"
```

Four of five sampled carry an explicit *regression / worked example / genuinely fails* marker; the
fifth is a worked example in substance. **A PR deleting these would remove regression coverage and
documentation the authors wrote on purpose**, and it would look like a tidy-up while doing it.

> The tool is not wrong — they *are* unreferenced private declarations. The wrong step is the
> inference **"unreferenced ⇒ dead"**. This is a worse trap than the ABSENT namespaces, because
> "remove dead code" reads as unambiguously good and the rows are individually plausible.
> **Do not open a `deadprivate` PR without reading every docstring.**

### Where that leaves the lanes
Rooting: exhausted (r629). `deadprivate`: trap. `unusedscan`, `dupbinder`: empty. `dupsig`: 1008 rows,
unscreened, and the r490/r512 experience says a large undifferentiated row count is where arbitrary
cuts come from. **No screened lane currently offers a defensible PR** beyond the two staged branches.

## r638 — `dupsig` closed: exactly one finding, and it is already staged

After r637 taught the tool that a `section` changes the `variable` context, the 247 collision groups
resolve to **65 genuine**. Partitioning those by shape closes the lane:

| shape | count | what they are |
|---|---|---|
| involves a `private` member | **63** | `_aux` layers, specialised-vs-general cases, `public section` re-exports |
| both public | **2** | one deliberate dot-notation form; one genuine alias — **already staged** |

### The two both-public rows, and why only one was taken
```lean
-- KEPT: the docstring states its purpose
/-- … (dot-notation form of `contractable_of_exchangeable`). -/
theorem Exchangeable.contractable … := contractable_of_exchangeable hX hX_meas

-- REMOVED (improve/dedup-tail-le-exchangeablesigma): docstring merely restates the theorem
/-- The path-space tail σ-algebra is contained in the exchangeable σ-algebra. -/
theorem tail_le_exchangeableSigma … := pathTail_le_exchangeableSigma
```

**The difference is the docstring.** One declares itself an intentional dot-notation affordance; the
other gives no reason to exist. CONTRIBUTING forbids retaining "duplicate theorem names", but a
documented API form is a policy question for a human, not a screen's call — and r632 is the standing
warning about deleting things whose purpose is stated in prose the tool cannot read.

> **Lane closed.** `dupsig` yields one PR, which is staged. Re-run it when `main` moves, but do not
> expect volume: 63 of 65 rows are private helpers whose duplication is structural.
