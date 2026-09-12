#!/usr/bin/env python3
"""mathlibns.py <mathlib-root> <namespace>... -- does Mathlib declare into this namespace?

The last hand-run step of the namespace-at-a-time recipe.  `nscand.py` says outright that it
cannot answer this -- *"the namespace must also be ROOT IN MATHLIB … which this snapshot cannot
tell you"* -- so every round it was a grep, and in r511 that grep was **wrong on five of six
candidates, in both directions**:

    RootPairing.InvariantForm           grep: not a namespace   truth: 10 declarations
    RootPairing.Equiv                   grep: not a namespace   truth: 56
    SheafOfModules.LocalGeneratorsData  grep: not a namespace   truth:  6
    Integrable                          grep: found a file      truth:  1 (nested elsewhere)
    Basis                               grep: found a file      truth: 14 (as `Module.Basis`)
    BilinForm.IsAlt                     grep: found a file      truth:  0

`^namespace A.B$` cannot see a namespace opened as nested `namespace A` / `namespace B`, and a bare
`^namespace B$` match says nothing about what encloses it.  Both failures have their own ledger
entries already (r458 nesting, r487 compound) -- this is the sixth and seventh time the same shape
has bitten, so it stops being a grep.

Counts come from the same nesting- and compound-aware index `movedopens.py` builds.  A count of 0
means Mathlib declares nothing there: rooting into it would invent a Mathlib namespace, which is
what `Probability.Kernel` (Mathlib spells it `ProbabilityTheory.Kernel`) and `BilinForm.IsAlt`
(`LinearMap.BilinForm`) would have done.

A LARGE count is not automatically a green light either -- it says the namespace exists, not that
your declarations belong in it.  Judge that separately.
"""
import sys, os, importlib.util
from collections import Counter

spec = importlib.util.spec_from_file_location(
    "mo", os.path.join(os.path.dirname(os.path.abspath(__file__)), "movedopens.py"))
mo = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mo)

def main():
    root, cands = sys.argv[1], sys.argv[2:]
    where, nfiles = mo.index(root)
    # AN EMPTY INDEX IS UNRUN, NEVER A VERDICT (r552).  Every candidate scores 0 against an empty
    # index, so the tool prints `ABSENT ... do NOT root into it` for ALL of them -- a confident
    # answer in the dangerous direction, since it would stop every target rather than let a bad one
    # through.  It happened by passing the first candidate where the Mathlib root belongs; the
    # control line said "0 Mathlib files" while the rows still gave verdicts, and it contradicted
    # this function's own known-good example (`BialgHom` 55).
    if not nfiles:
        print(f"# UNRUN: indexed 0 Mathlib files under {root!r}. The first argument is the "
              f"MATHLIB ROOT (…/.lake/packages/mathlib/Mathlib), not a candidate. Refusing to "
              f"report ABSENT against an empty index.", file=sys.stderr)
        return 2
    ns = Counter()
    for _short, spaces in where.items():
        for s in spaces:
            ns[s] += 1
    bad = 0
    for c in cands:
        n = ns.get(c, 0)
        bad += n == 0
        print(f"{'ROOT ' if n else 'ABSENT'} {n:6d}  {c}"
              + ("" if n else "   <- Mathlib declares nothing here; do NOT root into it"))
    print(f"# FIRING CONTROL: {nfiles} Mathlib files, {len(ns)} distinct namespaces, "
          f"nesting- and compound-aware. {len(cands) - bad} of {len(cands)} candidate(s) exist. "
          f"Known-good shipped: `IsClosed` 119, `BialgHom` 55. Known-bad: `Probability.Kernel` 0 "
          f"(Mathlib says `ProbabilityTheory.Kernel`), `BilinForm.IsAlt` 0 (`LinearMap.BilinForm`). "
          f"A nonzero count says the namespace EXISTS, not that your declarations belong in it.",
          file=sys.stderr)
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
