#!/usr/bin/env python3
"""importcover.py <mathlib-root> <tauceti-root> <file.lean> -- imports another import already covers.

THE r503 DEFECT, `placement` on #5959, and the class `prepush.sh` did NOT cover (r505 said so
rather than bolting on something untested; this is the follow-through).  Two rows, both correct:

  * `Mul.lean` imported `Mathlib.LinearAlgebra.Basis.Defs` while also importing
    `Mathlib.RingTheory.TensorProduct.Free`, which reaches `Basis.Defs` through a chain of
    `public import`s.  I had added it under a WRONG DIAGNOSIS -- `Basis` was unbound because the
    source file's `open Module` did not travel with the move (r498), not because the chain was
    short -- and then justified it in the commit message as "the house convention".
  * `CentralSimple/TensorProduct.lean` kept its direct `Mathlib.RingTheory.TensorProduct.Free`
    import after it began importing `TauCeti.Algebra.TensorProduct.Mul`, which imports `Free`
    publicly.  **A move changes what the ORIGIN file needs, not just the destination.**

WHY `redundantimport.py` DOES NOT COVER THIS.  Its patterns are anchored to `TauCeti` modules
(`^public import (TauCeti...)$`), so it never sees a Mathlib import covered by a TauCeti one, nor a
Mathlib import covered by another Mathlib module's public chain.  Both r503 rows are exactly those
shapes.

PUBLIC vs PLAIN IS NOT A DETAIL.  Coverage runs along `public import` edges only: a plain import
does not re-export.  And a `public import` in the file under test may only be dropped when its
cover is ALSO public -- otherwise the file stops re-exporting a module its consumers rely on.
Getting this backwards would propose a change that silently narrows the file's interface.

Prints a firing control so a zero is interpretable (r184).
"""
import sys, os, re
from collections import defaultdict

IMPORT = re.compile(r'^\s*(public\s+)?(?:meta\s+)?import\s+([A-Za-z_][\w.]*)\s*$')

def index(roots):
    """module name -> list of modules it PUBLICLY imports."""
    pub = defaultdict(list)
    nfiles = 0
    for root, prefix in roots:
        for dp, _, fs in os.walk(root):
            for f in fs:
                if not f.endswith('.lean'):
                    continue
                p = os.path.join(dp, f)
                mod = prefix + os.path.relpath(p, root)[:-5].replace(os.sep, '.')
                nfiles += 1
                try:
                    lines = open(p, encoding='utf-8').read().split('\n')
                except Exception:
                    continue
                for L in lines:
                    m = IMPORT.match(L)
                    if m and m.group(1):
                        pub[mod].append(m.group(2))
    return pub, nfiles

def closure(mod, pub, seen=None):
    """`mod` plus everything reachable from it along `public import` edges."""
    seen = seen if seen is not None else set()
    if mod in seen:
        return seen
    seen.add(mod)
    for m in pub.get(mod, ()):
        closure(m, pub, seen)
    return seen

def main():
    mathlib, tauceti, target = sys.argv[1], sys.argv[2], sys.argv[3]
    pub, nfiles = index([(mathlib, 'Mathlib.'), (tauceti, 'TauCeti.')])
    imports = []
    for L in open(target, encoding='utf-8').read().split('\n'):
        m = IMPORT.match(L)
        if m:
            imports.append((bool(m.group(1)), m.group(2)))
    cov = {mod: closure(mod, pub) - {mod} for _, mod in imports}
    rows = []
    for is_pub, mod in imports:
        for other_pub, other in imports:
            if other == mod:
                continue
            if mod in cov[other] and (not is_pub or other_pub):
                rows.append((mod, other, is_pub))
                break
    for mod, other, is_pub in rows:
        print(f"REDUNDANT  {'public ' if is_pub else ''}import {mod}\n"
              f"           already reached publicly from `{other}`, also imported here")
    print(f"# FIRING CONTROL: {nfiles} files indexed for `public import` edges; "
          f"{len(imports)} imports in {os.path.basename(target)}; {len(rows)} already covered. "
          f"Coverage follows PUBLIC import edges only -- a plain import does not re-export -- and a "
          f"`public import` here is reported only when its cover is also public, since dropping it "
          f"otherwise narrows what this file re-exports. `redundantimport.py` cannot raise these: "
          f"its patterns are anchored to TauCeti modules, and both r503 rows involve Mathlib.",
          file=sys.stderr)
    return 1 if rows else 0

if __name__ == '__main__':
    sys.exit(main())
