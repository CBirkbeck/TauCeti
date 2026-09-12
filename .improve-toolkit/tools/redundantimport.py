#!/usr/bin/env python3
"""redundantimport.py <dir> -- imports another import already provides.

Under Lean's module system an import is NOT transitive: `import B` gives you B, but B's own
plain imports stay private to B.  Only `public import` re-exports.  So "A is redundant
because B imports it" holds precisely when B reaches A along a chain of PUBLIC imports.
Ignoring that distinction would report most of the tree; this repo has 10,837 `public
import` and 2,328 plain, and one file's own prose says "import is not public, so this adds
no second route".

Two rules, deliberately conservative:

* plain `import A` is redundant if ANY other direct import B publicly reaches A -- F only
  needs to SEE A.
* `public import A` is redundant only if another **public** direct import B publicly reaches
  A -- F also RE-EXPORTS A, and a plain import of B would not carry that on.

Only `TauCeti.*` modules are considered: Mathlib's import graph is not in this tree, so a
claim about it could not be checked.  Comment and docstring lines are skipped (prose says
"import" often enough to matter).

FIRING CONTROL on stderr: files, public/plain edges, files carrying 2+ TauCeti imports --
without which a zero could not be told from a scan that never ran.
"""
import re, sys, os
from collections import defaultdict

PUB = re.compile(r'^public\s+import\s+(TauCeti(?:\.[A-Za-z0-9_\']+)*)\s*$')
PLAIN = re.compile(r'^import\s+(TauCeti(?:\.[A-Za-z0-9_\']+)*)\s*$')


def module_of(root, path):
    rel = os.path.relpath(path, root)
    return rel[:-5].replace(os.sep, ".") if rel.endswith(".lean") else None


def parse(path):
    """(public imports, plain imports) of one file, skipping comments."""
    pub, plain, incomment = [], [], 0
    for line in open(path, encoding="utf-8"):
        line = line.rstrip("\n")
        opens, closes = line.count("/-"), line.count("-/")
        was = incomment
        incomment = max(0, incomment + opens - closes)
        if was or opens > closes or line.lstrip().startswith("--"):
            continue
        m = PUB.match(line)
        if m:
            pub.append(m.group(1)); continue
        m = PLAIN.match(line)
        if m:
            plain.append(m.group(1))
    return pub, plain


def main():
    root = sys.argv[1]
    pubs, plains, files = {}, {}, []
    for dp, _, fs in os.walk(root):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            mod = module_of(root, p)
            if not mod:
                continue
            files.append((mod, p))
            pubs[mod], plains[mod] = parse(p)

    # transitive closure over PUBLIC edges only, memoised
    reach = {}

    def publicly_reaches(m, seen=None):
        if m in reach:
            return reach[m]
        acc, stack, vis = set(), list(pubs.get(m, ())), set()
        while stack:
            n = stack.pop()
            if n in vis:
                continue
            vis.add(n); acc.add(n)
            stack.extend(pubs.get(n, ()))
        reach[m] = acc
        return acc

    rows, multi, npub, nplain = [], 0, 0, 0
    for mod, path in files:
        P, Q = pubs.get(mod, []), plains.get(mod, [])
        npub += len(P); nplain += len(Q)
        if len(P) + len(Q) >= 2:
            multi += 1
        for A in Q:                                  # plain: any other import may cover it
            for B in P + Q:
                if B != A and A in publicly_reaches(B):
                    rows.append((path, "import", A, B)); break
        for A in P:                                  # public: only a public import covers it
            for B in P:
                if B != A and A in publicly_reaches(B):
                    rows.append((path, "public import", A, B)); break

    for path, kind, A, B in rows:
        print(f"{path}\t{kind} {A}\tcovered by {B}")
    print(f"# FIRING CONTROL: {len(files)} modules, {npub} public + {nplain} plain TauCeti "
          f"import edges; {multi} files carry 2+ TauCeti imports. redundant={len(rows)}",
          file=sys.stderr)


if __name__ == "__main__":
    main()
