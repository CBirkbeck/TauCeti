#!/usr/bin/env python3
"""nscand.py <snapshot> <lint-findings> -- rank NAMESPACE-AT-A-TIME rooting candidates.

The r483+ lane roots a whole namespace at once rather than one declaration.  What decides whether
a target is defensible is not how many findings sit in one file, but

    flagged declarations in the namespace  /  TOTAL declarations in the namespace, TREE-WIDE.

r490 established the filter after computing it by hand: `BialgHom` 8/8 and `ValuativeRel` 5/5
shipped clean, while `GroupExtension` at **3/37** was rejected unwritten -- rooting 3 of 37 is the
arbitrary boundary that cost #5905 three blocks.  This tool computes that ratio for every namespace
the linter flags, so the judgement stops being a hand computation that gets skipped.

TWO ANCHOR SHAPES HAVE FAILED FIVE TIMES, ALWAYS BY RETURNING ZERO:
  * declarations -- `^theorem X\\.` misses `protected` (r481); the regex missed `public`, the
    module-system keyword, so `ModularForm/Norm/Reduction.lean` reported 0 of its 6 (r490).
  * namespaces -- `^namespace X$` misses NESTING (r458) and COMPOUND `namespace A.B` (r487).
A silent zero here reads exactly like "clean", which is why every one of these survived a round.
Both patterns below are written to cover all of it, and `# FIRING CONTROL` prints the totals so a
zero is interpretable (r184).

SPAN MEANS THE SUBTREE, NOT THE EXACT NAMESPACE (r515).  `SheafOfModules.LocalGeneratorsData`
reported *"spans 1 file"* and its subtree spans **three**: `…LocalGeneratorsData.IsInvertible` is a
CHILD namespace, and `LocalTriviality.lean` and `FinitePresentation.lean` declare into it.  Rooting
the parent in one file would have left a structure's own API split across files -- the r499 defect
with the pieces in different files instead of the same one.  So `spans` now counts the namespace
AND everything under it.

FLAGGED-IN-NAMESPACE IS NOT ENOUGH -- COMPARE IT TO FLAGGED-IN-FILE (r512).  r490 gave the ratio
WITHIN a namespace; this is the file-level twin, and it separated a good target from a bad one that
had already been written:

    RootPairing.Equiv                   2 flagged in the namespace /  32 in the FILE   REJECTED
    RootPairing.InvariantForm           2 / 2      shipped as #5993
    SheafOfModules.LocalGeneratorsData  2 / 2
    IsClosed              (#5984)       2 / 2
    BialgHom              (#5950)       8 / 8

Every PR this lane has shipped has namespace-flagged == file-flagged.  Rooting 2 of 32 flagged
declarations in one file is the arbitrary boundary that cost #5905 three blocks -- and `prepush.sh`
caught it only because `parallelns` fired, one screen downstream of where the judgement belonged.

WHAT THIS TOOL DOES NOT DECIDE.  The namespace must also be ROOT IN MATHLIB -- `Probability` is
not, `BilinForm` is `LinearMap.BilinForm`, `Periodic` is `Function.Periodic` -- and that check
needs Mathlib, not this snapshot.  Ratio first, Mathlib second, then the sibling scan.

LEAN IDENTIFIERS ARE NOT ASCII (r494, anchor miss number SIX).  The old class -- an ASCII-only
head (A-Z, a-z, underscore) followed by an ASCII-only body -- does not FAIL on
`eval_Ψ₃_of_a₁_eq_zero`; it matches `eval_` and stops, yielding a WRONG NAME rather than no name.
(Spelled in prose deliberately: r497 swept the literal class across the toolkit and rewrote this
very sentence, turning the record of the defect into a description of the fix.)  In this tool that undercounts a namespace's total, so a partial namespace
reads as WHOLE, which is the one direction that ships a bad PR.  `TauCeti.WeierstrassCurve` came
out at 26 flagged of 22 total -- a ratio above 1, the arithmetic tell.  22 of 994 findings (2.2%)
carry a non-ASCII name.  Use a Unicode-aware class (see the pattern below); `str` regexes are Unicode by default.
"""
import sys, os, re
from collections import defaultdict

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?'
                  r'(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+|'
                  r'partial\s+|unsafe\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+'
                  r"(_root_\.)?([^\W\d][\w.'!?]*)")
NS = re.compile(r'^namespace\s+(\S+)\s*$')       # accepts compound `namespace A.B`
END = re.compile(r'^end\s+(\S+)\s*$')

def owners(path):
    """Yield (fully-qualified-namespace, short-name) for every declaration in the file.

    The namespace is the enclosing `namespace` stack joined, PLUS any dotted prefix the header
    itself carries -- `theorem AlgHom.foo` inside `namespace TauCeti` lands in `TauCeti.AlgHom`
    exactly as a nested block would.  `_root_.`-anchored declarations belong to no TauCeti
    namespace and are skipped.
    """
    try:
        lines = open(path, encoding='utf-8').read().split('\n')
    except Exception:
        return
    stack, incomment = [], 0
    for L in lines:
        opens, closes = L.count('/-'), L.count('-/')
        was = incomment
        incomment = max(0, incomment + opens - closes)
        if was or opens > closes:
            continue
        m = NS.match(L)
        if m:
            stack.extend(m.group(1).split('.'))        # compound opens several levels
            continue
        m = END.match(L)
        if m:
            for part in reversed(m.group(1).split('.')):
                if stack and stack[-1] == part:
                    stack.pop()
            continue
        m = DECL.match(L)
        if m and not m.group(2):
            parts = m.group(3).split('.')
            ns = stack + parts[:-1]
            if ns:
                yield '.'.join(ns), parts[-1]

def ancestors(ns):
    """Every strict ancestor of a dotted namespace: `A.B.C` -> `A.B`, `A`."""
    parts = ns.split('.')
    return ['.'.join(parts[:i]) for i in range(1, len(parts))]

def main():
    snap, findings = sys.argv[1], sys.argv[2]
    flagged = defaultdict(list)
    for L in open(findings, encoding='utf-8'):
        m = re.match(r'\s*(\S+\.lean):(\d+): (TauCeti\.\S+)', L)
        if not m:
            continue
        full = m.group(3)
        flagged['.'.join(full.split('.')[:-1])].append((m.group(1), int(m.group(2))))
    total, nfiles, ndecl = defaultdict(int), 0, 0
    infile, perfile = {}, defaultdict(int)
    subfiles = defaultdict(set)
    for hits in flagged.values():
        for f, _ln in hits:
            perfile[f] += 1
    nsfiles = defaultdict(set)
    for dp, _, fs in os.walk(snap):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            nfiles += 1
            for ns, _short in owners(p):
                total[ns] += 1
                nsfiles[ns].add(p)
                subfiles[ns].add(p)
                for anc in ancestors(ns):
                    subfiles[anc].add(p)
                ndecl += 1
    rows = []
    for ns, hits in flagged.items():
        t = total.get(ns, 0)
        files = {h[0] for h in hits}
        rows.append((len(hits) == t and t > 0, len(hits), t, len(files),
                     len(subfiles.get(ns, ())), ns))
        infile[ns] = max(perfile[f] for f in files) if files else 0
    rows.sort(key=lambda r: (not r[0], -(r[1] / r[2]) if r[2] else 0, -r[1]))
    for whole, nf, t, ffiles, nsf, ns in rows:
        ratio = f"{nf}/{t}" if t else f"{nf}/0 ?"
        mark = "WHOLE" if whole else ("     " if not t else "     ")
        # `n/m of the file` is only meaningful when the flagged declarations sit in ONE file.
        # Across several it read `9/2 of the file` for MonoidAlgebra -- 9 flagged, at most 2 in any
        # one file -- which invites exactly the misreading the r512 filter exists to prevent.
        m_in_file = infile.get(ns, 0)
        share = (f"{nf}/{m_in_file} of the file" if ffiles == 1 and m_in_file
                 else f"max {m_in_file} in a file" if m_in_file else "?")
        print(f"{mark} {ratio:>9s}  {share:>18s}  flagged in {ffiles} file(s), SUBTREE spans {nsf}  {ns}")
    whole_n = sum(1 for r in rows if r[0])
    zero_n = sum(1 for r in rows if r[2] == 0)
    print(f"# FIRING CONTROL: {nfiles} files, {ndecl} declarations located namespace-aware, "
          f"{len(flagged)} flagged namespaces; {whole_n} are WHOLE (every declaration flagged) and "
          f"are the defensible targets. {zero_n} report a total of 0 -- that is an ANCHOR MISS, not "
          f"a clean namespace: five have now returned a silent zero (r458 nesting, r481 `protected`, "
          f"r487 compound `namespace A.B`, r490 `public`). Ratio does NOT settle a target: the "
          f"namespace must also be ROOT IN MATHLIB -- run `mathlibns.py` for that, never a grep "
          f"(r511: wrong on five of six) -- and its flagged count must match the FILE's, or the "
          f"cut is arbitrary (r512: `RootPairing.Equiv` was 2 of 32).",
          file=sys.stderr)

if __name__ == '__main__':
    main()
