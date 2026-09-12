#!/usr/bin/env python3
"""xsibling.py <root> <base-ref> <file.lean>... -- CROSS-FILE short-reference breakage.

THE r550 RED BUILD.  #6056 rooted the `TauCeti.RootPairing` subtree, `prepush.sh` reported
14 ok / 0 failed / 0 UNRUN, and CI answered with six errors.  One of them was this shape:

    InvariantSubmodule.lean   declares  `_root_.RootPairing.root_mem_of_pairing_ne_zero`
    Irreducible.lean          writes    `root_mem_of_pairing_ne_zero`  bare

Both files sat inside `namespace RootPairing`, so the bare reference resolved.  The PR turned
both wrappers into `section` and the reference died: `Unknown identifier`.

`siblingscan` cannot see this.  It is FILE-LOCAL ON BOTH ENDS -- it collects the `_root_.X.`
declarations of ONE file and looks for bare uses in THAT SAME file.  A name declared in file A
and used bare in file B is outside its universe, and `nsslice` does not help either: it counts
what still DECLARES into `TauCeti.X` elsewhere, never what USES it.  This is r527's cross-file
gap again, one level down: r527 closed it for declarations, and this closes it for references.

THE REACHABLE SET NEEDS NO BASE TREE.  Everything that lived in `TauCeti.X` before the PR is,
after it, either rooted under `X` (the files the PR touched) or still in `TauCeti.X` (everywhere
else).  Scanning HEAD for both therefore reconstructs exactly what a bare reference inside
`namespace X` used to reach -- and it also picks up names rooted by an EARLIER merged PR, which a
base-tree diff would have missed.  Only the question "which wrappers did this PR lose?" needs the
base, and that is a handful of `git show` calls on the targets themselves.

SUFFIXES, NOT SHORT NAMES (the same r550 lesson as `vacuousns.suffixes_below`).  Inside
`namespace RootPairing`, `RootPairing.Equiv.indexHom` is reachable as `Equiv.indexHom` AND as
`indexHom`.  Every component-boundary suffix is a candidate reference.

ATTRIBUTE BRACKETS ARE REPORTED SEPARATELY, NEVER AS A BLOCKER.  The same #6056 carried a second
defect in the other direction: the retarget pass qualified `@[ext]` into
`@[RootPairing.weylGroup.ext]`, because `ext` is the short name of `RootPairing.weylGroup.ext`.
CI: `Unknown attribute`.  A bare token inside `@[...]` is an attribute name, not a declaration
reference, so blocking on it would push the fix toward the very edit that broke the build.  The
rows are printed under ATTRIBUTE so they can be read, and excluded from the exit status.

A SINGLE-COMPONENT SUFFIX IN TACTIC POSITION IS A TACTIC, NOT A REFERENCE.  `RootPairing`
declares `weylGroup.ext`, whose shortest suffix is `ext` -- and `ext i` opens six tactic blocks in
`Positive.lean`.  Blocking on those would have sent me to qualify a tactic into
`RootPairing.weylGroup.ext i`.  When the occurrence is the first token of a tactic step and the
suffix is one component naming a known tactic, it is reported as TACTIC and excluded from the exit
status.  Multi-component suffixes (`Equiv.indexHom_injective`) can never be a tactic and always
block.

A file carrying `open X` is skipped for that X: the bare names still resolve.

KNOWN LIMIT, recorded rather than discovered.  The reachable set is built from TAU CETI's
declarations only, so a short reference to a MATHLIB name under the same namespace -- `namespace
WeierstrassCurve.Affine` removed while the file still writes `CoordinateRing.XYIdeal` for
Mathlib's `WeierstrassCurve.Affine.CoordinateRing.XYIdeal` -- is invisible here.  In practice the
files that do this carry an `open` line covering the namespace (LocalRing.lean opens
`WeierstrassCurve.Affine`), and the `open` handling above takes them out of scope, which is why
this has not yet bitten.  Closing it properly means indexing Mathlib the way `movedopens.py`
does; until then, a wrapper removed WITHOUT a matching `open` is the case to check by hand.
"""
import sys, os, re, subprocess, importlib.util
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
def _load(n):
    spec = importlib.util.spec_from_file_location(n, os.path.join(HERE, n + ".py"))
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
nss = _load("nsslice")
vns = _load("vacuousns")           # TACTICS/LEAD live there: ONE definition, two tools

NS = re.compile(r'^namespace\s+(\S+)\s*$')
END = re.compile(r'^end\s+(\S+)\s*$')
OPEN = re.compile(r'^\s*(?:scoped\s+)?open\s+(.*?)(?:\s+in)?\s*$')

def ns_entered(lines):
    """Every full namespace path the file is ever inside."""
    seen, stack, inc = set(), [], 0
    for L in lines:
        o, c = L.count('/-'), L.count('-/')
        was = inc; inc = max(0, inc + o - c)
        if was or o > c: continue
        m = NS.match(L)
        if m:
            stack.extend(m.group(1).split('.')); seen.add('.'.join(stack)); continue
        m = END.match(L)
        if m:
            for part in reversed(m.group(1).split('.')):
                if stack and stack[-1] == part: stack.pop()
    return seen

def opened(lines):
    names = set()
    for L in lines:
        m = OPEN.match(L)
        if m and '⟨' not in m.group(1):
            for t in m.group(1).split():
                if re.fullmatch(r"[^\W\d][\w.']*", t): names.add(t)
    return names

def code_lines(lines):
    """(lineno, code, attr_spans) with comments, docstrings, backticks and strings masked."""
    depth = 0
    for i, raw in enumerate(lines, 1):
        o, c = raw.count('/-'), raw.count('-/')
        was = depth; depth = max(0, depth + o - c)
        if was or o:
            continue
        code = re.sub(r'`[^`]*`', lambda m: ' ' * len(m.group(0)), raw)
        code = re.sub(r'"(?:[^"\\]|\\.)*"', lambda m: ' ' * len(m.group(0)), code)
        code = re.sub(r'--.*$', lambda m: ' ' * len(m.group(0)), code)
        spans = [(m.start(), m.end()) for m in re.finditer(r'@\[[^\]]*\]', code)]
        code = vns.mask_decl_name(code)         # r563: a header's own name is not a reference
        yield i, code, spans

def main():
    root, base, targets = sys.argv[1], sys.argv[2], [os.path.normpath(t) for t in sys.argv[3:]]
    missing = [t for t in targets if not os.path.exists(t)]
    if missing:
        # NEVER SKIP A TARGET SILENTLY.  An earlier run passed this tool a single argument holding
        # newline-separated paths (zsh does not word-split an unquoted `$var`, only `$(...)`), and
        # the `os.path.exists` filter quietly dropped it -- so the screen reported "nothing to
        # check" for three whole-subtree branches that plainly did remove wrappers.  That is the
        # prepush principle (an unrunnable check is UNRUN, never a pass) failing INSIDE a tool.
        print(f"# UNRUN: {len(missing)} target(s) do not exist, e.g. {missing[0][:120]!r}. "
              f"Refusing to report on a partial target list.", file=sys.stderr)
        return 2
    head = {t: open(t, encoding='utf-8').read().split('\n') for t in targets}

    # ---- which wrappers did each target lose?
    lost = {}
    for t, hl in head.items():
        h = ns_entered(hl)
        try:
            bl = subprocess.run(['git', 'show', f'{base}:{t}'], capture_output=True, text=True,
                                check=True).stdout.split('\n')
            b = ns_entered(bl)
        except subprocess.CalledProcessError:
            b = set()                                   # new file: nothing lost
        gone = {p[len('TauCeti.'):] for p in b - h
                if p.startswith('TauCeti.') and p != 'TauCeti'}
        # a file that declares into root `X` while not being inside `namespace X` is exposed too,
        # even when the base had no wrapper at all
        for ns, _s, is_root in nss.walk(t):
            if is_root and ns and ('TauCeti.' + ns.split('.')[0]) not in h:
                gone.add(ns.split('.')[0])
        gone -= opened(hl)
        if gone: lost[t] = gone

    if not lost:
        print("# FIRING CONTROL: none of the given files lost a `namespace` wrapper "
              "(and none declares into a root namespace it is not inside); nothing to check.",
              file=sys.stderr)
        return 0

    wrappers = set().union(*lost.values())

    # ---- what a bare reference inside `namespace X` used to reach (see docstring)
    tails, nfiles = defaultdict(set), 0
    for dp, _, fs in os.walk(root):
        for f in fs:
            if not f.endswith('.lean'): continue
            p = os.path.normpath(os.path.join(dp, f)); nfiles += 1
            for ns, short, is_root in nss.walk(p):
                full = ns + '.' + short if ns else short
                for X in wrappers:
                    if is_root and (ns == X or ns.startswith(X + '.')):
                        tails[X].add((full[len(X) + 1:], full))
                    elif not is_root and (ns == 'TauCeti.' + X or
                                          ns.startswith('TauCeti.' + X + '.')):
                        tails[X].add((full[len('TauCeti.' + X) + 1:], X + full[len('TauCeti.'):]))

    cand = defaultdict(dict)                             # X -> {suffix: full declaration name}
    for X, ts in tails.items():
        for t, full in ts:
            parts = t.split('.')
            for i in range(len(parts)):
                cand[X].setdefault('.'.join(parts[i:]), full)

    # first token of a tactic step, and the suffix names a tactic -> not a reference.
    # ONE definition, shared with `siblingscan` through `vacuousns`: two copies of this set would
    # drift, and the two tools have to agree about what is a tactic (r550).
    TACTICS, LEAD = vns.TACTICS, vns.LEAD
    rows, attrs, tacs, nsuf = [], [], [], 0
    for t, gone in sorted(lost.items()):
        pool = {}                                        # suffix -> X
        for X in gone:
            for s, full in cand.get(X, {}).items(): pool.setdefault(s, (X, full))
        nsuf += len(pool)
        first = defaultdict(list)                        # cheap substring guard (r540)
        for s in pool: first[s.split('.')[0]].append(s)
        for ln, code, spans in code_lines(head[t]):
            for tok, sufs in first.items():
                if tok not in code: continue
                for s in sufs:
                    for m in re.finditer(r'(?<![\w.])' + re.escape(s) + r'(?!\w)', code):
                        X, full = pool[s]
                        if any(a <= m.start() < b for a, b in spans):
                            attrs.append((t, ln, s, full)); continue
                        if ('.' not in s and s in TACTICS
                                and LEAD.match(code[:m.start()].replace('<;>', '   '))):
                            tacs.append((t, ln, s, full)); continue
                        rows.append((t, ln, s, full))
    seen = set(); uniq = []
    for r in rows:
        if r[:3] not in seen: seen.add(r[:3]); uniq.append(r)
    for t, ln, s, full in uniq:
        print(f"BREAKS  {t}:{ln}  `{s}` -> `{full}`\n"
              f"        qualify it as `{full}`")
    for t, ln, s, full in attrs[:8]:
        print(f"ATTRIBUTE  {t}:{ln}  `{s}` sits inside `@[...]` -- an attribute name, "
              f"NOT a reference. Do not qualify it (that is what broke #6056).")
    for t, ln, s, full in tacs[:8]:
        print(f"TACTIC     {t}:{ln}  `{s}` opens a tactic step -- the `{s}` tactic, not a "
              f"reference to `{full}`. Do not qualify it.")
    print(f"# FIRING CONTROL: {nfiles} files walked; {len(lost)} target(s) lost a wrapper "
          f"({', '.join(sorted(wrappers))}); {sum(len(v) for v in tails.values())} names were "
          f"reachable there, {nsuf} suffix forms searched; {len(uniq)} BREAK, {len(attrs)} in "
          f"attribute brackets and {len(tacs)} in tactic position (both reported, never "
          f"blocking). `siblingscan` is FILE-LOCAL ON BOTH "
          f"ENDS and cannot see any of this -- r550, learned from a red build.", file=sys.stderr)
    return 1 if uniq else 0

if __name__ == '__main__':
    sys.exit(main())
