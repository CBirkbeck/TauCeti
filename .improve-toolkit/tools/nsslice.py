#!/usr/bin/env python3
"""nsslice.py [--base <ref>] <root> <file.lean>... -- is this PR rooting only PART of a namespace?

THE GAP THE r527 PROBE EXPOSED.  I told Chris that a file-at-a-time PR on a multi-file namespace
"would trip my own `slice` and `parallelns` checks".  It does not, and the probe proved it:

    slice:      ok   -- it counts FLAGGED declarations PER FILE, and the file went to zero
    parallelns: ok   -- the file has no nested namespace; the headers are dotted inside `TauCeti`

Both checks are file-local by construction.  **Neither can see a namespace sliced ACROSS files** --
9 of `IsCoveringMap`'s 67 declarations rooted, 58 left in eight other files, `TauCeti.IsCoveringMap`
surviving as a half-emptied shadow of the Mathlib namespace.  That is the r515 defect (a structure's
API split across files) in its cross-file form, and it is exactly what `api-design` blocked on in
#5950 when the split was inside one file.

So: for every `_root_.X.y` declaration these files introduce, count what still declares into
`TauCeti.X` (and its subtree) ANYWHERE ELSE in the tree.  A nonzero count means the PR leaves the
namespace half-rooted.

A row is not automatically fatal -- the remainder may belong where it is -- but it is the question
a reviewer will ask, and it must be answered in the PR body rather than discovered.

INTRODUCE MEANS THE DELTA, NOT THE FILE'S ABSOLUTE STATE (r592).  The paragraph above says "for
every `_root_.X.y` declaration these files INTRODUCE", and for four rounds the code did not: it
collected every namespace holding a `_root_.` declaration in the target files, so a file carrying a
PRE-EXISTING rooted declaration reported its namespace as half-rooted no matter what the PR did.
`Algebra/Module/Lattice.lean` has held `_root_.Submodule.toAddSubgroup_submoduleOf` since before
this lane existed, and a PR touching that file for an unrelated namespace was told `Submodule: 24
declaration(s) still in TauCeti.Submodule across 7 other file(s)` -- a defect report about main.
Running the tool on a PRISTINE checkout of that file reproduces both rows, which is the proof.

This is r551 exactly, one tool over: `nsbalance` printed 4600 false rows on green `main` until it
was made a delta against the merge-base.  With `--base <ref>` the rooted set is
`rooted(HEAD) - rooted(base)` per target file, so only namespaces THIS PR roots are checked.
Without it the legacy absolute scan is kept, and the firing control says which mode ran.
"""
import sys, os, re, subprocess, tempfile
from collections import defaultdict

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?'
                  r'(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+|'
                  r'partial\s+|unsafe\s+)*'
                  r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+'
                  r"(_root_\.)?([^\W\d][\w.'!?]*)")
NS = re.compile(r'^namespace\s+(\S+)\s*$')
END = re.compile(r'^end\s+(\S+)\s*$')

def walk(path):
    """yield (namespace, short, rooted) for each declaration."""
    try:
        lines = open(path, encoding='utf-8').read().split('\n')
    except Exception:
        return
    stack, inc = [], 0
    for L in lines:
        o, c = L.count('/-'), L.count('-/')
        was = inc
        inc = max(0, inc + o - c)
        if was or o > c:
            continue
        m = NS.match(L)
        if m:
            stack.extend(m.group(1).split('.')); continue
        m = END.match(L)
        if m:
            for part in reversed(m.group(1).split('.')):
                if stack and stack[-1] == part:
                    stack.pop()
            continue
        m = DECL.match(L)
        if m:
            parts = m.group(2).split('.')
            yield ('.'.join(parts[:-1]) if m.group(1) else '.'.join(stack + parts[:-1]),
                   parts[-1], bool(m.group(1)))

def rooted_in(path):
    """namespaces holding a `_root_.` declaration in one file."""
    return {ns for ns, _s, is_root in walk(path) if is_root and ns}

def main():
    argv = sys.argv[1:]
    base = None
    if '--base' in argv:
        i = argv.index('--base'); base = argv[i + 1]; del argv[i:i + 2]
    root, targets = argv[0], [os.path.normpath(t) for t in argv[1:]]
    rooted, pre = set(), set()
    for t in targets:
        head = rooted_in(t)
        if base:
            r = subprocess.run(['git', 'show', f'{base}:{t}'], capture_output=True, text=True)
            if r.returncode == 0:                         # absent at base => a new file roots it all
                with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as tf:
                    tf.write(r.stdout); tmp = tf.name
                was = rooted_in(tmp)
                os.unlink(tmp)
                pre |= was
                head -= was
        rooted |= head
    if not rooted:
        print(f"# FIRING CONTROL: no namespace is newly rooted by these file(s); nothing to check. "
              f"{len(pre)} namespace(s) were ALREADY rooted here at the base and are not this PR's "
              f"to answer for (r592).", file=sys.stderr)
        return 0
    left = defaultdict(lambda: defaultdict(int))
    nfiles = 0
    for dp, _, fs in os.walk(root):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.normpath(os.path.join(dp, f))
            nfiles += 1
            if p in targets:
                continue
            for ns, _s, is_root in walk(p):
                if is_root:
                    continue
                for r in rooted:
                    if ns == "TauCeti." + r or ns.startswith("TauCeti." + r + "."):
                        left[r][p] += 1
    rows = 0
    for r in sorted(rooted):
        if left[r]:
            rows += 1
            n = sum(left[r].values())
            print(f"HALF-ROOTED  {r}: {n} declaration(s) still in `TauCeti.{r}` "
                  f"across {len(left[r])} other file(s)")
            for p, c in sorted(left[r].items())[:6]:
                print(f"             {c:3d}  {p}")
            if len(left[r]) > 6:
                print(f"             … and {len(left[r]) - 6} more")
    print(f"# FIRING CONTROL: [{'delta vs ' + base if base else 'ABSOLUTE scan -- pass --base to '
                                'exclude namespaces main already rooted (r592)'}] "
          f"{nfiles} files scanned; {len(rooted)} namespace(s) rooted here "
          f"({', '.join(sorted(rooted))}); {rows} left half-rooted elsewhere. `slice` and "
          f"`parallelns` are FILE-LOCAL and cannot see this (r527 probe: both passed on a PR that "
          f"rooted 9 of IsCoveringMap's 67). A row is the question a reviewer will ask -- answer it "
          f"in the body, do not discover it.", file=sys.stderr)
    return 1 if rows else 0

if __name__ == '__main__':
    sys.exit(main())
