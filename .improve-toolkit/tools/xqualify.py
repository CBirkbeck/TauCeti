#!/usr/bin/env python3
"""xqualify.py -- apply the qualifications `xsibling.py` reports, reading its output on stdin.

    python3 xsibling.py TauCeti "$(git merge-base origin/main HEAD)" $FILES | python3 xqualify.py

DRIVEN BY THE SCREEN, NEVER BY A NAME LIST.  This is the distinction that matters, and #6056 is
what happens without it.  The retarget pass that built that PR swept a set of short NAMES through
the changed files, and one of those names was `ext` -- the shortest suffix of
`RootPairing.weylGroup.ext` -- so it rewrote `@[ext]` into `@[RootPairing.weylGroup.ext]` and CI
answered `Unknown attribute`.  A name sweep cannot tell a reference from an attribute or a tactic.

`xsibling` already makes that judgement per OCCURRENCE: attribute brackets and tactic-position
tokens are classified out and never appear as BREAKS.  So this fixer touches only the exact
(file, line, suffix) sites the screen names, replaces each with the full declaration name the
screen resolved, and asserts the site still matches before writing.  A site that has moved is a
hard error, not a silent skip (r550: an `os.path.exists` filter in `xsibling` itself quietly
dropped a whole target list and reported "nothing to check").

Widths are NOT fixed here: a qualification lengthens the line, and wrapping Lean needs judgement
about where the break goes.  Run the width check afterwards and wrap by hand -- and iterate to a
fixed point, because wrapping a very long line can leave a continuation that is itself too long
(r549: 101 wraps, then 5 more).
"""
import sys, re
from collections import defaultdict

rows = defaultdict(list)
for m in re.finditer(r'^BREAKS\s+(\S+):(\d+)\s+`([^`]+)` -> `([^`]+)`', sys.stdin.read(), re.M):
    rows[m.group(1)].append((int(m.group(2)), m.group(3), m.group(4)))

def mask(raw):
    blank = lambda m: ' ' * len(m.group(0))
    c = re.sub(r'`[^`]*`', blank, raw)
    c = re.sub(r'"(?:[^"\\]|\\.)*"', blank, c)
    c = re.sub(r'--.*$', blank, c)
    return re.sub(r'@\[[^\]]*\]', blank, c)

total = 0
for path, items in sorted(rows.items()):
    L = open(path, encoding='utf-8').read().split('\n')
    for ln, suf, full in sorted(items, reverse=True):
        raw = L[ln - 1]
        spans = [m.span() for m in re.finditer(r'(?<![\w.])' + re.escape(suf) + r'(?!\w)', mask(raw))]
        if not spans:
            sys.exit(f"xqualify: {path}:{ln} no longer contains a bare `{suf}` -- refusing to "
                     f"guess. Re-run xsibling against the current tree.")
        for a, b in reversed(spans):
            raw = raw[:a] + full + raw[b:]
            total += 1
        L[ln - 1] = raw
    open(path, 'w', encoding='utf-8').write('\n'.join(L))
print(f"xqualify: {total} occurrence(s) at {sum(len(v) for v in rows.values())} site(s) "
      f"across {len(rows)} file(s)")
