#!/usr/bin/env python3
"""deadfix.py -- apply the corrections `deadpath.py` reports, reading its output on stdin.

    python3 deadpath.py TauCeti "$MATHLIB" $FILES | python3 deadfix.py

Screen-driven, like `xqualify.py` and `endfix.py`: only the exact (file, line, token) sites the
screen names, and the current text is asserted before anything is written.

TWO RULES, and the second one grows the PR on purpose.  A DEAD PATH is replaced by the declaration
the screen resolved.  A DEAD NS -- `open TauCeti.WeierstrassCurve` after every declaration has left
that namespace -- is repaired by dropping the `TauCeti.` prefix, and those files are usually NOT in
the diff yet: emptying a namespace breaks files the PR never touched, and the repo rule is to update
every in-repository use in the same PR.

A row whose suggestion is absent is a hard stop, never a silent skip: an over-qualified name with no
resolution is a question for a person, not something to guess at.
"""
import sys, re
from collections import defaultdict

PATH = re.compile(r'^DEAD PATH\s+(\S+):(\d+)\s+`([^`]+)` is not a declaration'
                  r'(?: -- did you mean `([^`]+)`\?)?')
NS = re.compile(r'^DEAD NS\s+(\S+):(\d+)\s+`([^`]+)` no longer holds')

edits = defaultdict(list)
for L in sys.stdin.read().split('\n'):
    m = PATH.match(L)
    if m:
        if not m.group(4):
            sys.exit(f"deadfix: {m.group(1)}:{m.group(2)} `{m.group(3)}` has no resolution -- "
                     f"stopping. Decide this one by hand.")
        edits[m.group(1)].append((int(m.group(2)), m.group(3), m.group(4))); continue
    m = NS.match(L)
    if m:
        edits[m.group(1)].append((int(m.group(2)), m.group(3), m.group(3)[len('TauCeti.'):]))

n = 0
for path, items in sorted(edits.items()):
    L = open(path, encoding='utf-8').read().split('\n')
    for ln, old, new in sorted(items, reverse=True):
        raw = L[ln - 1]
        spans = [mm.span() for mm in
                 re.finditer(r'(?<![\w.])' + re.escape(old) + r'(?![\w])', raw)]
        if not spans:
            sys.exit(f"deadfix: {path}:{ln} no longer contains `{old}` -- refusing to guess.")
        for a, b in reversed(spans):
            raw = raw[:a] + new + raw[b:]
            n += 1
        L[ln - 1] = raw
    open(path, 'w', encoding='utf-8').write('\n'.join(L))
print(f"deadfix: {n} occurrence(s) across {len(edits)} file(s)")
