#!/usr/bin/env python3
"""endfix.py -- apply the `end` corrections `nsbalance.py` reports, reading its output on stdin.

    python3 nsbalance.py "$(git merge-base origin/main HEAD)" $FILES | python3 endfix.py

Same discipline as `xqualify.py`: driven by the screen, never by a pattern.  Each row names the
line, what stands there, and what the scope at the other end requires, so the edit is determined
rather than inferred -- and the current text is asserted before anything is written.  That is the
whole lesson of r551: the pass that CREATED these breaks rewrote "the next `end`", a positional
guess that is wrong the moment anything nests.

Re-run `nsbalance` afterwards.  Fixing one end can change what the stack expects at the next, so
the result is only trustworthy when a second pass reports zero.
"""
import sys, re
from collections import defaultdict

BARE = re.compile(r'^UNBALANCED\s+(\S+):(\d+): a bare `end` closes the \w+ opened at line \d+ '
                  r'\(`([^`]+)`\) -- expected `end ([^`]+)`')
NAMED = re.compile(r'^UNBALANCED\s+(\S+):(\d+): `end ([^`]+)` closes the \w+ opened at line \d+ '
                   r'\(anonymous\) -- expected a bare `end`')

edits = defaultdict(list)                  # path -> [(line, current, replacement)]
for L in sys.stdin.read().split('\n'):
    m = BARE.match(L)
    if m:
        edits[m.group(1)].append((int(m.group(2)), 'end', f'end {m.group(4)}')); continue
    m = NAMED.match(L)
    if m:
        edits[m.group(1)].append((int(m.group(2)), f'end {m.group(3)}', 'end'))

n = 0
for path, items in sorted(edits.items()):
    L = open(path, encoding='utf-8').read().split('\n')
    for ln, cur, new in sorted(items, reverse=True):
        if L[ln - 1].rstrip() != cur:
            sys.exit(f"endfix: {path}:{ln} holds {L[ln - 1]!r}, not {cur!r} -- refusing to guess. "
                     f"Re-run nsbalance against the current tree.")
        L[ln - 1] = new
        n += 1
    open(path, 'w', encoding='utf-8').write('\n'.join(L))
print(f"endfix: {n} `end` line(s) corrected across {len(edits)} file(s)")
