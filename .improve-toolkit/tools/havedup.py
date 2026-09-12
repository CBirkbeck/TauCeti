#!/usr/bin/env python3
"""havedup.py <snapshot> [minlines]

Find identical multi-line proof blocks repeated across the tree.
Normalises whitespace, ignores comments, and reports groups sorted by
(lines x occurrences) -- the duplication that costs the most.
"""
import sys, os, re, hashlib
from collections import defaultdict

root = sys.argv[1]
MIN = int(sys.argv[2]) if len(sys.argv) > 2 else 6

def norm(l):
    l = re.sub(r'--.*$', '', l)
    return ' '.join(l.split())

groups = defaultdict(list)
for dp, _, fns in os.walk(root):
    for fn in fns:
        if not fn.endswith('.lean'): continue
        p = os.path.join(dp, fn)
        try: lines = open(p, encoding='utf-8').read().split('\n')
        except Exception: continue
        n = len(lines)
        # sliding windows of MIN..MIN+24 normalised non-blank lines
        for size in range(MIN, MIN + 25):
            for i in range(0, n - size):
                win = lines[i:i+size]
                nw = [norm(x) for x in win]
                if any(not x for x in nw): continue
                if sum(1 for x in nw if len(x) > 3) < size: continue
                key = hashlib.sha1('\n'.join(nw).encode()).hexdigest()
                groups[(key, size)].append((p, i+1, '\n'.join(win)))

seen_report = []
for (key, size), occ in groups.items():
    files = {o[0] for o in occ}
    if len(occ) >= 2 and len(files) >= 2:
        seen_report.append((size * len(occ), size, occ))
seen_report.sort(key=lambda x: -x[0])

printed, covered = 0, set()
for score, size, occ in seen_report:
    sig = tuple(sorted((o[0], o[1] // 5) for o in occ))
    if sig in covered: continue
    covered.add(sig)
    print(f"=== {size} lines x {len(occ)} occurrences (score {score}) ===")
    for p, ln, _ in occ:
        print(f"    {p}:{ln}")
    print("    ---- text ----")
    for l in occ[0][2].split('\n'):
        print("    | " + l)
    print()
    printed += 1
    if printed >= 12: break
