#!/usr/bin/env python3
"""dupinproof.py <snapshot> <min_body_lines> [min_block]

The #5270 shape: a multi-line tactic block repeated INSIDE one proof body.
Such a block has two consumers by construction, which answers proof-quality's
"inline genuine one-offs" outright instead of arguing against it.

Restricted to proofs whose body already clears <min_body_lines>, so this
finds targets inside the standing bar rather than beside it.
"""
import sys, os, re, hashlib
from collections import defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import importlib.util
spec = importlib.util.spec_from_file_location(
    "bp", os.path.join(os.path.dirname(os.path.abspath(__file__)), "blockprof.py"))

def norm(l):
    l = re.sub(r'--.*$', '', l)
    return ' '.join(l.split())

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*'
    r'(theorem|lemma|def|instance|abbrev|example)\b')
STOP = re.compile(r'^(?:@\[|/--|/-!|--|open\b|namespace\b|end\b|section\b|variable\b|'
                  r'import\b|universe\b|attribute\b|local\b|set_option\b|'
                  r'private\b|protected\b|noncomputable\b|theorem\b|lemma\b|def\b|'
                  r'instance\b|abbrev\b|example\b|structure\b|inductive\b|class\b|'
                  r'deriving\b|macro\b|syntax\b|notation\b|declare\b|suppress\b)')

def indent(s):
    n = 0
    for ch in s:
        if ch == ' ': n += 1
        elif ch == '\t': n += 2
        else: break
    return n

def bodies(path):
    try: L = open(path, encoding='utf-8').read().split('\n')
    except Exception: return
    i = 0
    while i < len(L):
        if indent(L[i]) == 0 and DECL.match(L[i]):
            start = i
            after = L[i][DECL.match(L[i]).end():].strip()
            name = after.split()[0].rstrip(':') if after else '?'
            by = None
            j = i
            while j < len(L) and j < start + 400:
                if re.search(r':=\s*by\b', L[j]): by = j; break
                if j > start and indent(L[j]) == 0 and STOP.match(L[j]): break
                j += 1
            if by is None: i += 1; continue
            k = by + 1; body = []
            while k < len(L):
                if L[k].strip() and indent(L[k]) == 0 and STOP.match(L[k]): break
                body.append(L[k]); k += 1
            while body and not body[-1].strip(): body.pop()
            yield name, start + 1, by + 2, body
            i = k
        else:
            i += 1

root = sys.argv[1]
MINBODY = int(sys.argv[2])
MINBLK = int(sys.argv[3]) if len(sys.argv) > 3 else 3

hits = []
for dp, _, fns in os.walk(root):
    for fn in fns:
        if not fn.endswith('.lean'): continue
        p = os.path.join(dp, fn)
        for name, dline, bline, body in bodies(p):
            nb = [s for s in body if s.strip()]
            if len(nb) < MINBODY: continue
            seen = defaultdict(list)
            for size in range(MINBLK, min(30, len(nb))):
                for a in range(0, len(nb) - size + 1):
                    win = [norm(x) for x in nb[a:a+size]]
                    if any(len(x) <= 3 for x in win): continue
                    seen[hashlib.sha1('\n'.join(win).encode()).hexdigest()].append((a, size))
            best = None
            for h, occ in seen.items():
                if len(occ) < 2: continue
                size = occ[0][1]
                starts = sorted(a for a, _ in occ)
                # require the repeats to be disjoint
                keep = []
                for a in starts:
                    if not keep or a >= keep[-1] + size: keep.append(a)
                if len(keep) < 2: continue
                if best is None or size * len(keep) > best[0]:
                    best = (size * len(keep), size, len(keep), keep, nb[keep[0]:keep[0]+size])
            if best:
                hits.append((best[0], len(nb), best[1], best[2], p, dline, name, best[4]))
# RANK BY CROSSING, NEVER BY `score` (r85, re-learned the hard way in r360/r361).
#
# `score` is size*times -- raw lines saved.  It is the WRONG order for this lane, because the
# proof-quality bar is at 50 and a saving that leaves the body above 50 buys nothing.  A 14-line
# saving on a 125-line body (`connected_diagramGraph_cartanMatrix`, 7x3) tops the score table and
# is worthless; the highest-score rows are Lyons/Irreducible, which r85 declined for exactly this
# reason and which r360 chased anyway because the tool still printed them first.
#
#     after = body - size*(times-1) + times     (one call line per former occurrence)
#
# CROSSES means body > 50 and after <= 50.  Those are the only rows this lane can use, so they are
# printed first and the rest are marked.  Sorting is by `after` ascending within the crossing set.
BAR = 50
def after_of(blen, size, times):
    return blen - size * (times - 1) + times
hits.sort(key=lambda h: (after_of(h[1], h[2], h[3]) > BAR or h[1] <= BAR,
                         after_of(h[1], h[2], h[3])))
ncross = 0
for score, blen, size, times, p, dline, name, txt in hits:
    aft = after_of(blen, size, times)
    crosses = blen > BAR and aft <= BAR
    ncross += crosses
    print(f"{'CROSSES' if crosses else '   -   '} body={blen:4d} after={aft:4d} "
          f"dup={size:2d} lines x{times} score={score:4d}  {p}:{dline} {name}")
    for t in txt: print("        | " + t.strip()[:110])
print(f"# FIRING CONTROL: {len(hits)} proofs carry an internal duplicate; "
      f"{sum(1 for h in hits if h[1] > BAR)} have body > {BAR}; "
      f"{ncross} CROSS (after <= {BAR}) and are the only usable rows. "
      f"Ranking by `score` instead surfaces the biggest SAVING, which r85 established is the wrong "
      f"criterion -- do not re-rank.", file=sys.stderr)
