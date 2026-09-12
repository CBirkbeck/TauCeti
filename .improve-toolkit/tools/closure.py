#!/usr/bin/env python3
"""closure.py <profline-file>

For each prime candidate, measure the INTERFACE COST of lifting its dominant
block: how many names bound EARLIER in the same proof body does that block
reference?  The brief's decisive screen -- "a dominant block that closes over
a dozen local facts would make the helper longer than the parent".

Reads blockprof.py output lines on stdin/file, prints candidates sorted by
ascending closure cost (cheapest interface first).
"""
import re, sys

BIND = re.compile(r'^\s*(?:have|let|set|obtain|intro|rintro|rcases|induction|refine)\b')
# Lean identifiers are routinely non-ASCII (γ' t₀ 𝒪 ℝ). An ASCII-only pattern
# silently scores closure=0 for such proofs -- a FALSE NEGATIVE that promotes
# heavily-capturing proofs to the top of the ranking. Measured 2026-08-24.
NAME = re.compile(r"[^\W\d]['\w\u2080-\u2089]*", re.UNICODE)

def indent(l):
    n=0
    for c in l:
        if c==' ': n+=1
        elif c=='\t': n+=2
        else: break
    return n

def bound_names(line):
    """names introduced by a binder line"""
    out=set()
    s=line.strip()
    m=re.match(r"(?:have|let|set)\s+([^\W\d]['\w\u2080-\u2089]*)", s, re.UNICODE)
    if m: out.add(m.group(1))
    # obtain/rcases/rintro patterns  ⟨a, b, c⟩  or  a b c
    if re.match(r'(?:obtain|rcases|rintro|intro)\b', s):
        for tok in re.findall(r"[⟨,\s]([^\W\d]['\w\u2080-\u2089]*)", s, re.UNICODE):
            out.add(tok)
    return out

rows=[]
for line in open(sys.argv[1]):
    line=line.rstrip('\n')
    if not line.startswith('prime'): continue
    # NOT `snap/...`: hardcoding the snapshot directory name made this tool
    # exit 0 with NO OUTPUT on any snapshot dir but `snap/` -- a silent zero,
    # indistinguishable from "no candidates". Measured 2026-08-24 (round 3).
    m=re.search(r'(\S+\.lean):(\d+) blk@(\d+) (\w+) (\S+)', line)
    if not m: continue
    path, dline, bline, kind, name = m.group(1), int(m.group(2)), int(m.group(3)), m.group(4), m.group(5)
    try: L=open(path, encoding='utf-8').read().split('\n')
    except Exception: continue
    # collect names bound between decl start and block start
    pre=set()
    for i in range(dline, bline-1):
        if i-1 < len(L) and BIND.match(L[i-1]):
            pre |= bound_names(L[i-1])
    # the block itself
    b0=bline-1
    if b0>=len(L): continue
    base=indent(L[b0])
    blk=[L[b0]]
    j=b0+1
    while j<len(L) and (not L[j].strip() or indent(L[j])>base):
        blk.append(L[j]); j+=1
    text='\n'.join(blk)
    stmt=blk[0]
    used = set(NAME.findall(text)) & pre
    used_stmt = set(NAME.findall(stmt)) & pre
    rows.append((len(used), len(used_stmt), len(blk), path, dline, bline, name, sorted(used)))

if not rows:
    sys.exit("closure.py: parsed 0 candidates from %s -- refusing to report a "
             "silent zero. Check the input is blockprof.py output." % sys.argv[1])

rows.sort(key=lambda r:(r[0], r[1]))
for c, cs, n, path, dl, bl, name, used in rows:
    print(f"closure={c:2d} in_stmt={cs:2d} blk={n:3d} {path}:{dl} blk@{bl} {name}")
    print(f"      closes over: {' '.join(used) if used else '(nothing)'}")
