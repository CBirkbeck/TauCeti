#!/usr/bin/env python3
"""blockprof.py <dir> <min_body_lines>

For every proof body of >= n non-blank lines in a Lean tree, report the
largest contiguous TOP-LEVEL block and classify it:

  prime    : one block 25-60 lines, under 75% of body  -> lifting collapses parent
  relocate : largest block >= 75% of body              -> extraction just moves it
  assembly : largest block < 12                        -> many small steps
  partial  : anything else

A "top-level block" is a tactic at the proof's base indentation together
with everything nested under it (its continuation lines).
Counts are CHARACTER-based (unicode-safe), never bytes.
"""
import re, sys, os

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*'
    r'(theorem|lemma|def|instance|abbrev|example)\b')
# top-level commands that terminate a declaration body
STOP = re.compile(r'^(?:@\[|/--|/-!|--|open\b|namespace\b|end\b|section\b|variable\b|'
                  r'import\b|universe\b|attribute\b|local\b|set_option\b|'
                  r'private\b|protected\b|noncomputable\b|theorem\b|lemma\b|def\b|'
                  r'instance\b|abbrev\b|example\b|structure\b|inductive\b|class\b|'
                  r'deriving\b|macro\b|syntax\b|notation\b|declare\b|suppress\b)')

def indent(line):
    n = 0
    for ch in line:
        if ch == ' ': n += 1
        elif ch == '\t': n += 2
        else: break
    return n

def profile_file(path):
    try:
        lines = open(path, encoding='utf-8').read().split('\n')
    except Exception:
        return []
    out = []
    i = 0
    while i < len(lines):
        if indent(lines[i]) == 0 and DECL.match(lines[i]):
            decl_start = i
            m = DECL.match(lines[i])
            kind = m.group(1)
            # name: first token after the keyword
            after = lines[i][m.end():].strip()
            name = after.split()[0].rstrip(':') if after else '?'
            # find ":= by" opening the proof
            j, by_line = i, None
            while j < len(lines) and j < decl_start + 400:
                s = lines[j]
                if re.search(r':=\s*by\s*$', s) or re.search(r':=\s*by\b', s):
                    by_line = j; break
                if j > decl_start and indent(s) == 0 and STOP.match(s) and j != decl_start:
                    break
                j += 1
            if by_line is None:
                i += 1; continue
            # body runs to the next top-level decl/command
            k = by_line + 1
            body = []
            while k < len(lines):
                s = lines[k]
                if s.strip() and indent(s) == 0 and STOP.match(s):
                    break
                body.append(s); k += 1
            while body and not body[-1].strip():
                body.pop()
            nonblank = [s for s in body if s.strip()]
            if len(nonblank) >= MINBODY:
                base = min(indent(s) for s in nonblank)
                # group into top-level blocks
                blocks, cur = [], []
                for s in body:
                    if s.strip() and indent(s) == base:
                        if cur: blocks.append(cur)
                        cur = [s]
                    else:
                        if cur: cur.append(s)
                if cur: blocks.append(cur)
                sizes = [len([x for x in b if x.strip()]) for b in blocks]
                if sizes:
                    largest = max(sizes)
                    bi = sizes.index(largest)
                    bodylen = len(nonblank)
                    frac = largest / bodylen
                    if largest >= 0.75 * bodylen:      verdict = 'relocate'
                    elif largest < 12:                  verdict = 'assembly'
                    elif 25 <= largest <= 60:           verdict = 'prime'
                    else:                               verdict = 'partial'
                    # line number of the largest block's first line
                    off = by_line + 1
                    for bb in blocks[:bi]: off += len(bb)
                    # second-largest: a long proof may need two cuts to clear the 50-line bar,
                    # and `largest` alone cannot say whether two would be enough (r186).
                    second = sorted(sizes, reverse=True)[1] if len(sizes) > 1 else 0
                    out.append(dict(verdict=verdict, body=bodylen, largest=largest,
                                    second=second,
                                    frac=round(frac,2), nblocks=len(sizes),
                                    path=path, line=decl_start+1, blockline=off+1,
                                    kind=kind, name=name))
            i = k
        else:
            i += 1
    return out

root, MINBODY = sys.argv[1], int(sys.argv[2])
res = []
for dp, _, fns in os.walk(root):
    for fn in fns:
        if fn.endswith('.lean'):
            res += profile_file(os.path.join(dp, fn))
res.sort(key=lambda r: -r['largest'])
for r in res:
    print(f"{r['verdict']:8s} body={r['body']:4d} largest={r['largest']:3d} second={r['second']:3d} "
          f"frac={r['frac']:.2f} blocks={r['nblocks']:3d} "
          f"{r['path']}:{r['line']} blk@{r['blockline']} {r['kind']} {r['name']}")
print(f"# total={len(res)} prime={sum(1 for r in res if r['verdict']=='prime')} "
      f"partial={sum(1 for r in res if r['verdict']=='partial')} "
      f"relocate={sum(1 for r in res if r['verdict']=='relocate')} "
      f"assembly={sum(1 for r in res if r['verdict']=='assembly')}", file=sys.stderr)
