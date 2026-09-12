#!/usr/bin/env python3
"""strictscan.py <snapshot>

Find theorems whose STRICT inequality hypothesis is only ever used non-strictly:
`(h : a < b)` where every textual use of `h` in the proof is `h.le` or
`le_of_lt h`.  Such a hypothesis can be weakened to `a ≤ b` -- the exact
`generality` defect the review pipeline raised three times on this worker's own
PRs (r164 `hδ`, r172 `hε`, r157 `x ∈ Ioi 0`).

SOUNDNESS.  Tactics like `linarith`, `positivity` and `omega` consume context
hypotheses without naming them, so a text scan cannot see those uses.  Any proof
containing one is therefore SKIPPED rather than reported -- the tool trades
recall for the right to be believed.  Comments are masked before matching, since
`theorem` and hypothesis names occur in prose (r171).
"""
import sys, os, re
from collections import defaultdict

root = sys.argv[1]
DECL = re.compile(r'^(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+)*(theorem|lemma)\s+'
                  r'([^\W\d][\w.\'!?]*)')
# tactics that read the local context without naming hypotheses
OPAQUE = re.compile(r'\b(linarith|nlinarith|positivity|omega|polyrith|gcongr|bound|aesop|decide|'
                    r'simp_all|norm_num|field_simp|tauto|fin_cases|interval_cases|continuity|'
                    r'measurability|fun_prop|assumption|solve_by_elim|exact\?|apply\?)\b')
STRICT = re.compile(r'\((h[\w\']*)\s*:\s*([^()]*?<[^()]*?)\)')

def mask_comments(lines):
    inc, out = False, []
    for l in lines:
        # `/--` and `/-!` each CONTAIN `/-`, so summing all three counted a docstring opener
        # two or three times.  A one-line `/-- text -/` then scored o=2, c=1, latching the
        # masker ON and deleting the declaration that followed it -- and its whole proof --
        # until the next line holding `-/`.  Nearly every public declaration carries a
        # one-line docstring, so most of the tree was invisible to this screen.  (r442)
        o = l.count('/-'); c = l.count('-/'); was = inc
        if not inc and o > c: inc = True
        elif inc and c >= 1: inc = False
        out.append('' if (was or (o and not was)) else re.sub(r'--.*$', '', l))
    return out

hits = []
for dp, _, fns in os.walk(root):
    for fn in fns:
        if not fn.endswith('.lean'): continue
        p = os.path.join(dp, fn)
        try: raw = open(p, encoding='utf-8').read().split('\n')
        except Exception: continue
        lines = mask_comments(raw)
        for i, l in enumerate(lines):
            m = DECL.match(l)
            if not m: continue
            # signature = until the proof separator; body = until the next top-level decl
            j = i
            while j < min(i + 40, len(lines)) and not re.search(r':=|\bby\b', lines[j]): j += 1
            sig = ' '.join(' '.join(lines[i:j + 1]).split())
            k = j + 1
            while k < len(lines) and not DECL.match(lines[k]) and not lines[k].startswith('end '):
                k += 1
            # The body must start AFTER the proof separator, not at the start of line `j`.  Line `j`
            # is the LAST signature line, so including it whole dragged the binders in with it:
            # `(hgap : a < b)` contributed a bare `hgap`, `uses` came back ['', '.le'], and
            # `all(u == '.le')` was therefore False.  A declaration was only ever reportable when its
            # signature happened to WRAP, leaving the binder on an earlier line -- which is why this
            # screen found almost nothing.  (r442)
            sep = lines[j].find(':=')
            if sep == -1:
                _mby = re.search(r'\bby\b', lines[j])
                sep = (_mby.start() - 2) if _mby else (len(lines[j]) - 2)
            body = '\n'.join([lines[j][sep + 2:]] + lines[j + 1:k])
            if OPAQUE.search(body): continue                 # cannot see context uses -> skip
            for hname, htype in STRICT.findall(sig):
                uses = re.findall(r'\b' + re.escape(hname) + r'\b(\.le\b)?', body)
                if not uses: continue                        # unused: a different defect
                if all(u == '.le' for u in uses):
                    hits.append((p, i + 1, m.group(2), hname, htype.strip(), len(uses)))

# THE `cost` COLUMN IS A BARE NAME GREP -- do not rank by it (r449).  `callsites()` runs
# `grep -rlF <name>`, so a generic name counts every unrelated occurrence: `of_lt` reported
# "1017 site(s) in 354 file(s)" when `ExchangeableAtMonotone.of_lt` has **zero** real callers.
# Read it as an upper bound for a distinctive name and as noise for a common one; confirm with a
# qualified grep before believing it.  (Same family as r355's dot-lookbehind and r439's short-name
# match: a name is not an identity.)
#
# Two cheap discriminators, learned the hard way (r179, r182):
#   * a weakening on a PRIVATE helper whose caller already holds the strong fact is cosmetic;
#   * a weakening whose call sites must all gain `.le` costs one edit per site, so a widely
#     used lemma is expensive to generalise and pays only if some caller actually benefits.
# Report both so the judgement is made before the build, not after.
import subprocess
def callsites(name):
    try:
        out = subprocess.run(['grep', '-rlF', name, root], capture_output=True, text=True).stdout
        files = [f for f in out.split('\n') if f.strip()]
        out2 = subprocess.run(['grep', '-rhoF', name, root], capture_output=True, text=True).stdout
        return len(files), max(0, out2.count(name) - 1)      # minus the declaration itself
    except Exception:
        return -1, -1

print(f"# {len(hits)} strict hypotheses used only via .le")
print("# cost = files x call-sites that must gain `.le`;  private+cheap = cosmetic")
for p, ln, nm, h, ty, n in sorted(hits, key=lambda r: -r[5])[:25]:
    vis = 'private' if 'private' in open(p, encoding='utf-8').read().split('\n')[ln - 1] else 'PUBLIC'
    nf, nc = callsites(nm)
    print(f"  {p}:{ln}")
    print(f"     {nm}")
    print(f"     ({h} : {ty})   {n} use(s) all `.le`   [{vis}]   cost: {nc} site(s) in {nf} file(s)")
