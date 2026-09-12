#!/usr/bin/env python3
"""impliedscan.py <snapshot>

Find ORDER hypotheses that the declaration's other hypotheses already imply.

Companion to strictscan.py.  strictscan asks "is this hypothesis's strictness
used?"; this asks the strictly stronger question the review pipeline asked on
#5618 -- "is this hypothesis derivable from the others?" -- which is what caught
three of that PR's four instances.

Sound by construction: it only uses transitivity of `<` and `≤` in a linear
order, which holds unconditionally.  Membership binders are expanded to their
defining inequalities (`t ∈ Ioo a b` gives `a < t` and `t < b`, and so on).
A hypothesis is reported only when the REMAINING binders already give a path
from its left side to its right side that is at least as strict.
"""
import sys, os, re
from collections import defaultdict

root = sys.argv[1]
DECL = re.compile(r'^(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+)*(theorem|lemma)\s+'
                  r'([^\W\d][\w.\'!?]*)')
V = r"[^\W\d][\w'₀₁₂]*"
# a term may be a bare name or a name offset by another: `t₀ - ρ`, `t₀ + ρ`
T = r"[^\W\d][\w'₀₁₂]*(?:\s*[+-]\s*[^\W\d][\w'₀₁₂]*)?"
POS = re.compile(r'\((' + V + r')\s*:\s*0\s*(<|≤)\s*(' + V + r')\)')
OFF = re.compile(r'^(' + V + r')\s*([+-])\s*(' + V + r')$')
NE   = re.compile(r'\((' + V + r')\s*:\s*(' + T + r')\s*≠\s*(' + T + r')\)')
ORD  = re.compile(r'\((' + V + r')\s*:\s*(' + T + r')\s*(<|≤)\s*(' + T + r')\)')
MEM  = re.compile(r'\((' + V + r')\s*:\s*(' + T + r')\s*∈\s*(Ioo|Icc|Ico|Ioc)\s+(' + T + r')\s+(' + T + r')\)')
IVAL = {'Ioo': ('<', '<'), 'Icc': ('≤', '≤'), 'Ico': ('≤', '<'), 'Ioc': ('<', '≤')}

def mask(lines):
    inc, out = False, []
    for l in lines:
        # `/--` and `/-!` each CONTAIN `/-`, so summing all three counted one opener twice or
        # thrice.  A one-line `/-- text -/` scored o>=2, c=1, latching the masker ON and
        # deleting the declaration that followed until the next line holding `-/`.  Found in
        # strictscan at r442 and propagated by copy-paste to this file too.  (r444)
        o = l.count('/-'); c = l.count('-/'); was = inc
        if not inc and o > c: inc = True
        elif inc and c >= 1: inc = False
        out.append('' if (was or (o and not was)) else re.sub(r'--.*$', '', l))
    return out

def reachable(edges, src, dst):
    """Best strictness of a path src -> dst: '<', '≤', or None."""
    best, seen, stack = None, set(), [(src, '≤')]
    while stack:
        u, strict = stack.pop()
        if (u, strict) in seen: continue
        seen.add((u, strict))
        for v, rel in edges.get(u, ()):
            s2 = '<' if (strict == '<' or rel == '<') else '≤'
            if v == dst:
                if s2 == '<': return '<'
                best = best or '≤'
            stack.append((v, s2))
    return best

hits = []
precond1 = precond2 = ndecl = 0
for dp, _, fns in os.walk(root):
    for fn in fns:
        if not fn.endswith('.lean'): continue
        p = os.path.join(dp, fn)
        try: lines = mask(open(p, encoding='utf-8').read().split('\n'))
        except Exception: continue
        for i, l in enumerate(lines):
            m = DECL.match(l)
            if not m: continue
            ndecl += 1
            j = i
            while j < min(i + 40, len(lines)) and not re.search(r':=|\bby\b', lines[j]): j += 1
            sig = ' '.join(' '.join(lines[i:j + 1]).split())
            facts = []                                   # (hyp-name, u, rel, v)
            for h, u, rel, v in ORD.findall(sig): facts.append((h, u, rel, v))
            for h, t, kind, a, b in MEM.findall(sig):
                lo, hi = IVAL[kind]
                facts.append((h, a, lo, t)); facts.append((h, t, hi, b))
            # `0 < ρ` (or `0 ≤ ρ`) licenses `t - ρ < t` and `t < t + ρ` for any term `t ± ρ`
            pos = {m0[2]: m0[1] for m0 in POS.findall(sig)}
            for _, u0, _, v0 in list(facts):
                for term in (u0, v0):
                    mo = OFF.match(term.strip())
                    if not mo: continue
                    base, sign, off = mo.group(1), mo.group(2), mo.group(3)
                    if off not in pos: continue
                    rel = pos[off]
                    if sign == '-': facts.append(('#offset', term, rel, base))
                    else:           facts.append(('#offset', base, rel, term))
            # `≠` hypotheses: implied when the rest gives a STRICT path either way
            nes = [(h, u, v) for h, u, v in NE.findall(sig)]
            for h, u, v in nes:
                edges = defaultdict(list)
                for hh, a, r, b in facts:
                    if hh != h: edges[a].append((b, r))
                if reachable(edges, u, v) == '<' or reachable(edges, v, u) == '<':
                    hits.append((p, i + 1, m.group(2), h, f"{u} ≠ {v}", '< (strict path)'))
            if len(facts) >= 1: precond1 += 1
            if len(facts) >= 2: precond2 += 1
            if len(facts) < 2: continue
            names = {h for h, *_ in facts}
            for target in names:
                tgt = [f for f in facts if f[0] == target]
                if len(tgt) != 1: continue               # only single-edge hypotheses
                _, u, rel, v = tgt[0]
                edges = defaultdict(list)
                for h, a, r, b in facts:
                    if h != target: edges[a].append((b, r))
                got = reachable(edges, u, v)
                if got and (got == '<' or rel == '≤'):
                    hits.append((p, i + 1, m.group(2), target, f"{u} {rel} {v}", got))

# A zero is only informative with a control on the precondition (r184): how often does a
# declaration even carry two order facts that *could* imply one another?
print(f"# FIRING CONTROL: {ndecl} declarations scanned; {precond1} carry an order/membership "
      f"binder; {precond2} carry two or more (the precondition for an implication)")
print(f"# {len(hits)} order hypotheses implied by the other binders")
for p, ln, nm, h, what, got in hits[:30]:
    print(f"  {p}:{ln}\n     {nm}   ({h} : {what})   implied ({got}) by the rest")
