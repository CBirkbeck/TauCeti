#!/usr/bin/env python3
"""dupstate.py <snapshot> [min-occurrences]

Find declarations whose CONCLUSIONS coincide up to binder renaming -- two
lemmas proving the same thing under different names.  Distinct from
havedup.py, which compares proof *text*: here the proofs may differ entirely
and the redundancy is in the API surface.

v2.  v1 keyed on the whole signature and therefore grouped by the *binder
prefix*, re-finding the signature duplication havedup already reports.  A
declaration reads `theorem name <bracketed binders> : <conclusion> := proof`,
so the conclusion is everything after the FIRST depth-0 `:` -- every binder
before it is inside (), {} or [].  Keys without a relation symbol are dropped.
"""
import sys, os, re
from collections import defaultdict

root = sys.argv[1]
MIN  = int(sys.argv[2]) if len(sys.argv) > 2 else 2

DECL = re.compile(r'^(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+)*'
                  r'(theorem|lemma)\s+([^\W\d][\w.\'!?]*)')
REL  = re.compile(r'=|≤|<|>|≥|∈|↔|≃|⊆|∣|≠|⟶|≅')

def decl_text(lines, i):
    """Whole declaration head, up to the proof separator.

    The separator is a `:=` or ` by ` at bracket depth 0.  Scanning line by
    line is wrong: a named argument such as `(R := ℤ)` contains `:=` inside
    parentheses, and matching it truncates the statement mid-expression --
    which silently makes two different theorems look identical.  So track
    depth per character.
    """
    text = ' '.join(re.sub(r'--.*$', '', l) for l in lines[i:i + 80])
    depth = 0
    k = 0
    while k < len(text):
        ch = text[k]
        if ch in '([{': depth += 1
        elif ch in ')]}': depth -= 1
        elif depth == 0:
            if text.startswith(':=', k): return ' '.join(text[:k].split())
            if text.startswith(' by ', k) or text.startswith(' by\t', k):
                return ' '.join(text[:k].split())
        k += 1
    return ' '.join(text.split())

def conclusion(s):
    """Text after the first depth-0 `:`; '' if there is none."""
    s = re.sub(r'^(theorem|lemma)\s+[^\W\d][\w.\'!?]*\s*', '', s)
    depth = 0
    for k, ch in enumerate(s):
        if ch in '([{': depth += 1
        elif ch in ')]}': depth -= 1
        elif ch == ':' and depth == 0:
            if k + 1 < len(s) and s[k + 1] == '=':      # `:=` is not a separator
                continue
            return s[k + 1:].strip()
    return ''

def binder_names(sig):
    """Names actually bound by this declaration's signature.

    Only these may be alpha-renamed.  Renaming every short identifier instead
    (the v2 rule) also renames *global* constants such as `GeckConstruction.e`
    and `.f`, which makes two genuinely different theorems look identical.
    """
    out = []
    for grp in re.findall(r'[({\[⦃]\s*([^:()\[\]{}⦃⦄]+?)\s*:', sig):
        for n in grp.split():
            if re.fullmatch(r"[^\W\d][\w']*", n):
                out.append(n)
    return out

def normalise(c, sig=None):
    names, mapping, i = binder_names(sig if sig is not None else c), {}, 0
    for n in names:
        if n not in mapping:
            mapping[n] = f'#{i}'; i += 1
    for n, r in sorted(mapping.items(), key=lambda kv: -len(kv[0])):
        c = re.sub(r'\b' + re.escape(n) + r'\b', r, c)
    return ' '.join(c.split())

groups = defaultdict(list)
for dp, _, fns in os.walk(root):
    for fn in fns:
        if not fn.endswith('.lean'): continue
        p = os.path.join(dp, fn)
        try: lines = open(p, encoding='utf-8').read().split('\n')
        except Exception: continue
        # mask block comments: `theorem` occurs in prose inside /-- ... -/ and /-! ... -/
        incomment, masked = False, []
        for l in lines:
            # `/--` and `/-!` each CONTAIN `/-`; summing all three counted one opener twice,
            # so a one-line `/-- text -/` latched the masker ON and deleted what followed.
            # Found in strictscan at r442, propagated by copy-paste.  (r444)
            opens = l.count('/-')
            closes = l.count('-/')
            was = incomment
            if not incomment and opens > closes: incomment = True
            elif incomment and closes >= 1: incomment = False
            masked.append('' if (was or (opens and not was)) else l)
        for i, l in enumerate(masked):
            m = DECL.match(l)
            if not m: continue
            sig = decl_text(lines, i)
            c = conclusion(sig)
            if len(c) < 25 or not REL.search(c): continue
            groups[normalise(c, sig)].append((p, i + 1, m.group(2)))

out = [(k, v) for k, v in groups.items() if len(v) >= MIN]
out.sort(key=lambda kv: -(len(kv[0]) * len(kv[1])))
print(f"# {len(out)} conclusion-duplicate groups")
for k, v in out[:30]:
    if len({nm for _, _, nm in v}) == 1: continue      # same name in variants: skip
    print(f"\n=== {len(v)} declarations share a conclusion ({len(k)} chars) ===")
    for p, ln, nm in v: print(f"    {p}:{ln}  {nm}")
    print(f"    ---- {k[:180]}")
