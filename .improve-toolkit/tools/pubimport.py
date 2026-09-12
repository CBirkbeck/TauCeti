#!/usr/bin/env python3
"""pubimport.py <snapshot>   ** RETIRED r191 -- DO NOT RUN **

RETIRED, UNSOUND.  Measured hit rate 2323 of 4090 checked (57%) -- a defect rate
that high means the predicate is wrong, not that the tree is broken.  Reason:
`public import M` declares that anyone importing THIS file also gets `M`.  It is
justified by what DOWNSTREAM consumers need, not by whether `M`'s names appear in
this file's own signatures, so "no name of M in a public signature here" is not
evidence of anything.  Excluding re-export hubs moved the rate by 1 point.

The correct oracle is the module system itself (`lake exe module-system`), which
knows the visibility surface.  Kept only as a record of the attempt.


Find `public import M` where nothing from `M` appears in any PUBLIC declaration's
signature in the importing file -- i.e. `M` is a proof-only dependency being
re-exported through the module's API.

This is the defect `api-design` raised on #5576 (r170):
    "`public import Mathlib.Data.Set.PowersetCard` exposes a proof-only
     dependency through the canonical module API.  Fix: change it to a plain
     `import`; keep public imports only for dependencies needed by public
     declarations."

SOUNDNESS.  A module can be needed without any of its names appearing: instances
are found by search and notation by parsing.  So an import is SKIPPED whenever
its module declares an `instance`, `notation`, `macro`, `syntax`, `class` or
`structure` -- reporting those would be a claim this tool cannot support (r190).
Only TauCeti-internal imports are checked; Mathlib's are out of scope here.
"""
import sys, os, re, collections

root = sys.argv[1]
IMP  = re.compile(r'^\s*public\s+import\s+(TauCeti[A-Za-z0-9_.]*)\s*$')
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+|'
                  r'partial\s+|unsafe\s+|scoped\s+|local\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|'
                  r'notation|macro|syntax)\s*(?:\([^)]*\)\s*)?'
                  r'(?:_root_\.)?([A-Za-z_][A-Za-z0-9_.\'!?]*)?')
IMPLICIT = {'instance', 'structure', 'class', 'inductive', 'notation', 'macro', 'syntax'}

def mask(lines):
    inc, out = False, []
    for l in lines:
        o = l.count('/--') + l.count('/-!') + l.count('/-'); c = l.count('-/'); was = inc
        if not inc and o > c: inc = True
        elif inc and c >= 1: inc = False
        out.append('' if (was or (o and not was)) else re.sub(r'--.*$', '', l))
    return out

mod_lines, provides, implicit_mod = {}, collections.defaultdict(set), set()
for dp, _, fns in os.walk(root):
    for fn in fns:
        if not fn.endswith('.lean'): continue
        p = os.path.join(dp, fn)
        mod = 'TauCeti.' + os.path.relpath(p, root)[:-5].replace(os.sep, '.')
        try: ls = mask(open(p, encoding='utf-8').read().split('\n'))
        except Exception: continue
        mod_lines[mod] = (p, ls)
        for l in ls:
            m = DECL.match(l)
            if not m: continue
            if m.group(1) in IMPLICIT: implicit_mod.add(mod)
            if m.group(2): provides[mod].add(m.group(2).split('.')[-1])

checked = skipped = 0
hits = []
for mod, (p, ls) in mod_lines.items():
    # public signatures in this file: decl line up to the proof separator
    pub_sig = []
    for i, l in enumerate(ls):
        m = DECL.match(l)
        if not m or m.group(1) in ('notation', 'macro', 'syntax'): continue
        if re.match(r'\s*private\s', l): continue
        j = i
        while j < min(i + 30, len(ls)) and not re.search(r':=|\bby\b', ls[j]): j += 1
        pub_sig.append(' '.join(ls[i:j + 1]))
    blob = ' '.join(pub_sig)
    toks = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", blob))
    # A hub module -- one that declares nothing of its own -- exists to re-export its
    # submodules, which is precisely what `public import` is for.  Not a defect.
    if not pub_sig and not any(DECL.match(l) for l in ls): continue
    for l in ls:
        mi = IMP.match(l)
        if not mi: continue
        dep = mi.group(1)
        if dep not in provides: continue
        if dep in implicit_mod: skipped += 1; continue
        checked += 1
        if not (provides[dep] & toks):
            hits.append((p, dep, len(provides[dep])))

print(f"# FIRING CONTROL: {checked} TauCeti `public import`s checked, "
      f"{skipped} skipped (module provides instances/notation/structures)")
print(f"# {len(hits)} public imports whose module contributes no name to a public signature")
for p, dep, n in hits[:25]:
    print(f"  {p}\n      public import {dep}   ({n} names, none in a public signature here)")
