#!/usr/bin/env python3
"""nsshadow.py <snapshot>

Find `namespace X` blocks where `X` is a well-known ROOT namespace but the block
is nested inside another namespace, so declarations inside get names like
`TauCeti.Probability.Real.foo` that read as `Real.foo` and are neither.

This is the defect the `naming` rubric raised on #5579 (r160):
    "declared in `TauCeti.Probability.Real`, contrary to the convention that
     dot-notation material on an existing Mathlib type belongs in that type's
     namespace" -- fixed there by `theorem _root_.Real.foo`.

Comments are masked before matching (r171): `namespace` occurs in prose.
Prints a firing control so a zero is interpretable (r184).
"""
import sys, os, re
from collections import Counter

root = sys.argv[1]
ROOTNS = {"Real","Nat","Int","Rat","Complex","Finset","Set","List","Array","Matrix","Polynomial",
          "Filter","Function","Multiset","Sym","Equiv","Prod","Sum","Option","Fin","ENNReal",
          "NNReal","MeasureTheory","Topology","Metric","Ideal","Subgroup","Submodule","Module",
          "Ring","Field","Group","Monoid","Order","Bool","Char","String","Sigma","Quot","Quotient"}
NS  = re.compile(r'^namespace\s+([^\W\d][\w.\']*)\s*$')
END = re.compile(r'^end\s+([^\W\d][\w.\']*)\s*$')

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

hits, total_ns, root_level = [], 0, Counter()
for dp, _, fns in os.walk(root):
    for fn in fns:
        if not fn.endswith('.lean'): continue
        p = os.path.join(dp, fn)
        try: lines = mask(open(p, encoding='utf-8').read().split('\n'))
        except Exception: continue
        # Explicit `variable (x y : T)` names IN SCOPE at each line.  `variable` bindings are
        # scoped to the enclosing `section`/`namespace`, so a whole-file union (r193) let an
        # explicit binder 170 lines below suppress a block above it -- a false negative that hid a
        # real target.  Track a scope stack instead and snapshot the in-scope set per line.
        evars_at, scopes, cur = [], [[]], set()
        for vl in lines:
            evars_at.append(frozenset(cur))
            if re.match(r'^\s*(?:section|namespace)\b', vl):
                scopes.append([])
            elif re.match(r'^\s*end\b', vl):
                if len(scopes) > 1:
                    for nm in scopes.pop(): cur.discard(nm)
            else:
                vm = re.match(r'^\s*variable\s+(.*)$', vl)
                if vm:
                    for g in re.finditer(r"\(\s*([^\W\d][\w' ]*?)\s*:", vm.group(1)):
                        for nm in g.group(1).split():
                            scopes[-1].append(nm); cur.add(nm)
        stack = []
        for i, l in enumerate(lines):
            m = NS.match(l)
            if m:
                total_ns += 1
                name = m.group(1)
                if name in ROOTNS:
                    if stack:
                        # size the block: how many declarations would a rename touch?
                        depth, ndecl, j = 0, 0, i + 1
                        while j < len(lines):
                            if NS.match(lines[j]): depth += 1
                            elif END.match(lines[j]):
                                if depth == 0: break
                                depth -= 1
                            elif re.match(r'^(?:private |protected |nonrec |noncomputable |'
                                          r'@\[[^\]]*\]\s*)*(theorem|lemma|def|abbrev|instance|'
                                          r'structure|inductive)\b', lines[j]): ndecl += 1
                            j += 1
                        # NARROWING (r188): `TauCeti.X` mirroring Mathlib's `X` is an established
                        # repository convention (5+ files use `namespace Matrix` inside `TauCeti`),
                        # so nesting alone is not a defect.  The `naming` rubric's actual criterion
                        # on #5579 was dot-notation: the lemma's FIRST EXPLICIT argument had type
                        # head `X`, so it belonged in root `X`.  Flag only those.
                        dotnote = []
                        depth2, j2 = 0, i + 1
                        while j2 < len(lines):
                            if NS.match(lines[j2]): depth2 += 1
                            elif END.match(lines[j2]):
                                if depth2 == 0: break
                                depth2 -= 1
                            dm = re.match(r'^(?:private |protected |nonrec |noncomputable )*'
                                          r'(theorem|lemma)\s+([^\W\d][\w.\']*)', lines[j2])
                            if dm:
                                sig = ' '.join(lines[j2:j2 + 8])
                                # r193: an EXPLICIT `variable (x : T)` in scope precedes the
                                # signature's own binders, so if the signature mentions such an
                                # `x`, the first explicit argument is `x`, not the first `(y : U)`
                                # written here.  #5628's `variable (k : Type u)` made exactly this
                                # mistake: the name moved to the right namespace with the wrong
                                # argument order, and `M.foo` never elaborated.
                                # NB: this loop increments `j2` at the bottom, so a bare `continue`
                                # here would spin forever.  Guard with a flag instead.
                                inscope = evars_at[j2] if j2 < len(evars_at) else frozenset()
                                shadowed = any(re.search(r'\b' + re.escape(ev) + r'\b', sig)
                                               for ev in inscope)
                                if not shadowed:
                                    fb = re.search(r'\(\s*[^\W\d][\w\']*\s*:\s*([^\W\d][\w.]*)', sig)
                                    if fb and fb.group(1).split('.')[0] == name:
                                        dotnote.append((j2 + 1, dm.group(2), fb.group(1)))
                            j2 += 1
                        if dotnote:
                            hits.append((p, i + 1, name, '.'.join(stack), ndecl, dotnote))
                    else:     root_level[name] += 1
                stack.append(name); continue
            e = END.match(l)
            if e and stack and stack[-1] == e.group(1): stack.pop()

print(f"# FIRING CONTROL: {total_ns} `namespace` blocks scanned; "
      f"{sum(root_level.values())} root-level uses of a well-known namespace "
      f"(correct usage) across {len(root_level)} names")
print(f"# {len(hits)} nested lookalike namespaces")
hits.sort(key=lambda h: h[4])
print("# sorted by block size: a rename touches every declaration inside, plus its call sites")
for p, ln, name, under, nd, dn in hits[:30]:
    print(f"  {p}:{ln}   namespace {name} inside `{under}`  ({nd} decls)")
    for dl, dname, head in dn:
        print(f"      line {dl}: {dname}   first explicit arg has type head `{head}` -> belongs in root `{name}`")
