#!/usr/bin/env python3
"""docghost.py <snapshot>

Find module docstrings that advertise a declaration which is not in that file.

This is the defect `placement` and `documentation` both raised on #5579 (r160):
    "The Basic module advertises `gammaKernel_mul_exp_mul_pow_div_factorial`,
     although the declaration lives in downstream `Gamma/Poisson.lean` and is
     unavailable to users importing Basic."

Unlike a namespacing convention, a doc/code mismatch is a defect on its face:
the file claims something it does not contain.  Matching is on the LEAF name, so
a bullet may name the declaration with any qualification.

Prints a firing control (r184): how many advertised names were found, and how
many resolved inside their own file.
"""
import sys, os, re

root = sys.argv[1]
# THE ROOT MUST BE THE DIRECTORY *CONTAINING* THE MODULES, i.e. `<snap>/TauCeti`, because module
# names are built as `'TauCeti.' + relpath(p, root)`.  Handed `<snap>` instead, every module comes
# out `TauCeti.TauCeti.X`, no import ever matches the closure, and every advertised-elsewhere name
# is reported unreachable: on the live tree that is **118 findings instead of 4** (r453).
# Every other screen tool takes `<snap>`, so this one argument is a standing trap -- absorb it.
if os.path.isdir(os.path.join(root, "TauCeti")):
    root = os.path.join(root, "TauCeti")
    print(f"# note: descended into {root} -- module names are built relative to the directory "
          f"holding them, not to the snapshot root (r453)", file=sys.stderr)
# a module-doc bullet naming a declaration: `* `Some.Name` — ...`
BULLET = re.compile(r'^\s*[*-]\s*`([^\W\d][\w.\'!?]*)`')
DECL   = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+|'
                    r'partial\s+|unsafe\s+|scoped\s+|local\s+)*'
                    r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)\s*'
                    # `instance (priority := 100) Name` -- a parenthesised modifier, not an attribute
                    r'(?:\([^)]*\)\s*)?'
                    r'(?:_root_\.)?([^\W\d][\w.\'!?]*)')

advertised = resolved = 0
hits = []
for dp, _, fns in os.walk(root):
    for fn in fns:
        if not fn.endswith('.lean'): continue
        p = os.path.join(dp, fn)
        try: lines = open(p, encoding='utf-8').read().split('\n')
        except Exception: continue
        # module docstring: the first `/-! ... -/` block
        doc, inside = [], False
        for i, l in enumerate(lines):
            if not inside and l.lstrip().startswith('/-!'): inside = True; continue
            if inside:
                if '-/' in l: break
                doc.append(l)
        if not doc: continue
        # every declaration name in the file, by leaf
        leaves = set()
        for l in lines:
            m = DECL.match(l)
            if m: leaves.add(m.group(1).split('.')[-1])
        anon_instance = any(re.match(r'\s*(?:scoped\s+|local\s+)?instance\s*(?:\([^)]*\)\s*)?:',
                                     l) for l in lines)
        for l in doc:
            b = BULLET.match(l)
            if not b: continue
            name = b.group(1).rstrip('.')
            leaf = name.split('.')[-1]
            # Lean auto-names an anonymous `instance : Foo …` as `instFoo`; such a name cannot be
            # matched against the source text, so a file containing any anonymous instance cannot
            # be checked for `inst*` bullets.  Skip rather than report a name we cannot verify.
            if re.match(r'inst[A-Z]', leaf) and anon_instance: continue
            if not leaf or leaf[0].isupper() and '.' not in name:   # a type/structure reference
                pass
            advertised += 1
            if leaf in leaves: resolved += 1
            else: hits.append((p, name, leaf))

# NARROWING (r189): a hub module documenting a subsystem is a legitimate pattern -- most
# unresolved names live in a file this one IMPORTS, so the reader can reach them.  The #5579
# defect was sharper: `Gamma/Basic.lean` advertised a declaration in *downstream* `Poisson.lean`,
# "unavailable to users importing Basic".  Flag only names that are NOT REACHABLE from here.
import collections
mod_of = {}
declares = collections.defaultdict(set)
for dp, _, fns in os.walk(root):
    for fn in fns:
        if not fn.endswith('.lean'): continue
        p = os.path.join(dp, fn)
        mod = 'TauCeti.' + os.path.relpath(p, root)[:-5].replace(os.sep, '.')
        mod_of[p] = mod
        try: ls = open(p, encoding='utf-8').read().split('\n')
        except Exception: continue
        for l in ls:
            m = DECL.match(l)
            if m: declares[m.group(1).split('.')[-1]].add(mod)
IMP = re.compile(r'^\s*(?:public\s+|private\s+|meta\s+)*import\s+([A-Za-z0-9_.]+)', re.M)
imports = {}
for p, mod in mod_of.items():
    try: imports[mod] = set(IMP.findall(open(p, encoding='utf-8').read()))
    except Exception: imports[mod] = set()
def closure(mod):
    seen, q = {mod}, collections.deque([mod])
    while q:
        m0 = q.popleft()
        for d in imports.get(m0, ()):
            if d not in seen: seen.add(d); q.append(d)
    return seen
unreachable = []
for p, name, leaf in hits:
    # a one- or two-letter bullet is prose (`* `h` is the height ...`), not a declaration
    # reference; it collides with unrelated short definitions elsewhere in the tree.
    if len(leaf) < 4 and '_' not in leaf and '.' not in name: continue
    homes = declares.get(leaf)
    if not homes: continue                      # declared nowhere: a stale name, different defect
    if not (homes & closure(mod_of[p])):
        unreachable.append((p, name, leaf, sorted(homes)[0]))
print(f"# NARROWED: {len(unreachable)} of {len(hits)} advertise a name that is NOT reachable "
      f"from the advertising file (the #5579 defect)")
for p, name, leaf, home in unreachable[:20]:
    print(f"  {p}")
    print(f"      advertises `{name}` -> declared in {home}, which this file does not import")
print()
print(f"# FIRING CONTROL: {advertised} declaration names advertised in module docs; "
      f"{resolved} resolve inside their own file ({100*resolved//max(advertised,1)}%)")
print(f"# {len(hits)} advertised names NOT declared in the advertising file")
from collections import Counter
byfile = Counter(h[0] for h in hits)
for p, cnt in byfile.most_common(20):
    names = [h[1] for h in hits if h[0] == p]
    print(f"  {cnt:2d}  {p}")
    print(f"      {', '.join(names[:4])}{' …' if len(names) > 4 else ''}")
