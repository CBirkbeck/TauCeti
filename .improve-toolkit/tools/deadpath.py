#!/usr/bin/env python3
"""deadpath.py <root> <mathlib-root> <file.lean>... -- rooted paths this PR writes that don't exist.

THE r552 RED BUILD, #6065.  Two shapes, both invisible to every existing screen:

  1. OVER-QUALIFICATION.  r549 fixed three load-bearing names "by hand" and qualified them with the
     WRAPPER's name instead of the declaration's own: `WeierstrassCurve.conj` for a lemma actually
     called `WeierstrassCurve.Affine.CoordinateRing.conj`.  `xsibling` cannot see this -- it hunts
     BARE references, and its search refuses a name preceded by a dot, so an over-qualified name is
     outside its universe by construction.  `stalequal` cannot see it either: that tool tracks dead
     `TauCeti.` paths, and these are dead `WeierstrassCurve.` paths.  CI: `Unknown constant`.

  2. AN `open` OF THE NAMESPACE THE PR JUST EMPTIED.  Three files still said
     `open TauCeti.WeierstrassCurve` after every declaration had left it: `unknown namespace`.
          A namespace path is not a declaration name, so `stalequal`'s dead-path set never held it --
     and, decisively, **none of those three files is in the PR's diff**.  Emptying a namespace
     breaks files the PR never touched, so this half of the screen walks the WHOLE TREE, not the
     changed files.  That is `xsibling`'s cross-file lesson one level up: from references to
     namespaces.

Both are the same question -- **does the qualified name this PR writes actually exist?** -- asked
of the namespaces the PR roots into.  Existence means: declared `_root_.` somewhere in the tree
after the change, or declared in Mathlib, or a namespace PREFIX of such a name (`CoordinateRing`
alone is a namespace, not a declaration, and is written all the time).

The `Unknown constant` errors came with `unsolved goals`, `Type mismatch`, `declaration uses
sorry` and `This simp argument is unused` -- twenty-five errors from three real causes.  Only the
first kind is a finding; the rest are its wake.
"""
import sys, os, re, subprocess, importlib.util
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
def _load(n):
    spec = importlib.util.spec_from_file_location(n, os.path.join(HERE, n + ".py"))
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
nss = _load("nsslice")
mo = _load("movedopens")

TOKEN = re.compile(r"(?<![\w.])([^\W\d][\w']*(?:\.[^\W\d][\w'!?]*)+)")

def code_lines(lines):
    depth = 0
    for i, raw in enumerate(lines, 1):
        o, c = raw.count('/-'), raw.count('-/')
        was = depth; depth = max(0, depth + o - c)
        if was or o:
            continue
        blank = lambda m: ' ' * len(m.group(0))
        code = re.sub(r'`[^`]*`', blank, raw)
        code = re.sub(r'"(?:[^"\\]|\\.)*"', blank, code)
        code = re.sub(r'--.*$', blank, code)
        yield i, code

def main():
    argv = sys.argv[1:]
    base = None
    if '--base' in argv:
        i = argv.index('--base'); base = argv[i + 1]; del argv[i:i + 2]
    root, mlroot, targets = argv[0], argv[1], [os.path.normpath(t) for t in argv[2:]]
    missing = [t for t in targets if not os.path.exists(t)]
    if missing:
        print(f"# UNRUN: {len(missing)} target(s) do not exist, e.g. {missing[0][:120]!r}.",
              file=sys.stderr)
        return 2

    rooted_full, tauceti_ns, nfiles = set(), defaultdict(int), 0
    for dp, _, fs in os.walk(root):
        for f in fs:
            if not f.endswith('.lean'): continue
            nfiles += 1
            for ns, short, is_root in nss.walk(os.path.normpath(os.path.join(dp, f))):
                full = f"{ns}.{short}" if ns else short
                # EVERY declaration counts as a known name, not just the `_root_.` ones.
                # A file may open a TOP-LEVEL `namespace WeierstrassCurve` without `_root_.`, and
                # `Coprimality.lean` does exactly that -- so `WeierstrassCurve.ΨSq_ne_zero_of_Δ_ne_zero`
                # is a perfectly good root-level name.  Counting only rooted declarations reported it
                # as dead: a false positive on a line the PR never touched (r552).
                rooted_full.add(full)
                if not is_root and ns.startswith('TauCeti'):
                    tauceti_ns[ns] += 1

    where, nml = mo.index(mlroot)
    if not nml:
        print(f"# UNRUN: indexed 0 Mathlib files under {mlroot!r} -- every name would look dead.",
              file=sys.stderr)
        return 2
    known = set(rooted_full)
    for short, spaces in where.items():
        for s in spaces:
            known.add(f"{s}.{short}" if s else short)
    prefixes = set()
    for n in known:
        p = n.split('.')
        for i in range(1, len(p)):
            prefixes.add('.'.join(p[:i]))

    # the namespaces THESE files root into -- the only ones this screen judges
    roots_here = set()
    for t in targets:
        for ns, _s, is_root in nss.walk(t):
            if is_root and ns:
                roots_here.add(ns.split('.')[0])
    if not roots_here:
        print("# FIRING CONTROL: no `_root_.` declaration in the given file(s); nothing to check.",
              file=sys.stderr)
        return 0

    def ok(tok):
        p = tok.split('.')
        for i in range(len(p), 1, -1):            # any dotted prefix that IS a declaration
            if '.'.join(p[:i]) in known:
                return True
        return tok in prefixes                    # or the token is itself a namespace

    rows, emptied, nseen = [], [], 0
    for t in targets:
        for ln, code in code_lines(open(t, encoding='utf-8').read().split('\n')):
            for m in TOKEN.finditer(code):
                tok = m.group(1)
                head = tok.split('.')[0]
                if head not in roots_here:
                    continue
                nseen += 1
                if not ok(tok):
                    rows.append((t, ln, tok))
    # WHOLE-TREE half: a namespace this PR emptied, still named anywhere.
    gone = {X for X in roots_here
            if not any(k == 'TauCeti.' + X or k.startswith('TauCeti.' + X + '.')
                       for k in tauceti_ns)}
    if gone:
        for dp, _, fs in os.walk(root):
            for f in fs:
                if not f.endswith('.lean'): continue
                p = os.path.normpath(os.path.join(dp, f))
                try: src = open(p, encoding='utf-8').read()
                except Exception: continue
                if 'TauCeti.' not in src: continue
                # PROSE COUNTS HERE, unlike the DEAD PATH half above (r554).  A comment that
                # explains why an import is not `public` "because it would re-export
                # `TauCeti.WeierstrassCurve.Affine`" is not decoration: after the namespace is
                # emptied the sentence is false, and it gives the next reader wrong guidance about
                # namespaces and imports.  #6065 was blocked by the `documentation` rubric on
                # exactly two such comments.  `stalequal` already scans prose for dead DECLARATION
                # paths; a dead NAMESPACE path in prose fell between the two tools.
                for ln, raw in enumerate(src.split('\n'), 1):
                    for X in gone:
                        key = 'TauCeti.' + X
                        if key not in raw: continue
                        for m in re.finditer(re.escape(key) + r"(?![\w])", raw):
                            emptied.append((p, ln, key))

    seen, uniq = set(), []
    for r in rows:
        if r not in seen: seen.add(r); uniq.append(r)
    # SCOPE THE ROWS TO WHAT THIS PR WROTE (r594).  `prepush` says "every qualified name this PR
    # writes resolves", but the scan is absolute: a reference that was ALREADY dead in a file blames
    # whoever next opens that file.  A 250-file sample of green `main` carries 95 rows across 33
    # files (`Vandermonde.lean` 15, `EulerCharacteristic.lean` 14), so most of the tree is a
    # landmine.  This is r551/r592/r593 a fourth time.  With `--base <ref>` a row is dropped when its
    # token is already present in that file at the base -- the PR did not author the reference.  A
    # declaration the PR DELETED out from under a live reference is `stalequal`'s row, not this one.
    nprexist = 0
    if base:
        def base_text(t):
            g = subprocess.run(['git', 'show', f'{base}:{t}'], capture_output=True, text=True)
            return None if g.returncode else g.stdout
        cache = {}
        def already(t, tok):
            if t not in cache:
                cache[t] = base_text(t)
            txt = cache[t]
            return txt is not None and tok in txt
        keep = [r for r in uniq if not already(r[0], r[2])]
        nprexist += len(uniq) - len(keep)
        uniq = keep
        ek = [r for r in dict.fromkeys(emptied) if not already(r[0], r[2])]
        nprexist += len(dict.fromkeys(emptied)) - len(ek)
        emptied = ek
    for t, ln, tok in uniq:
        # A SUGGESTION MUST END WITH THE TOKEN'S TAIL (r556, a red build).  Matching on the LEAF
        # alone is a coin flip: `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr` has leaf
        # `mpr`, so leaf-matching offered `TypeVec.Arrow.mpr` -- and `deadfix` applied it.  The
        # good case has the whole tail in common (`WeierstrassCurve.conj` ->
        # `WeierstrassCurve.Affine.CoordinateRing.conj`); requiring that refuses the bad one and
        # keeps every fix r552 made.
        tail, head0 = tok.split('.', 1)[1] if '.' in tok else tok, tok.split('.')[0]
        cands = sorted((n for n in known if n.endswith('.' + tail)),
                       key=lambda n: (not n.startswith(head0 + '.'), len(n)))[:3]
        print(f"DEAD PATH   {t}:{ln}  `{tok}` is not a declaration"
              + (f" -- did you mean `{cands[0]}`?" if cands else ""))
    for t, ln, ns in dict.fromkeys(emptied):
        print(f"DEAD NS     {t}:{ln}  `{ns}` no longer holds any declaration -- "
              f"this PR emptied it")
    mode = (f"delta vs {base}; {nprexist} row(s) suppressed as already present at the base"
            if base else
            "ABSOLUTE scan -- pass --base so references main already had are not blamed here (r594)")
    print(f"# FIRING CONTROL: [{mode}] "
          f"{nfiles} tree files, {nml} Mathlib files, {len(known)} known full "
          f"names; roots into {', '.join(sorted(roots_here))}; {nseen} qualified reference(s) "
          f"checked, {len(uniq)} DEAD, {len(dict.fromkeys(emptied))} dead namespace path(s). "
          f"`xsibling` hunts BARE names and cannot see an over-qualified one; `stalequal` tracks "
          f"`TauCeti.` paths and cannot see a dead `WeierstrassCurve.` one (r552).",
          file=sys.stderr)
    return 1 if (uniq or emptied) else 0

if __name__ == '__main__':
    sys.exit(main())
