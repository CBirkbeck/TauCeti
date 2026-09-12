#!/usr/bin/env python3
"""importnarrow.py <root> -- narrow redundantimport rows to DEFENSIBLE drops.

Reads `redundantimport.py` rows (TSV: file, import-stmt, covered-by) on stdin and
keeps only those meeting all four r218/r222 criteria:

  1. the covered module registers no instances/notation,
  2. NONE of its declaration names appears in the importing file,
  3. the file's own prose does not name the module,
  4. the file has declarations of its own.

Why the criteria exist.  Dropping a *redundant* import is build-safe by construction --
the cover still provides the module, so even a used name resolves.  These criteria are
not about safety, they are about being UNARGUABLE: r218's eight shipped rows were files
that never mentioned the module at all, which is what made "drop it" impossible to
contest.  A file that visibly leans on the module can keep the direct import as a
statement of intent, and a reviewer is right to say so.

THE USE TEST MUST COUNT A PRECEDING DOT (r355).  Lean writes most uses of a namespaced
declaration dotted -- `W.comap φ`, `Graphon.comap_apply` -- so a lookbehind that excludes
`.` sees a heavily-used module as unreferenced.  That defect promoted 29 rows to
"findings" in one round, `AEEqFun.lean <- Graphon.Pullback` among them, a file that uses
`comap` twice.  It is the same dot-lookbehind bug that cost r295 and r296.

So the firing control prints BOTH counts.  If the dot-excluding number ever drifts above
the real one again, it is visible in the output instead of inflating a bank.
"""
import re, sys, os

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*'
                  r'(?:theorem|lemma|def|abbrev|instance|structure|class)\s+'
                  r'([^\W\d][\w.\']*)', re.M)
DECLANY = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*'
                     r'(?:theorem|lemma|def|abbrev|instance|structure|class)\s', re.M)
REG = re.compile(r'^\s*(?:@\[[^\]]*instance|instance\b|notation\b|scoped notation|'
                 r'infixl|infixr|prefix|postfix|attribute \[)', re.M)

def strip_imports(src):
    return re.sub(r'^\s*(?:public )?import.*$', '', src, flags=re.M)

def used(name, body, count_dot):
    """Does `name`'s last component occur as an identifier in `body`?"""
    # `back` must apply to BOTH probes.  Leaving the full-name probe dot-blind in naive
    # mode makes the comparison lie: it silently repairs the very bug it is measuring, and
    # the control then passes without exercising anything.
    back = r'(?<!\w)' if count_dot else r'(?<![\w.])'
    tail = re.escape(name.split('.')[-1])
    if re.search(back + tail + r'(?!\w)', body):
        return True
    return bool(re.search(back + re.escape(name) + r'(?!\w)', body))

def main():
    root = sys.argv[1]
    rows, cache = [], {}
    def read(p):
        if p not in cache:
            try: cache[p] = open(p, encoding='utf-8').read()
            except Exception: cache[p] = None
        return cache[p]
    scanned = unresolved = 0
    keep, naive_only = [], []
    for line in sys.stdin:
        parts = line.rstrip('\n').split('\t')
        if len(parts) < 2 or not parts[0].endswith('.lean'):
            continue
        f, mod = parts[0], parts[1].split()[-1]
        msrc = read(os.path.join(root, mod.replace('.', os.sep) + '.lean'))
        src = read(os.path.join(root, f))
        if msrc is None or src is None:
            unresolved += 1
            continue
        scanned += 1
        body = strip_imports(src)
        decls = set(DECL.findall(msrc))
        if REG.search(msrc) or not decls or not DECLANY.search(body):
            continue
        if mod.split('.')[-1] in body:            # prose names the module
            continue
        hit_real = [d for d in decls if used(d, body, True)]
        hit_naive = [d for d in decls if used(d, body, False)]
        if not hit_real:
            keep.append((f, mod, len(decls)))
        elif not hit_naive:
            naive_only.append((f, mod, sorted(hit_real)[:3]))
    for f, mod, n in keep:
        print(f"{f}\tdrop {mod}\t(module declares {n}, registers 0, unreferenced, unnamed)")
    print(f"# FIRING CONTROL: {scanned} rows scanned, {unresolved} module files unresolved; "
          f"{len(keep)} defensible. A dot-EXCLUDING use test would have reported "
          f"{len(keep) + len(naive_only)} -- {len(naive_only)} of those are files that use the "
          f"module only through dotted names (the r355 defect).", file=sys.stderr)
    for f, mod, ex in naive_only[:5]:
        print(f"#   dot-only use: {f} <- {mod} via {ex}", file=sys.stderr)

if __name__ == "__main__":
    main()
