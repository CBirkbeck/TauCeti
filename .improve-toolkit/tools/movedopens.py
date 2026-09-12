#!/usr/bin/env python3
"""movedopens.py <mathlib-root> <source.lean> <first-line> <last-line>

Which of a moved block's names resolve ONLY because of an `open` in the file it is leaving.

THE r498 DEFECT, and it cost three CI cycles and two wrong diagnoses.  #5959 moved two lemmas out
of `TauCeti/Algebra/CentralSimple/TensorProduct.lean`.  Their binder says `Basis ι K B`, and the
source file resolves that through its `open Module` -- in the pinned Mathlib the type is
`Module.Basis`.  The new file had no `open Module`, so `Basis` was AUTO-BOUND as an implicit and
the build said

    Function expected at Basis / but this term has type ?m.5

`?m.5` is the tell: a metavariable type means auto-bound, i.e. the name never resolved.  I read
that as a missing import and spent two rounds on import chains; the import was fine both times.

`lint-dot-notation`'s own message says it outright -- *"Watch for `open` and `variable` commands
that must move with it."*  This makes that check mechanical instead of remembered.

METHOD.  Index every Mathlib declaration by (short name -> set of enclosing namespaces), then for
each capitalised identifier in the block report where Mathlib puts it.  A name Mathlib declares
ONLY inside a namespace the source file `open`s is one the destination must qualify or re-open.
Root-declared names are safe; names found in both are reported so the caller can look.

The index tracks the `namespace` stack, accepts NESTED and COMPOUND (`namespace A.B`) forms, the
`public`/`private`/`protected`/`noncomputable` modifier run, and Unicode identifiers -- every one
of those has silently returned zero at least once (r458, r481, r487, r490, r494).
"""
import sys, os, re
from collections import defaultdict

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?'
                  r'(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+|'
                  r'partial\s+|unsafe\s+|local\s+)*'
                  r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+'
                  r"(_root_\.)?([^\W\d][\w.'!?]*)")
NS = re.compile(r'^namespace\s+(\S+)\s*$')
END = re.compile(r'^end\s+(\S+)\s*$')
OPEN = re.compile(r'^open\s+(?:scoped\s+)?(.+?)(?:\s+in)?\s*$')
IDENT = re.compile(r"(?<![\w.'])([A-Z][\w']*)")

def index(root):
    """short name -> set of namespaces it is declared in ('' means root)."""
    where = defaultdict(set)
    nfiles = 0
    for dp, _, fs in os.walk(root):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            nfiles += 1
            stack, incomment = [], 0
            try:
                lines = open(os.path.join(dp, f), encoding='utf-8').read().split('\n')
            except Exception:
                continue
            for L in lines:
                o, c = L.count('/-'), L.count('-/')
                was = incomment
                incomment = max(0, incomment + o - c)
                if was or o > c:
                    continue
                m = NS.match(L)
                if m:
                    stack.extend(m.group(1).split('.'))
                    continue
                m = END.match(L)
                if m:
                    for part in reversed(m.group(1).split('.')):
                        if stack and stack[-1] == part:
                            stack.pop()
                    continue
                m = DECL.match(L)
                if m:
                    # `_root_.` ESCAPES THE NAMESPACE STACK (r556, a red build).  The prefix was
                    # matched and thrown away here, so every `_root_.`-declared name in Mathlib was
                    # filed under whatever namespace happened to enclose it:
                    # `theorem _root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`, declared
                    # inside `namespace IsSelfAdjoint`, was indexed as
                    # `IsSelfAdjoint.ContinuousLinearMap`.  `deadpath` then judged a perfectly good
                    # Mathlib name DEAD and `deadfix` replaced it.  `nsslice.walk` has always
                    # branched on this group; this one did not.
                    parts = m.group(2).split('.')
                    ns = '.'.join(parts[:-1]) if m.group(1) else '.'.join(stack + parts[:-1])
                    where[parts[-1]].add(ns)
    return where, nfiles

def main():
    mathlib, src, a, b = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    lines = open(src, encoding='utf-8').read().split('\n')
    opens = []
    for L in lines:
        m = OPEN.match(L)
        if m:
            opens.extend(w for w in m.group(1).split() if w[:1].isupper())
    block = '\n'.join(lines[a - 1:b])
    idents = sorted(set(IDENT.findall(block)))
    where, nfiles = index(mathlib)
    risky, safe, unknown = [], 0, 0
    for n in idents:
        ns = where.get(n)
        if not ns:
            unknown += 1
            continue
        if '' in ns:
            safe += 1
            continue
        hit = sorted(x for x in ns if x in opens)
        if hit:
            risky.append((n, hit[0]))
        else:
            unknown += 1
    for n, o in risky:
        print(f"NEEDS `open {o}`   {n}  ->  write `{o}.{n}` or re-open it in the destination")
    print(f"# FIRING CONTROL: {nfiles} Mathlib files indexed, {len(where)} distinct short names; "
          f"source opens {opens or '(none)'}; {len(idents)} capitalised identifiers in lines "
          f"{a}-{b}; {safe} are declared at Mathlib's ROOT and travel safely, {len(risky)} resolve "
          f"ONLY through one of those opens, {unknown} not attributable (local, TauCeti's own, or "
          f"a namespace the file does not open). A `?m.5` metavariable type in a build error means "
          f"AUTO-BOUND, i.e. the name never resolved -- look here before looking at imports.",
          file=sys.stderr)
    return 1 if risky else 0

if __name__ == '__main__':
    sys.exit(main())
