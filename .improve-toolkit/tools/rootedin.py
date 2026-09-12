#!/usr/bin/env python3
"""rootedin.py <file.lean>... -- a bare reference to a declaration rooted OUT of a wrapper that stays.

THE RED BUILD OF r609.  `#6148` kept `namespace IsCompactOperator` (because six unflagged private
helpers still lived in it) while rooting the flagged declarations out to `_root_.IsCompactOperator.x`.
I asserted, citing r389, that a rooted sibling stays reachable by its short name inside the surviving
wrapper.  **It does not**, and CI said so:

    Eigenspace.lean:135:53: Unknown identifier `finiteDimensional_eigenspace`

r389's rule is about `namespace Foo` **at root**.  Here the wrapper opens `TauCeti.IsCompactOperator`
while rooting moves the declaration to `IsCompactOperator` -- a different namespace that the wrapper
does not open.  Lean tries `TauCeti.IsCompactOperator.x`, then `TauCeti.x`, then root `x`; it never
tries `IsCompactOperator.x`.

WHY NOTHING ELSE CATCHES IT.  `siblingscan` and `xsibling` both model breakage caused by a wrapper
being REMOVED, and here the wrapper survives -- that is the whole point of the shape.  `deadpath` only
sees qualified names, and the broken reference is bare.  Until this check the only detector was a
13-minute build.

THE RULE.  Inside a `namespace NS` block that is still present, a declaration written
`_root_.P.x` is reachable by bare `x` only when `P` is empty or `P.x` is one of the names the
enclosing stack itself generates.  Rooting puts `P` at a Mathlib namespace, so a bare `x` referring
to it does not resolve and must be qualified.
"""
import sys, os, re, importlib.util
_spec = importlib.util.spec_from_file_location(
    "vns", os.path.join(os.path.dirname(os.path.abspath(__file__)), "vacuousns.py"))
vns = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(vns)

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?"
                  r"(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+|"
                  r"partial\s+|unsafe\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
                  r"_root_\.([\w.']+)")
OPEN = re.compile(r'^(?:@\[[^\]]*\]\s*)?'
                  r'(?:public\s+|private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+|'
                  r'scoped\s+)*'
                  r'(namespace|section)(?:\s+(\S+))?\s*$')
END = re.compile(r'^end(?:\s+(\S+))?\s*$')

def blocks(lines):
    """[(stack_at_open, open_idx, close_idx)] for every `namespace` block, 0-based, end-exclusive."""
    stack, opened, out, depth = [], [], [], 0
    for i, L in enumerate(lines):
        o, c = L.count('/-'), L.count('-/')
        was = depth; depth = max(0, depth + o - c)
        if was or o > c:
            continue
        m = OPEN.match(L)
        if m:
            if m.group(1) == 'namespace' and m.group(2):
                parts = m.group(2).split('.')
                opened.append((list(stack), i, len(parts)))
                stack.extend(parts)
            else:
                opened.append(None); 
            continue
        m = END.match(L)
        if m and opened:
            e = opened.pop()
            if e is not None:
                st, oi, n = e
                del stack[len(stack) - n:]
                out.append((st + (m.group(1).split('.') if False else []), oi, i, n, list(stack)))
    return out

def main():
    targets = [os.path.normpath(t) for t in sys.argv[1:]]
    missing = [t for t in targets if not os.path.isfile(t)]
    if missing:
        print(f"# UNRUN: {len(missing)} target(s) are not files, e.g. {missing[0][:100]!r}.",
              file=sys.stderr)
        return 2
    rows, nblocks, nrooted = [], 0, 0
    for t in targets:
        lines = open(t, encoding='utf-8').read().split('\n')
        # rebuild the namespace stack per line
        stack, depth, per_line = [], 0, []
        for L in lines:
            o, c = L.count('/-'), L.count('-/')
            was = depth; depth = max(0, depth + o - c)
            if not (was or o > c):
                m = OPEN.match(L)
                if m and m.group(1) == 'namespace' and m.group(2):
                    stack.extend(m.group(2).split('.'))
                    per_line.append(list(stack)); continue
                m2 = END.match(L)
                if m2 and m2.group(1):
                    for part in reversed(m2.group(1).split('.')):
                        if stack and stack[-1] == part:
                            stack.pop()
            per_line.append(list(stack))
        # declarations rooted OUT of a surviving stack
        rooted = []
        depth = 0
        for i, L in enumerate(lines):
            o, c = L.count('/-'), L.count('-/')
            was = depth; depth = max(0, depth + o - c)
            if was or o > c:
                continue
            m = DECL.match(L)
            if not m:
                continue
            nrooted += 1
            full = m.group(1)
            st = per_line[i]
            if not st:
                continue                              # nothing encloses it: bare names are fine
            nblocks += 1
            # EVERY PROPER SUFFIX IS A WAY THE REFERENCE CAN BE WRITTEN, not only the last
            # component (r643).  #6406 rooted `SheafOfModules.LocalGeneratorsData.IsInvertible` and
            # referred to it as `LocalGeneratorsData.IsInvertible` inside
            # `namespace TauCeti.SheafOfModules`.  This check looked only at `IsInvertible`, found
            # it shadowed by the class of that name, and reported `ok` on a tree whose build failed
            # with `Unknown identifier` -- a check reporting ok on the defect it exists to catch.
            # Lean tries `TauCeti.SheafOfModules.<s>`, `TauCeti.<s>`, then root `<s>`; it never
            # tries `SheafOfModules.<s>`, so a suffix is stranded unless one of those candidates IS
            # the rooted name.  The full name is excluded because it always resolves at root: the
            # stack-prefixed form is precisely what the rooting removed.
            for short in sorted(vns.proper_suffixes(full), key=len, reverse=True):
                cands = {'.'.join(st[:k] + [short]) for k in range(len(st) + 1)}
                if full in cands:
                    continue                          # the stack itself generates it: reachable
                rooted.append((i, full, short, '.'.join(st)))
        # A SAME-NAMED DECLARATION IN THE ENCLOSING STACK SHADOWS THE ROOTED ONE (r625).
        # `Invertible/Basic.lean` declares the class `TauCeti.SheafOfModules.IsInvertible` AND roots
        # `SheafOfModules.LocalGeneratorsData.IsInvertible`; a bare `IsInvertible` inside
        # `namespace SheafOfModules` resolves to the first and is perfectly fine. Reporting it is the
        # r563 mistake -- assuming a short name must mean the declaration this PR moved.
        ANYNAME = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?"
                             r"(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|"
                             r"scoped\s+|partial\s+|unsafe\s+)*"
                             r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
                             r"(_root_\.)?([\w.']+)")
        declared, depth = set(), 0
        for i, L in enumerate(lines):
            o, c = L.count('/-'), L.count('-/')
            was = depth; depth = max(0, depth + o - c)
            if was or o > c:
                continue
            m = ANYNAME.match(L)
            if not m:
                continue
            if m.group(1):
                declared.add(m.group(2))
            else:
                declared.add('.'.join(per_line[i] + [m.group(2)]))
        rooted = [r for r in rooted
                  if '.'.join(r[3].split('.') + [r[2]]) not in declared]
        if not rooted:
            continue
        # A BARE occurrence of `short` elsewhere in the file. Two exclusions, both learned from
        # false positives on a branch whose build is fine (r625):
        #   * `--` line comments -- masking only `/- -/` left `-- \`ofIso\` leaves the index type`
        #     looking like a reference;
        #   * ANY declaration header -- `class IsInvertible` and `theorem IsInvertible.of_iso` are
        #     declarations that share a name, not references to the rooted one.
        ANYDECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?"
                             r"(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|"
                             r"scoped\s+|partial\s+|unsafe\s+)*"
                             r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
                             r"((?:_root_\.)?[\w.']+)")
        depth = 0
        for i, L in enumerate(lines):
            o, c = L.count('/-'), L.count('-/')
            was = depth; depth = max(0, depth + o - c)
            if was or o > c:
                continue
            code = re.sub(r'--.*$', '', L)            # strip a line comment
            # MASK ATTRIBUTE BRACKETS (r550, re-encountered r626). `@[ext]` on the line above
            # `theorem _root_.RootPairing.weylGroup.ext` is an ATTRIBUTE, not a reference to the
            # declaration below it -- auditing merged #6056 reported exactly that. r550 shipped a
            # tool that rewrote `@[ext]` into `@[RootPairing.weylGroup.ext]` for the same reason.
            code = re.sub(r'@\[[^\]]*\]', ' ', code)
            # MASK THE DECLARED NAME, DO NOT SKIP THE LINE (r563/r625). A reference frequently sits
            # on the header itself (`theorem uses : True := moved`), so dropping the whole line loses
            # real breakages; dropping only the name being DECLARED keeps them while ignoring
            # `class IsInvertible` and `theorem IsInvertible.of_iso`, which declare rather than refer.
            md = ANYDECL.match(code)
            if md:
                code = code[:md.start(1)] + ' ' * (md.end(1) - md.start(1)) + code[md.end(1):]
            for di, full, short, st in rooted:
                if i == di:
                    continue
                if not re.search(r'(?<![\w.\'])' + re.escape(short) + r'(?![\w\'])', code):
                    continue
                # SHADOWING IS JUDGED FROM THE REFERENCE'S OWN STACK, not the rooted declaration's
                # (r648).  The r625 filter compared `<rooted decl's stack>.<short>` against the declared
                # set, which only sees a shadow sitting in the SAME block.  #6413 rooted
                # `FDRep.frobeniusSchurIndicator` while `TauCeti.Representation.frobeniusSchurIndicator`
                # is declared in the same file; nine bare uses inside `namespace Representation` resolve
                # to that one perfectly well, and were reported as breakages.  A reference resolves to the
                # FIRST candidate that exists, so walk the reference's stack outwards and stop there.
                ref_st = per_line[i]
                hit = next((c for k in range(len(ref_st), -1, -1)
                            for c in ['.'.join(ref_st[:k] + [short])] if c in declared), None)
                if hit is not None and hit != full:
                    continue
                rows.append((t, i + 1, short, full, st))
    seen = set()
    for t, ln, short, full, st in rows:
        k = (t, ln, short)
        if k in seen:
            continue
        seen.add(k)
        # `bare` when the reference is a single component, `partially qualified` when it carries
        # some of the namespace but not enough to resolve (r643).  Both are unreachable; saying
        # which one keeps the message honest without losing the original wording.
        kind = 'bare' if '.' not in short else 'partially qualified'
        print(f"UNREACHABLE  {t}:{ln}  {kind} `{short}` cannot reach `{full}` from inside "
              f"`{st}` -- qualify it as `{full}`")
    print(f"# FIRING CONTROL: {nrooted} `_root_.`-anchored declaration(s), {nblocks} of them inside a "
          f"surviving namespace; {len(seen)} bare reference(s) that cannot resolve. This is the r609 "
          f"red build, which `siblingscan`/`xsibling` cannot see because they model a wrapper being "
          f"REMOVED and here it SURVIVES.", file=sys.stderr)
    return 1 if seen else 0

if __name__ == '__main__':
    sys.exit(main())
