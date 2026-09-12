#!/usr/bin/env python3
"""rootns.py <namespace> <file.lean>... -- move a namespace's declarations to Mathlib's root.

The extraction step that rounds 550-552 kept getting wrong by hand.  It does exactly two things:

  1. rewrite each declaration header in the namespace to `_root_.<NS>.<name>` -- BOTH shapes, the
     bare `theorem foo` inside a `namespace <NS>` block and the dotted `theorem <NS>.foo` written
     directly inside `namespace TauCeti` (r547 shipped a script that matched only the first and
     rooted 37 of 67 while reporting success);
  2. retire the wrapper -- `namespace <NS>` **or a compound `namespace A.<NS>`**, since
     `namespace TauCeti.AlgHom` opens both levels on one line and is just as much the wrapper --
     becoming `section` when the block carries a `variable`
     line of its own and is DELETED outright when it does not, and the **stack-matched** `end`
     is changed or deleted with it.

COMPOUND WRAPPERS COUNT (r561).  The first cut matched only a scope named exactly `<NS>`, so three
of `AlgHom`'s eleven files -- every one of them opening `namespace TauCeti.AlgHom` -- were skipped
in silence: **71 of 83 rooted, 8 of 11 files touched**.  That is r487's compound-namespace miss
(`^namespace A.B`) reappearing in a new tool, and the only reason it was caught before a branch was
built is the count this function prints next to the number you expected.  Retiring the compound
scope takes the `TauCeti` half with it, which is correct precisely because every declaration inside
has just been rooted out of it.

MATCHING THE `end` BY STACK IS THE WHOLE POINT (r551, a red build).  The hand-rolled pass rewrote
"the first `end` after the wrapper", which is wrong the moment anything nests: `Adjoint.lean` opens
`namespace ContinuousLinearMap`, then `section Restriction` inside it, so the first `end` belongs to
the section.  Lean answers `Missing name after 'end'` plus five follow-on errors that look like real
findings and are not.

PROSE IS NOT CODE (r561).  `scopes()` tracked `/- ... -/` depth from the start; the rewrite loop
below did not, so a docstring line that merely BEGINS with a declaration keyword was rewritten:

    structure on its functor of points evaluated at `A`. -/
 -> structure _root_.AlgHom.on its functor of points evaluated at `A`. -/

It cost one bogus name and showed up only because the rooted count came out 84 against an
enumeration of 83. r497 learned this once, `wrap100` learned it again in r555; a tool that rewrites
lines has to know which of them are prose.

ANYTHING IT CANNOT ACCOUNT FOR IS REPORTED, NEVER SKIPPED.  An anonymous `instance : C X` inside the
block has no name to root, so retiring the wrapper would silently move it to `TauCeti` -- a
different declaration.  Those are listed and the file is left alone.

Run `settle.sh` afterwards: rooting breaks short references, and that is what fixes them.

THE NEW NAME IS THE OLD FULL NAME MINUS `TauCeti`, NOT `NS` PLUS THE TAIL (r600).  Both rewrite paths
used to build the rooted name from the namespace ARGUMENT, which silently drops any wrapper sitting
between `TauCeti` and the target.  `Invertible/Basic.lean` opens `namespace TauCeti` then
`namespace SheafOfModules` and writes `structure LocalGeneratorsData.IsInvertible` dotted, so the full
name is `TauCeti.SheafOfModules.LocalGeneratorsData.IsInvertible`.  `rootns LocalGeneratorsData` made
that `_root_.LocalGeneratorsData.IsInvertible` -- **dropping `SheafOfModules`**, a namespace Mathlib
does not have -- and reported `3 declaration(s) rooted`.  Only the gate caught it, three steps later,
via `decldiff`, `stalequal` and `lint-dot-notation: NEW violations` (r598).

So the rooted name is now computed from the declaration's own position: the enclosing namespace path
with a leading `TauCeti` stripped, then the name as written.  A compound argument
(`SheafOfModules.LocalGeneratorsData`, which is what `nscand` and `mathlibns` both print) selects the
same declarations as its tail.  And the FIRING CONTROL prints every resulting full name, because the
failure mode here is rooting to the wrong place while reporting success (r184).
"""
import sys, os, re

DECL = re.compile(r"^(\s*)((?:@\[[^\]]*\]\s*)?"
                  r"(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+|"
                  r"partial\s+|unsafe\s+)*)"
                  r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
                  r"([^\W\d][\w.'!?]*)")
ANON = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?"
                  r"(?:public\s+|private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
                  r"instance\s*[:(\[]")
OPEN = re.compile(r'^(?:@\[[^\]]*\]\s*)?'
                  r'(?:public\s+|private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+|'
                  r'scoped\s+)*'
                  r'(namespace|section)(?:\s+(\S+))?\s*$')
END = re.compile(r'^end(?:\s+(\S+))?\s*$')
VAR = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?variable\b')

def scopes(lines):
    """[(kind, name, open_line, close_line, depth)] -- close_line None if never closed."""
    stack, out, depth = [], [], 0
    for i, L in enumerate(lines, 1):
        o, c = L.count('/-'), L.count('-/')
        was = depth; depth = max(0, depth + o - c)
        if was or o > c:
            continue
        m = OPEN.match(L)
        if m:
            stack.append([m.group(1), m.group(2), i, None, len(stack)]); continue
        m = END.match(L)
        if m and stack:
            e = stack.pop(); e[3] = i; out.append(tuple(e))
    for e in stack:
        out.append(tuple(e))
    return out

def ns_path_at(sc, lineno):
    """Enclosing namespace components at 1-based `lineno`, outermost first."""
    parts = []
    for kind, nm, a, b, _d in sorted(sc, key=lambda e: e[2]):
        if kind != 'namespace' or not nm:
            continue
        if a <= lineno and (b is None or lineno < b):
            parts.extend(nm.split('.'))
    return parts

def rooted_name(sc, lineno, name):
    """The full name a rooting should produce: enclosing path minus a leading `TauCeti`, then `name`."""
    encl = ns_path_at(sc, lineno)
    if encl and encl[0] == 'TauCeti':
        encl = encl[1:]
    return '.'.join(encl + [name]) if encl else name

def process(path, NS, report):
    lines = open(path, encoding='utf-8').read().split('\n')
    sc = scopes(lines)
    # ROOTING A NAMESPACE TAKES ITS SUBTREE (r601).  `SheafOfModules.LocalGeneratorsData` owns
    # `…LocalGeneratorsData.IsInvertible` too, and `LocalTriviality.lean` opens exactly that as a
    # block.  Matching only the namespace itself left that child's API nested while its parent went
    # to the root -- the r515 split, produced by the very tool meant to avoid it.
    TAIL = NS.split('.')[-1]
    def _is_target(nm):
        for cand in (NS, TAIL):
            if nm == cand or nm.endswith('.' + cand):
                return True
            if nm.startswith(cand + '.') or ('.' + cand + '.') in nm:
                return True                      # a CHILD namespace of the target
        return False
    blocks = [s for s in sc if s[0] == 'namespace' and s[1] and _is_target(s[1])]
    if not blocks:
        blocks = []
    # anonymous instances inside any block would lose their home
    bad = []
    for _k, _n, a, b, _d in blocks:
        if b is None:
            bad.append(f"{path}:{a}: `namespace {NS}` is never closed"); continue
        for i in range(a, b - 1):
            if ANON.match(lines[i]) and not DECL.match(lines[i]):
                bad.append(f"{path}:{i+1}: anonymous instance inside the block")
    if bad:
        report.extend(bad)
        return 0, 0, 0, []

    inblock = set()
    for _k, _n, a, b, _d in blocks:
        inblock |= set(range(a, b - 1))          # 0-based line indices strictly inside

    rooted, depth, produced = 0, 0, []
    for i, L in enumerate(lines):
        o, c = L.count('/-'), L.count('-/')
        was = depth
        depth = max(0, depth + o - c)
        if was or o:                             # inside or opening a comment: prose, not a decl
            continue
        m = DECL.match(L)
        if not m:
            continue
        ind, mods, kw, name = m.groups()
        if name.startswith('_root_.'):
            continue
        if i in inblock or name.startswith(NS + '.') or name.startswith(TAIL + '.'):
            full = rooted_name(sc, i + 1, name)
        else:
            continue
        new = f"_root_.{full}"
        lines[i] = L[:m.start(4)] + new + L[m.end(4):]
        produced.append(full)
        rooted += 1

    # retire the wrappers, bottom-up so line numbers stay valid
    to_sec = to_del = 0
    for _k, _n, a, b, _d in sorted(blocks, key=lambda s: -s[2]):
        own_var = any(VAR.match(lines[i]) for i in range(a, b - 1))
        if own_var:
            lines[a - 1] = 'section'
            lines[b - 1] = 'end'
            to_sec += 1
        else:
            del lines[b - 1]
            del lines[a - 1]
            to_del += 1
    open(path, 'w', encoding='utf-8').write('\n'.join(lines))
    return rooted, to_sec, to_del, produced

def main():
    NS, files = sys.argv[1], sys.argv[2:]
    report, R, S, D, touched, made = [], 0, 0, 0, 0, []
    for f in files:
        if not os.path.exists(f):
            print(f"# UNRUN: {f} does not exist.", file=sys.stderr); return 2
        r, s, d, prod = process(f, NS, report)
        R += r; S += s; D += d; touched += bool(r or s or d); made.extend(prod)
    for b in report:
        print("SKIPPED  " + b)
    # THE RESULTING NAMES, NOT JUST THE COUNT (r600). Rooting to the WRONG namespace is
    # success-shaped: it edits declarations and returns a nonzero count. Only the full names
    # show where they landed, and a name whose head is not what `mathlibns` blessed is the bug.
    for n in sorted(set(made)):
        print(f"ROOTED   _root_.{n}")
    heads = sorted({n.rsplit('.', 1)[0] for n in made})
    print(f"# FIRING CONTROL: {R} declaration(s) rooted into `{NS}` across {touched} file(s), "
          f"landing in {len(heads)} namespace(s): {', '.join(heads) if heads else '(none)'} -- "
          f"CHECK THAT AGAINST `mathlibns.py`, since rooting into a namespace Mathlib does not have "
          f"is what r598 did while reporting success; "
          f"{S} wrapper(s) became `section` (they carry a `variable`), {D} deleted outright; "
          f"{len(report)} file(s) LEFT ALONE and listed above. Compare {R} against the count you "
          f"expect -- r547 shipped a script that rooted 37 of 67 and reported success. Now run "
          f"`settle.sh`: rooting breaks short references by construction.", file=sys.stderr)
    return 1 if report else 0

if __name__ == '__main__':
    sys.exit(main())
