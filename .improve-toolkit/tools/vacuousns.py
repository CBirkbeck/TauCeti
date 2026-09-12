#!/usr/bin/env python3
"""vacuousns.py <root> -- `namespace` blocks that declare nothing into themselves.

The shape #5820 and #5838 removed: a `namespace X` ... `end X` block in which EVERY
declaration is written `_root_.Something.foo`, so the block contributes no name at all.
The wrapper only makes the file read as though it declared into `X`.

Why this is not `nsshadow`.  `nsshadow` fires only when the block's name is one of a fixed
list of well-known ROOT namespaces (`Matrix`, `Subgroup`, `Sym`, ...), because its question
is *"does this look like Mathlib's namespace?"*.  That caught #5820/#5838 by luck of the
name.  The defect here is independent of the name: a block called anything at all can wrap
only `_root_`-anchored declarations.  This screen asks the direct question instead.

Attribution is to the INNERMOST enclosing namespace: a declaration inside
`namespace A` / `namespace B` belongs to B, so wrapping blocks that legitimately contain
nested namespaces are not blamed for their children's declarations.

Reported only when the block holds at least one declaration of its own and ALL of them are
`_root_`-anchored.  A block with no declarations of its own is NOT reported -- it is usually
a section-like grouping around nested namespaces, and deleting it is a different judgement.

A directory-name heuristic was TRIED HERE AND REVERTED (r389).  The idea was to mark a block
whose name matches a component of the file's path as "structural" -- the file's home rather than a
mimicking wrapper -- so that `TauCeti/AlgebraicGeometry/.../Basic.lean` would keep its
`namespace AlgebraicGeometry` (78 sibling files place content there).  **The historical control
refused it**: `TauCeti/Analysis/Matrix/UnitaryGroup.lean` also sits under a matching directory, and
its `namespace Matrix` was #5820's finding -- merged, 10/10.  A name can be both a directory and a
Mathlib type, so the path tells you nothing about which it is.  Judge the outer subject-area blocks
by hand and record the call; do not encode this one.

A BLOCK THAT DECLARES NOTHING MAY STILL DO SOMETHING (r429).  `namespace Foo` also makes the
members of an EXISTING `Foo` reachable by short name -- it acts as an `open`.  `Stone/Unbounded.lean`
declares only `_root_`-anchored names, so this screen reports it, but its body writes
`isUnitary_toGroupOfInverse` and `eq_of_complexGenerator_eq` bare, and those live in
`TauCeti.Semigroups.StronglyContinuousGroup` in *other files*.  Deleting the wrapper would force both
to be spelled out -- longer code, no gain.  DECLINED on merit, not merely on breakage.

The check below catches this as a resolution hazard, which is enough to stop a bad edit; but when
judging a row, ask **"does this block do anything?"** rather than only "does it declare anything?".

THE WRAPPER MAY BE LOAD-BEARING FOR NAME RESOLUTION (r389, learned from a RED BUILD).  Inside
`namespace Foo`, a declaration written `_root_.Foo.bar` is reachable from a later sibling as plain
`bar`.  Delete the wrapper and those short references stop resolving: `unknown identifier bar`.
A block is therefore a finding only if NO declaration in it refers to a sibling by short name.
That check had a hole until r437: it skipped the ENTIRE declaration line, so a short sibling
reference sharing a line with its header -- a one-line term body, or a binder type -- was invisible.
It now has a real fixture (`fixtures/r437-vacuousns-ctl`) wired into `controls.sh`; before that its
"historical control" was a one-time run against the live tree, surviving only as a memory.
Where every internal reference is written in full -- as in #5838's `Index.lean`, which says
`Subgroup.profiniteIndex` explicitly -- removal is safe.  #5854 proposed five blocks without this
test and CI rejected three of them.

ONLY NESTED BLOCKS ARE FINDINGS (depth >= 1).  The first cut of this screen reported 50 blocks
and most were `namespace TauCeti` itself: every file in the repo opens the project namespace, and
a file whose declarations are all `_root_`-anchored trivially declares nothing into it.  Deleting
that would break the repo-wide convention, not fix anything.  The defect #5820/#5838 removed was
an INNER wrapper (`namespace Matrix` sitting inside `namespace TauCeti`), which the outer block
survives untouched.  Depth is therefore part of the finding, not a display detail.

Prints a firing control so a zero is interpretable (r184).
"""
import sys, os, re

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?'
                  r'(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+|partial\s+|unsafe\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+'
                  r'(_root_\.)?([^\W\d][\w.\'!?]*)')
NS = re.compile(r'^namespace\s+(\S+)\s*$')
END = re.compile(r'^end\s+(\S+)\s*$')

DECL_ROOT = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?'
                       r'(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+)*'
                       r'(?:theorem|lemma|def|abbrev|instance|structure|class)\s+_root_\.'
                       r"([^\W\d][\w.']*)")

# Names that are also TACTICS, and the "first token of a tactic step" test (r550).  A one-component
# suffix in that position is the tactic, not a reference: `RootPairing` declares `weylGroup.ext`,
# whose shortest suffix is `ext`, and `ext i` opens six tactic blocks in one file of #6056.
TACTICS = {'ext', 'simp', 'simpa', 'rfl', 'refl', 'symm', 'trans', 'cases', 'rcases', 'obtain',
           'intro', 'intros', 'apply', 'exact', 'constructor', 'use', 'ring', 'field_simp',
           'norm_num', 'omega', 'decide', 'positivity', 'gcongr', 'bound', 'aesop', 'tauto',
           'linarith', 'nlinarith', 'push_cast', 'norm_cast', 'congr', 'subst', 'induction',
           'rwa', 'rw', 'convert', 'refine', 'left', 'right', 'exfalso', 'contrapose',
           'by_cases', 'specialize', 'choose', 'measurability', 'continuity', 'fun_prop',
           'group', 'abel', 'module', 'grind', 'unfold', 'change', 'have', 'show', 'set'}
LEAD = re.compile(r'[\s\u00b7|;]*\Z')

# A DECLARATION'S OWN NAME IS NOT A REFERENCE TO ANOTHER DECLARATION (r563, a red build).
# The dot-lookbehind below already refuses `_root_.Foo.bar`, so a ROOTED header cannot match itself.
# A BARE header can: `theorem map_injective ...` in `namespace HomotopyGroup` looks exactly like a
# bare use of a rooted `IsCoveringMap.map_injective` declared in another file, and `xqualify`
# rewrote the HEADER -- moving `HomotopyGroup.map_injective` to `HomotopyGroup.IsCoveringMap.
# map_injective` and breaking every reference to it. A fixer must never change what a file
# declares; blank the declared name before looking for references on that line.
DECLNAME = re.compile(r'^(\s*(?:@\[[^\]]*\]\s*)?'
                      r'(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|'
                      r'scoped\s+|partial\s+|unsafe\s+)*'
                      r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+)'
                      r"([^\W\d][\w.'!?]*)")

def mask_decl_name(code):
    """Blank the NAME a declaration header introduces, leaving the rest of the line intact."""
    m = DECLNAME.match(code)
    if not m:
        return code
    a, b = m.start(2), m.end(2)
    return code[:a] + ' ' * (b - a) + code[b:]

def suffixes_below(path, wrapper):
    """Every component-boundary suffix of `path` that resolved inside `namespace wrapper`.

    r550, LEARNED FROM A RED BUILD.  This used to take `path.split('.')[-1]` -- the LAST
    component only -- and the search below refuses a name preceded by a dot.  Between them they
    made a declaration in a NESTED namespace invisible: `_root_.RootPairing.Equiv.indexHom_injective`
    was reduced to `indexHom_injective`, while the reference that actually breaks is the partially
    qualified `Equiv.indexHom_injective`.  #6056 shipped with `siblingscan` reporting 0 and CI
    returned four `Unknown constant Equiv.indexHom_injective...`.  Inside `namespace RootPairing`
    EVERY suffix of the tail resolves, so every suffix has to be searched for.
    """
    parts = path.split('.')
    if wrapper:
        w = wrapper.split('.')
        parts = parts[len(w):] if parts[:len(w)] == w else parts[-1:]
    else:
        parts = parts[-1:]
    return {'.'.join(parts[i:]) for i in range(len(parts))}

def proper_suffixes(path):
    """Every component-boundary suffix of a ROOTED name, excluding the name itself.

    The companion of `suffixes_below`, for the dual situation.  `suffixes_below` answers "the
    wrapper is being REMOVED, how could its own declaration have been written?" and so strips the
    wrapper prefix.  This answers "the declaration was rooted OUT and the wrapper SURVIVES, how
    could the rooted name have been written from inside?" -- where the name shares no prefix with
    the wrapper at all, which is exactly the case `suffixes_below` falls back to `parts[-1:]` for.

    ONE RULE, TWO CALLERS: a reference can be written as ANY component-boundary suffix, not just
    the last component.  r550 learned that from #6056 (`siblingscan` reported 0, CI returned four
    `Unknown constant Equiv.indexHom_injective`).  r625 then wrote `rootedin` from scratch with
    `rsplit('.', 1)` and reintroduced it verbatim; r643 shipped #6406 red with `Unknown identifier
    LocalGeneratorsData.IsInvertible` while `rootedin` reported ok.  The same defect, twice, with
    the fix and its rationale already written down in this file.  It lives here now so the next
    tool inherits it instead of rediscovering it.

    The full name is excluded: it always resolves at root, since the stack-prefixed form is
    precisely what the rooting removed.
    """
    parts = path.split('.')
    return {'.'.join(parts[i:]) for i in range(1, len(parts))}


def short_sibling_refs(lines, s, e, wrapper=None):
    """Short names of the block's own declarations that live CODE inside it uses unqualified.

    NOTE (r429): this only sees the block's OWN declarations.  A block can also depend on the
    namespace for members declared in OTHER files -- `Stone/Unbounded.lean` uses two.  That case is
    not detectable from one file, so a reported row still needs the repo-wide check by hand:
    collect the declarations in `namespace <X>` across the tree, then look for bare uses inside the
    block.

    Comments and docstrings must be masked first.  A docstring saying
    ``/-- Primewise form of `profiniteIndex_eq_iSup_openSubgroup`. -/`` is prose, not a
    reference, and counting it excluded two blocks that #5838 had already removed and merged
    green -- the historical control caught that immediately (r389).
    """
    names = set()
    for i in range(s - 1, min(e, len(lines))):
        m = DECL_ROOT.match(lines[i])
        if m:
            names |= suffixes_below(m.group(1), wrapper)
    hits, depth = set(), 0
    for i in range(s - 1, min(e, len(lines))):
        raw = lines[i]
        opens, closes = raw.count('/-'), raw.count('-/')
        was = depth
        depth = max(0, depth + opens - closes)
        if was or opens:                       # inside or opening a comment: prose, not code
            continue
        # Do NOT skip declaration lines (r437).  Skipping the whole line hid every short
        # sibling reference that shares a line with its header -- a one-line term body
        # (`theorem _root_.Foo.bar : True := sibling`) or a binder type (`(h : sibling)`).
        # The declaration's OWN name cannot self-match: it is spelled `_root_.Foo.bar`, and the
        # dot-lookbehind below already refuses a name preceded by `.`.
        blank = lambda m: ' ' * len(m.group(0))          # keep offsets: positions are used below
        code = re.sub(r'`[^`]*`', blank, raw)  # backticked names are prose too
        code = re.sub(r'--.*$', blank, code)   # line comment
        # An ATTRIBUTE NAME IS NOT A REFERENCE (r550).  #6056's second defect was a retarget pass
        # rewriting `@[ext]` into `@[RootPairing.weylGroup.ext]`, because `ext` is that
        # declaration's shortest suffix; CI answered `Unknown attribute`.  Once `suffixes_below`
        # started generating the short suffix, this function began reporting the restored `@[ext]`
        # as load-bearing and telling me to qualify it -- a gate aimed squarely at the bug it
        # exists to prevent.  Mask attribute brackets instead.
        code = re.sub(r'@\[[^\]]*\]', blank, code)
        code = mask_decl_name(code)             # r563: never read a header's own name as a use
        for n in names:
            for m in re.finditer(r'(?<![\w.])' + re.escape(n) + r'(?!\w)', code):
                if ('.' not in n and n in TACTICS
                        and LEAD.match(code[:m.start()].replace('<;>', '   '))):
                    continue                    # the tactic, not a reference
                hits.add(n)
                break
    return hits

def scan(path, rows, stats):
    try:
        lines = open(path, encoding='utf-8').read().split('\n')
    except Exception:
        return
    stack = []          # [name, startline, ndecl, nroot]
    incomment = 0
    for i, L in enumerate(lines):
        opens, closes = L.count('/-'), L.count('-/')
        was = incomment
        incomment = max(0, incomment + opens - closes)
        if was or opens > closes:
            continue
        m = NS.match(L)
        if m:
            stack.append([m.group(1), i + 1, 0, 0, len(stack)])
            stats['blocks'] += 1
            continue
        m = END.match(L)
        if m and stack and stack[-1][0] == m.group(1):
            name, start, nd, nr, depth = stack.pop()
            if nd > 0 and nd == nr and depth >= 1:
                if short_sibling_refs(lines, start, i + 1):
                    stats['loadbearing'] += 1
                else:
                    rows.append((path, start, i + 1, name, nd, depth))
            elif nd > 0 and nd == nr:
                stats['toplevel'] += 1
            continue
        m = DECL.match(L)
        if m and stack:
            stack[-1][2] += 1
            stats['decls'] += 1
            if m.group(2):
                stack[-1][3] += 1

def main():
    root = sys.argv[1]
    rows, stats = [], {'files': 0, 'blocks': 0, 'decls': 0, 'toplevel': 0, 'loadbearing': 0}
    for dp, _, fs in os.walk(root):
        for f in fs:
            if f.endswith('.lean'):
                stats['files'] += 1
                scan(os.path.join(dp, f), rows, stats)
    rows.sort(key=lambda r: -r[4])
    for p, s, e, name, nd, depth in rows:
        print(f"{p}:{s}-{e}\tnamespace {name} (depth {depth})\t{nd} decl(s), ALL `_root_`-anchored")
    print(f"# FIRING CONTROL: {stats['files']} files, {stats['blocks']} namespace blocks, "
          f"{stats['decls']} declarations attributed to an enclosing block; "
          f"{len(rows)} NESTED blocks declare nothing into themselves; "
          f"{stats['toplevel']} top-level blocks also declare nothing but are NOT findings "
          f"(they are the file's own `namespace TauCeti`). "
          f"{stats['loadbearing']} excluded as LOAD-BEARING (a sibling is referenced by short name, "
          f"so deleting the wrapper breaks resolution -- r389, learned from a red build). "
          f"(Blocks with no declarations of their own are deliberately NOT reported.)",
          file=sys.stderr)

if __name__ == '__main__':
    main()
