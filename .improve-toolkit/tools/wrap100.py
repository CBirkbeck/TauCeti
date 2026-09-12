#!/usr/bin/env python3
"""wrap100.py <file.lean>... -- break added lines that exceed 100 characters.

Rooting a namespace makes lines longer: every internal reference grows by the length of the
namespace plus a dot, and `ContinuousLinearMap` alone is twenty characters.  r553's extraction left
**48** over-width lines, which is too many to place by hand without introducing a mistake.

THE RULE: break at the last space **at bracket depth zero** before column 100, and re-indent the
remainder deeper than the line it continues (four for a declaration header, two otherwise, which is
what the surrounding files already do).  Lean continues an expression or a tactic across lines
whenever the continuation is indented FURTHER than the line that opened it, so a strictly deeper
continuation is never read as a new tactic.

DEPTH ZERO IS THE PART THAT MATTERS.  The first cut broke at the last space of any kind, which Lean
accepts -- whitespace inside parentheses is nothing to it -- and which produced

    theorem _root_.ContinuousLinearMap.isInvertible_of_injective {K E : Type*} [NontriviallyNormedField
      K] [CompleteSpace K]

splitting a binder across the break.  It compiles and no linter objects, because the only rule CI
enforces here is the column count; a reviewer would object, and would be right.  Breaking between
binder groups instead gives back exactly the layout these files already use.

WHAT IT REFUSES TO TOUCH, because the rule is not safe there:
  * anything INSIDE a block comment or docstring, tracked by `/-` .. `-/` depth rather than by how
    a line begins: prose wraps by meaning, not by column. The first cut only skipped lines that
    OPEN a comment, so it split a `*` bullet inside a `/-! ... -/` header away from its own URL and
    left the URL over the limit anyway. r497 learned this once already, when a blanket sweep
    rewrote the very docstrings that documented the bug;
  * a line with no space before column 100 -- one very long identifier or path, where any break
    would fall inside a name;
  * `import`, `open`, `namespace`, `section`, `end`, `set_option` and `variable` lines, where a
    continuation changes the meaning rather than the layout.
Those are listed instead, for a person.

ITERATE TO A FIXED POINT.  A break can leave a continuation that is itself over 100 (r549: 101
wraps, then 5 more), so the pass repeats until nothing changes.
"""
import sys, os, re

DECLHEAD = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\b')
SKIP = re.compile(r'^\s*(--|/-|import\b|open\b|namespace\b|section\b|end\b|set_option\b|variable\b)')
LIMIT = 100

def indent_of(s):
    return len(s) - len(s.lstrip(' '))

def wrap_line(L):
    """One break, or None if this line must be left alone."""
    if len(L) <= LIMIT or SKIP.match(L) or '"' in L or '`' in L:
        return None
    ind = indent_of(L)
    depth, cut = 0, -1
    for i, ch in enumerate(L):
        if i > LIMIT:
            break
        if ch in '([{\u27e8':
            depth += 1
        elif ch in ')]}\u27e9':
            depth = max(0, depth - 1)
        elif ch == ' ' and depth == 0 and i > ind:
            cut = i
    # SECOND CANDIDATE: a comma inside a `rw`/`simp` argument list. Such a list is ONE depth-zero
    # token, so the depth-zero rule alone either refuses the line or -- worse -- breaks at the space
    # after `rw`, stranding the bracket on its own line. Take whichever candidate lies FURTHER
    # RIGHT: the comma wins inside a list, and binder boundaries still win in a declaration header,
    # which carries no depth-one commas.
    depth, ccut = 0, -1
    for i, ch in enumerate(L):
        if i > LIMIT:
            break
        if ch in '([{\u27e8':
            depth += 1
        elif ch in ')]}\u27e9':
            depth = max(0, depth - 1)
        elif ch == ',' and depth == 1 and i + 1 < len(L) and L[i + 1] == ' ':
            ccut = i + 1
    cut = max(cut, ccut)
    if cut <= ind:                       # nothing idiomatic to break on: leave it for a person
        return None
    head, tail = L[:cut].rstrip(), L[cut + 1:].strip()
    if not tail:
        return None
    step = 4 if DECLHEAD.match(L) else 2
    return [head, ' ' * (ind + step) + tail]

def main():
    files = sys.argv[1:]
    total, refused = 0, []
    for f in files:
        if not os.path.exists(f):
            print(f"# UNRUN: {f} does not exist.", file=sys.stderr); return 2
        lines = open(f, encoding='utf-8').read().split('\n')
        for _pass in range(12):
            changed, out, depth = False, [], 0
            for L in lines:
                o, c = L.count('/-'), L.count('-/')
                was = depth
                depth = max(0, depth + o - c)
                w = None if (was or o) else wrap_line(L)   # inside or opening a comment: prose
                if w:
                    out.extend(w); changed = True; total += 1
                else:
                    out.append(L)
            lines = out
            if not changed:
                break
        depth = 0
        for i, L in enumerate(lines, 1):
            o, c = L.count('/-'), L.count('-/')
            was = depth
            depth = max(0, depth + o - c)
            if len(L) > LIMIT and not (was or o):
                refused.append(f"{f}:{i} ({len(L)}) {L.strip()[:70]}")
        open(f, 'w', encoding='utf-8').write('\n'.join(lines))
    for r in refused:
        print("LEFT     " + r)
    print(f"# FIRING CONTROL: {len(files)} file(s), {total} break(s) inserted, "
          f"{len(refused)} line(s) still over {LIMIT} and LEFT for a person (comments, docstrings, "
          f"single long tokens, and `open`/`namespace`-family lines are never touched). "
          f"Continuations are indented two further than the line they continue, which is what makes "
          f"them continuations to Lean rather than new tactics.", file=sys.stderr)
    return 1 if refused else 0

if __name__ == '__main__':
    sys.exit(main())
