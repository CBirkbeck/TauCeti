#!/usr/bin/env python3
"""nsbalance.py <base-ref> <file.lean>... -- did this PR break `namespace`/`section`/`end`?

THE r551 RED BUILD, and the third defect in #6056 alone.  The wrapper-conversion pass rewrote
`namespace RootPairing.weylGroup` to `section`, then rewrote the FIRST `end` it met rather than the
MATCHING one.  A nested `section LowerBound` sat in between, so:

    83:  namespace RootPairing.weylGroup  ->  section          (correct)
    181: section LowerBound                   section LowerBound
    269: end LowerBound                   ->  end              (WRONG: closes nothing by that name)
    324: end RootPairing.weylGroup            end RootPairing.weylGroup   (never rewritten)

Lean: `Missing name after 'end': Expected the current scope name 'LowerBound'`, and then five
further errors -- `Overlapping instance parameters`, `automatically included section variable(s)
unused` -- which are all downstream of the section that never closed.  Those five look like real
mathematical findings and are not; chasing them instead of the bracket would have wasted a round.

A positional heuristic ("the next `end`") is wrong whenever anything nests.  This is a stack, so
match it with a stack.  Cheap, exact, and it needs no Mathlib and no base tree.

REPORTED AS A DELTA AGAINST THE BASE, NEVER ABSOLUTELY.  The first cut judged files on their own
and produced **4600 rows against green `main`**: nearly every file opens `public section` or
`noncomputable section` and never closes it, which Lean is happy with at end of file.  Nine further
rows were legal Lean this stack model does not cover -- `end A.B` may close two nested scopes at
once, for one.  A gate that manufactures thousands of findings on a green tree is worse than no
gate, and `main` being green is exactly what makes the delta trustworthy: any complaint the BASE
version of a file also produces is a modelling artefact, so only complaints this PR ADDS are
reported. Same discipline as the lint and importcover deltas in `prepush.sh`.

Lean's rules, as modelled here:
  * `namespace A.B`   is ONE scope, closed only by `end A.B`.
  * `section`         (anonymous) is closed only by a bare `end`.
  * `section A`       is closed only by `end A`.
So a bare `end` facing a named scope, or `end X` facing a scope named otherwise, is an error --
which is precisely what Lean reports, one file at a time, only once the build reaches that file.
#6056's BraidRelation.lean was never reached in the first failing build at all.
"""
import sys, os, re, subprocess

# MODIFIERS COUNT (r551).  The first cut anchored on `^(namespace|section)` and reported three
# mismatches in a file that was FINE: `noncomputable section` and `public section` both open an
# anonymous scope, and neither starts with `section`.  That is the anchor-miss family again -- the
# tenth time a pattern has silently returned the wrong answer (r458/r481/r487/r490/r494/r497/
# r540/r547/r550) -- and here it manufactured findings instead of hiding them.
OPEN = re.compile(r'^(?:@\[[^\]]*\]\s*)?'
                  r'(?:public\s+|private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+|'
                  r'scoped\s+)*'
                  r'(namespace|section)(?:\s+(\S+))?\s*$')
END = re.compile(r'^end(?:\s+([^\s]+))?\s*$')

def strip_lines(msg):
    """Message with every line number removed, so base and head rows compare across edits."""
    return re.sub(r'\d+', 'N', msg)

def check(path):
    try:
        lines = open(path, encoding='utf-8').read().split('\n')
    except Exception as e:
        return [f"{path}: unreadable: {e}"], 0, 0
    return check_lines(lines, path)

def check_lines(lines, path):
    stack, bad, depth, nopen = [], [], 0, 0
    for i, L in enumerate(lines, 1):
        o, c = L.count('/-'), L.count('-/')
        was = depth
        depth = max(0, depth + o - c)
        if was or o > c:
            continue
        m = OPEN.match(L)
        if m:
            if m.group(1) == 'namespace' and not m.group(2):
                bad.append(f"{path}:{i}: `namespace` with no name")
            else:
                stack.append((m.group(1), m.group(2), i)); nopen += 1
            continue
        m = END.match(L)
        if m:
            name = m.group(1)
            if not stack:
                bad.append(f"{path}:{i}: {'`end ' + name + '`' if name else 'a bare `end`'}"
                           f" with no open scope left")
                continue
            kind, sname, sline = stack.pop()
            if name != sname:
                want = f"`end {sname}`" if sname else "a bare `end`"
                got = f"`end {name}`" if name else "a bare `end`"
                bad.append(f"{path}:{i}: {got} closes the {kind} opened at line {sline} "
                           f"({'anonymous' if not sname else '`' + sname + '`'}) -- expected {want}")
    for kind, sname, sline in reversed(stack):
        # An ANONYMOUS section left open at end of file is normal, not a defect: `public section`
        # and `noncomputable section` span the rest of the file and green `main` leaves 4600 of
        # them open. Only a NAMED scope that never closes is worth a row.
        if sname:
            bad.append(f"{path}:{sline}: {kind} `{sname}` is never closed")
    return bad, nopen, len(stack)

def main():
    base, files = sys.argv[1], sys.argv[2:]
    rows, nopen, nfiles, nbase = [], 0, 0, 0
    for f in files:
        if not os.path.exists(f):
            print(f"# UNRUN: {f} does not exist -- refusing to report on a partial file list.",
                  file=sys.stderr)
            return 2
        b, n, _ = check(f)
        nfiles += 1; nopen += n
        try:
            src = subprocess.run(['git', 'show', f'{base}:{f}'], capture_output=True, text=True,
                                 check=True).stdout
        except subprocess.CalledProcessError:
            prior = set()                                   # new file: everything is new
        else:
            pb, _, _ = check_lines(src.split('\n'), f)
            prior = {strip_lines(x) for x in pb}
            nbase += len(pb)
        for x in b:
            if strip_lines(x) not in prior:
                rows.append(x)
    for r in rows:
        print("UNBALANCED  " + r)
    print(f"# FIRING CONTROL: {nfiles} file(s), {nopen} `namespace`/`section` scope(s) opened; "
          f"{nbase} complaint(s) the BASE versions also produce (modelling artefacts on a green "
          f"tree -- `public section` is normally never closed); {len(rows)} NEW here. A positional "
          f"'next `end`' rewrite is wrong whenever anything nests -- #6056 converted a wrapper and "
          f"renamed the `end` of the section INSIDE it (r551).", file=sys.stderr)
    return 1 if rows else 0

if __name__ == '__main__':
    sys.exit(main())
