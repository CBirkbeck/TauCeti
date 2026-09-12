#!/usr/bin/env python3
"""nsjump.py <base-ref> <file.lean>... -- did this PR move a REFERENCE to an unrelated namespace?

THE DEFECT #6188 SHIPPED TO CI (r622).  `improve/linearequiv-root` sat gate-clean through six
re-gates over 29 rounds and failed its first build with

    Lattice.lean:300: Unknown identifier `LieSubalgebra.rationalizationEquiv`
    Lattice.lean:155: Type mismatch                (AlgHom.restrictScalars_apply)

because `xqualify`/`deadfix` had picked a candidate by matching the TAIL of a name (the r556 class)
and rewritten two reference families into namespaces that have nothing to do with them:

    Submodule.rationalizationEquiv        ->  LieSubalgebra.rationalizationEquiv   (3x)
    LinearEquiv.restrictScalars_apply     ->  AlgHom.restrictScalars_apply         (2x)

**`deadpath` cannot see this.**  It asks whether a qualified name exists SOMEWHERE in the index, and
names of that shape do exist elsewhere in the tree.  It cannot ask whether the name is reachable from
this file's imports, or whether it is the RIGHT declaration.  Existence is not resolution, and until
now only a red build could tell them apart.

THE RULE.  Pair every qualified name the diff REMOVES with one it ADDS that has the same tail.  A
rewrite is legitimate when the two prefixes are RELATED -- one is an extension or a truncation of the
other, which is exactly what rooting does:

    TauCeti.Submodule.foo  ->  Submodule.foo               truncation  (the rooting itself)
    LocalGeneratorsData.x  ->  SheafOfModules.LocalGeneratorsData.x   extension (r600)

and suspicious when it JUMPS -- neither prefix contains the other:

    Submodule.rationalizationEquiv  ->  LieSubalgebra.rationalizationEquiv    <- the bug

A jump is not proof of a defect (a declaration may genuinely have moved namespaces), but every
instance of the r556 class has this shape, and nothing else in this lane produces it.

IT DIFFS THE WORKING TREE, NOT TWO COMMITS.  `git diff <base> -- <files>` compares the base against
what is checked out, which is what `prepush` wants.  Auditing a PAST commit therefore means checking
it out first; running it with a commit merely named on the command line silently measures whatever
branch happens to be current (r623 -- I did exactly that and read the 0 as a regression).
"""
import sys, os, re, subprocess

# A ONE-LETTER HEAD IS A BINDER, NOT A NAMESPACE (r623).  Lean writes dot notation on local
# variables constantly -- `S.comp`, `T.comp`, `W.polynomial.eval` -- and the r622 cut treated those
# as qualified names, so auditing seven MERGED, CI-green PRs produced three "jumps" that were all
# binders.  Every namespace in this tree is a CamelCase word; no declaration lives in `S`.
QUAL = re.compile(r"(?<![\w.])([A-Z][A-Za-z0-9_']+(?:\.[A-Za-z0-9_'!?]+)+)")

def names(lines):
    """Qualified names a diff line REFERS TO -- prose mentions are not references (r646).

    r640: rooting `IsCoveringMap.isOpenQuotientMap` reported a jump to
    `IsQuotientCoveringMap.isOpenQuotientMap`, which no code in the PR ever wrote.  The only
    occurrence was one added DOCSTRING line naming Mathlib's companion theorem.  A check that
    cannot tell prose from code spends a reviewer's attention on sentences.

    Backticks are the discriminator, and a reliable one: a Lean docstring writes a declaration as
    `` `Foo.bar` `` and code never does.  Line comments go too.  Block-comment state cannot be
    tracked from a diff hunk -- the opening `/--` is often outside the context -- but a docstring
    that names a declaration puts it in backticks, so masking those spans covers the case that
    actually fires.  (`vacuousns` masks comments and backticks for the same reason.)
    """
    out = set()
    for L in lines:
        L = re.sub(r'`[^`]*`', ' ', L)        # prose reference, not a use
        L = re.sub(r'--.*$', ' ', L)          # line comment
        L = re.sub(r'/-.*?-/', ' ', L)        # single-line block comment
        for m in QUAL.finditer(L):
            out.add(m.group(1))
    return out

def related(a, b):
    """Is one prefix an extension or truncation of the other, on component boundaries?"""
    if a == b:
        return True
    return (a.endswith('.' + b) or b.endswith('.' + a)
            or a.startswith(b + '.') or b.startswith(a + '.'))

def main():
    if len(sys.argv) < 3:
        print("# UNRUN: usage: nsjump.py <base-ref> <file.lean>...", file=sys.stderr)
        return 2
    base, targets = sys.argv[1], [os.path.normpath(t) for t in sys.argv[2:]]
    missing = [t for t in targets if not os.path.isfile(t)]
    if missing:
        print(f"# UNRUN: {len(missing)} target(s) are not files, e.g. {missing[0][:100]!r}.",
              file=sys.stderr)
        return 2
    d = subprocess.run(['git', 'diff', f'{base}', '--'] + targets,
                       capture_output=True, text=True)
    if d.returncode:
        print(f"# UNRUN: git diff against {base!r} failed.", file=sys.stderr)
        return 2
    rem = names([l[1:] for l in d.stdout.split('\n') if l.startswith('-') and not l.startswith('---')])
    add = names([l[1:] for l in d.stdout.split('\n') if l.startswith('+') and not l.startswith('+++')])
    # A NAME ON BOTH SIDES OF THE DIFF DID NOT MOVE, so it cannot be the SOURCE of a jump (r649).
    # #6413 qualifies a bare `frobeniusSchurIndicator` to `FDRep.frobeniusSchurIndicator` on a line
    # that also mentions `Representation.frobeniusSchurIndicator` — unchanged, present in both the
    # removed and the added text. Pairing by tail then offered that survivor as the origin of a
    # `Representation` → `FDRep` jump, which is precisely the r556 defect this check exists to
    # catch, reported on a line where it did not happen. Rewriting a line re-emits every name on
    # it, so the removed set is full of names that merely came along.
    by_tail = {}
    for r in rem - add:
        by_tail.setdefault(r.rsplit('.', 1)[1], set()).add(r)

    # AN ADDED NAME IS SUSPICIOUS ONLY IF *NO* SAME-TAIL COUNTERPART EXPLAINS IT.  Pairing each
    # added name against every removed one with the same tail produces two false-positive families,
    # both seen on real branches:
    #   * a rearrangement -- the diff removes and re-adds BOTH `MulEquiv.trans_apply` and
    #     `LinearEquiv.trans_apply`, so each pairs with the other and reports a jump in both
    #     directions, on a branch whose build is green;
    #   * two distinct declarations sharing a tail -- `LocalGeneratorsData.IsInvertible.ofIso` and
    #     `LocalGeneratorsData.ofIso` both end in `ofIso`, and cross-pairing them invents a jump.
    # Requiring that NOTHING related explains the added name dissolves both: an identical prefix is
    # related to itself, and the genuine rooting counterpart is an extension or truncation.
    jumps, pairs = [], 0
    for a in sorted(add):
        tail = a.rsplit('.', 1)[1]
        ap = a.rsplit('.', 1)[0]
        cands = sorted(by_tail.get(tail, ()))
        if not cands:
            continue
        pairs += 1
        if any(related(r.rsplit('.', 1)[0], ap) for r in cands):
            continue                              # a related counterpart explains this rewrite
        for r in cands:
            jumps.append((r, a))
    for r, a in jumps:
        print(f"NS-JUMP  `{r}` became `{a}` -- the namespaces are unrelated, so a fixer may have "
              f"matched on the tail alone (r556)")
    print(f"# FIRING CONTROL: {len(rem)} qualified name(s) removed, {len(add)} added, {pairs} "
          f"same-tail rewrite(s), {len(jumps)} of them JUMPING to an unrelated namespace. A rooting "
          f"rewrite is an extension or a truncation of its old prefix; a jump is the r556 shape that "
          f"#6188 shipped to CI. Zero here means no reference changed namespace families.",
          file=sys.stderr)
    return 1 if jumps else 0

if __name__ == '__main__':
    sys.exit(main())
