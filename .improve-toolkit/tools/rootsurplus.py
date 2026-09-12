#!/usr/bin/env python3
"""rootsurplus.py --base <ref> <flagged-file> <file.lean>... -- does this PR root MORE than the
linter asked for?

THE GAP #6148 FOUND (r605).  `rootns` moves a whole `namespace` block, so a PR roots every
declaration in the wrapper -- not the subset the linter flagged.  On #6148 that was
`lint-dot-notation`: 11 findings, PR: 17 rooted.  The six-declaration surplus was
`genEigenspaceSuccMap`, `finiteDimensional_genEigenspace_succ`,
`finiteDimensional_genEigenspace_nat_of_eigenspace`, `exists_riesz`, `eq_of_apply_eq_of_succ_eq` and
`mkQ_comp_ker_subtype_surjective` -- all `private`, all general, none of them flagged. The PR was
asserting an `IsCompactOperator` receiver for six helpers on its own initiative, which is the
"relocating entrenches a receiver the construction does not need" defect that `generality` blocked
#6093 on.  `api-design` caught it; the gate did not, and the gate had every fact it needed.

NONE of the twelve existing checks asks this.  `slice` asks whether a file's flagged declarations
were rooted in full; `decldiff` asks whether each change is a rooting; `nsslice` asks whether a
namespace is left half-rooted.  All three are satisfied by rooting MORE than was asked.

A surplus is not automatically wrong -- a private helper genuinely belonging to the namespace may
travel with it, and a wrapper cannot be retired while leaving members behind.  But it is a claim the
PR makes on its own authority, so it must be deliberate and stated, not discovered by a reviewer.
"""
import sys, os, re, subprocess, tempfile, importlib.util

_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("nsl", os.path.join(_here, "nsslice.py"))
_nsl = importlib.util.module_from_spec(_spec)
try:
    _spec.loader.exec_module(_nsl)
except SystemExit:
    pass

def rooted_full_names(path):
    """{full name} for every `_root_.`-anchored declaration in one file."""
    out = set()
    for ns, short, is_root in _nsl.walk(path):
        if is_root and ns:
            out.add(f"{ns}.{short}")
    return out

def main():
    argv = sys.argv[1:]
    base = None
    if '--base' in argv:
        i = argv.index('--base'); base = argv[i + 1]; del argv[i:i + 2]
    if len(argv) < 2:
        print("# UNRUN: usage: rootsurplus.py --base <ref> <flagged-file> <file.lean>...",
              file=sys.stderr)
        return 2
    flagged_file, targets = argv[0], [os.path.normpath(t) for t in argv[1:]]
    missing = [t for t in targets if not os.path.exists(t)]
    if missing:
        print(f"# UNRUN: {len(missing)} target(s) do not exist, e.g. {missing[0][:100]!r}.",
              file=sys.stderr)
        return 2
    try:
        rows = open(flagged_file, encoding='utf-8').read().split('\n')
    except Exception as e:
        print(f"# UNRUN: cannot read the flagged set ({e}).", file=sys.stderr)
        return 2
    flagged = set()
    for r in rows:
        m = re.search(r':\s*(TauCeti\.[\w.\'!?]+)\s*$', r)
        if m:
            flagged.add(m.group(1))
    if not flagged:
        print("# UNRUN: the flagged set is empty -- every rooted declaration would look surplus.",
              file=sys.stderr)
        return 2

    newly = set()
    for t in targets:
        head = rooted_full_names(t)
        if base:
            g = subprocess.run(['git', 'show', f'{base}:{t}'], capture_output=True, text=True)
            if g.returncode == 0:
                with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as tf:
                    tf.write(g.stdout); tmp = tf.name
                head -= rooted_full_names(tmp)
                os.unlink(tmp)
        newly |= head

    surplus = sorted(n for n in newly if f"TauCeti.{n}" not in flagged)
    for n in surplus:
        print(f"SURPLUS  `{n}` is rooted by this PR but `TauCeti.{n}` is not flagged by the linter")
    print(f"# FIRING CONTROL: {len(flagged)} flagged declaration(s) in the base, {len(newly)} newly "
          f"rooted by this PR, {len(surplus)} of them NOT flagged. A surplus is a claim the PR makes "
          f"on its own authority -- #6148 rooted 17 where 11 were flagged and `api-design` blocked "
          f"the six (r605). Zero here means the PR moves exactly what was asked.", file=sys.stderr)
    return 1 if surplus else 0

if __name__ == '__main__':
    sys.exit(main())
