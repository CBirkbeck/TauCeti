#!/usr/bin/env python3
"""stalequal.py [--base <ref>] <snapshot> <file.lean>... -- names a change leaves DANGLING, prose included.

The #5953 defect, caught by three rubrics at once (api-design, naming, documentation).
Rooting `TauCeti.ValuativeRel.comap` to `_root_.ValuativeRel.comap` destroys the path
`TauCeti.ValuativeRel.comap`.  Two references still spelled it in full -- the `Main definitions`
bullet in the moved file and a proof-sketch paragraph in `IntegralOfValuationLeOne.lean`.  Both
are PROSE, so the build stayed green and every code-level check passed.

WHY NO EXISTING SCREEN SAW IT.  `vacuousns.short_sibling_refs` masks backticks and comments
before matching, and it must: its question is "will this still RESOLVE?", and prose resolves
nothing.  That masking is correct there and structurally blind here.  `lintcand.py` does count
these (its `qual=` column), but only along the single-declaration path -- the
namespace-at-a-time recipe (r483+) never picked the check up.  A check that lives in one lane's
tool is not a check the other lane has.

SCAN THE WHOLE REPOSITORY, NOT `TauCeti/` (r493, learned from a SECOND blocking round).  r491
ran this over snapshots built with `git archive <rev> TauCeti` and reported #5950 clean.  It was
not: `web/examples/Examples.lean:45` said `TauCeti.BialgHom.toLinearMap_comp_antipode φ` in CODE,
and `naming` blocked on it.  Two things hid it -- the scan root, and the fact that `web/examples`
is a SEPARATE LAKE PROJECT that the sandboxed build never compiles, so CI was green with a
reference that cannot resolve.  A rooting kills the old path everywhere in the repo; `TauCeti/` is
where the DECLARATIONS live, not where the REFERENCES do.  The guard below refuses a root holding
no `.lean` file outside `TauCeti/`, because a real checkout always has `TauCeti.lean` and `web/`.

DERIVE THE OLD NAME, DO NOT INFER IT (r564).  Without `--base` this tool assumes every rooted
declaration used to be `TauCeti.<new name>`.  That is true of an ordinary rooting and false the
moment a declaration came from somewhere else: #6093 renamed `HomotopyGroup.map_injective` -- a
top-level declaration outside `namespace TauCeti`, never flagged -- into
`HomotopyGroup.IsCoveringMap.map_injective`, and the old path had no `TauCeti.` prefix to guess at.
CI found it; this tool could not have.  With `--base <ref>` the stale set is computed exactly:
every full name declared in a target at the base and absent from it at HEAD, whatever its prefix.
That subsumes the assumption rather than replacing it -- an ordinary rooting yields the same
`TauCeti.` paths it always did.

MATCH THE FULL DECLARATION NAME, NEVER THE NAMESPACE PREFIX.  Grepping
`TauCeti.Algebra.TensorProduct` across the tree returns MODULE IMPORT PATHS
(`import TauCeti.Algebra.TensorProduct.CommonOverfield`) and references to OTHER members of the
namespace that this PR did not move (`baseChangeTensorAlgEquiv`) -- 10+ hits on #5959, every one
of them a false alarm.  Only the moved declaration's own full name is stale.

Prints a firing control so a zero is interpretable (r184).

LEAN IDENTIFIERS ARE NOT ASCII (r494, anchor miss number SIX).  The old class -- an ASCII-only
head (A-Z, a-z, underscore) followed by an ASCII-only body -- does not FAIL on
`eval_Ψ₃_of_a₁_eq_zero`; it matches `eval_` and stops, yielding a WRONG NAME rather than no name.
(Spelled in prose deliberately: r497 swept the literal class across the toolkit and rewrote this
very sentence, turning the record of the defect into a description of the fix.)  In this tool that undercounts a namespace's total, so a partial namespace
reads as WHOLE, which is the one direction that ships a bad PR.  `TauCeti.WeierstrassCurve` came
out at 26 flagged of 22 total -- a ratio above 1, the arithmetic tell.  22 of 994 findings (2.2%)
carry a non-ASCII name.  Use a Unicode-aware class (see the pattern below); `str` regexes are Unicode by default.
"""
import sys, os, re, subprocess, tempfile, importlib.util

_HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("nss", os.path.join(_HERE, "nsslice.py"))
nss = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(nss)

DECL_ROOT = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?'
                       r'(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+)*'
                       r'(?:theorem|lemma|def|abbrev|instance|structure|class)\s+_root_\.'
                       r"([^\W\d][\w.'!?]*)")

def full_names(path):
    """Every full declaration name a file introduces, `_root_.` honoured."""
    out = set()
    for ns, short, _rooted in nss.walk(path):
        out.add(f"{ns}.{short}" if ns else short)
    return out

def main():
    # Takes MANY targets and walks the tree ONCE (r540): prepush called it per changed file, and a
    # 13-file PR meant 13 walks.  The walk is not the expensive part though -- see the substring
    # guard in the loop below, which is what actually made it fast.
    argv, base = sys.argv[1:], None
    if '--base' in argv:
        i = argv.index('--base'); base = argv[i + 1]; del argv[i:i + 2]
    snap, targets = argv[0], argv[1:]
    missing = [t for t in targets if not os.path.isfile(t)]
    if missing:
        # UNRUN, not a traceback and not a pass.  A caller that passes one newline-joined argument
        # (zsh does not word-split an unquoted `$var`, only `$(...)`) used to reach `open()` and
        # die with `File name too long` -- a nonzero exit that `prepush` would have read as "a dead
        # path survives" (r564).  Say what is wrong instead.
        print(f"# UNRUN: {len(missing)} target(s) are not files, e.g. {missing[0][:100]!r}. "
              f"Refusing to report on a partial target list.", file=sys.stderr)
        return 2
    moved = []
    for target in targets:
        for L in open(target, encoding='utf-8').read().split('\n'):
            m = DECL_ROOT.match(L)
            if m:
                moved.append(m.group(1))
    # The `moved` guard belongs to the LEGACY path only.  With `--base` the stale set comes from
    # comparing declarations, and the case that motivated `--base` -- a rename INTO a namespace,
    # with no `_root_.` anywhere -- has an empty `moved` by construction.  Running the guard first
    # made the new mode return "nothing to check" on exactly the input it was written for (r564).
    if not base and not moved:
        print(f"# FIRING CONTROL: no `_root_.`-rooted declaration in {len(targets)} file(s); nothing to check. "
              f"If the file WAS rooted this round, the declaration pattern missed it -- five "
              f"anchors have now failed this way (r458/r481/r487/r490).", file=sys.stderr)
        return 0
    if base:
        gone = set()
        for t in targets:
            head = full_names(t)
            r = subprocess.run(['git', 'show', f'{base}:{t}'], capture_output=True, text=True)
            if r.returncode:
                continue                                  # new file: nothing could be stale
            with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as tf:
                tf.write(r.stdout); tmp = tf.name
            gone |= full_names(tmp) - head
            os.unlink(tmp)
        stale = {n: [] for n in gone}
    else:
        stale = {"TauCeti." + n: [] for n in moved}
    if not stale:
        print("# FIRING CONTROL: no declaration disappeared from the given file(s); nothing to "
              "check.", file=sys.stderr)
        return 0
    heads = {n.split('.')[0] for n in stale}              # cheap substring guard (r540)
    nfiles, noutside = 0, 0
    for dp, _, fs in os.walk(snap):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            nfiles += 1
            rel = os.path.relpath(p, snap)
            if not rel.startswith("TauCeti" + os.sep):
                noutside += 1
            try:
                txt = open(p, encoding='utf-8').read().split('\n')
            except Exception:
                continue
            for i, L in enumerate(txt, 1):
                # ONE substring test before any regex (r540).  The inner loop was a regex per NAME
                # per LINE: 22 names x ~4,600 files is millions of searches and a single walk took
                # over ten minutes.  Almost no line mentions `TauCeti.` at all.  Sharing the walk
                # across files -- the fix I reached for first -- was the wrong axis entirely.
                if not any(h in L for h in heads):
                    continue
                for k in stale:
                    if k not in L:
                        continue
                    # a trailing name character means this is a LONGER name, not ours
                    for m in re.finditer(re.escape(k) + r'(?![\w.\'])', L):
                        stale[k].append((p.replace(snap + "/", ""), i, L.strip()[:100]))
    # The direct question, not a proxy: a REPOSITORY ROOT contains a `TauCeti/` directory; the
    # `TauCeti/` subtree does not.  Counting files "outside TauCeti/" gets this backwards when the
    # subtree IS the root -- then every file is outside and the guard stays silent.
    if not os.path.isdir(os.path.join(snap, "TauCeti")):
        print(f"stalequal: {snap} has no TauCeti/ directory -- this looks like the `TauCeti/`\n"
              f"           subtree, not the repository root.  A real checkout has TauCeti.lean and\n"
              f"           web/examples/Examples.lean; r491 scanned the subtree, reported #5950\n"
              f"           clean, and `naming` blocked on web/examples/Examples.lean:45.  Re-run\n"
              f"           against the repository root.", file=sys.stderr)
        return 2
    nhit = 0
    for k in sorted(stale):
        for p, i, txt in stale[k]:
            nhit += 1
            print(f"STALE  {k}\n       {p}:{i}\n       | {txt}")
    print(f"# FIRING CONTROL: {len(moved)} rooted declaration(s) in {os.path.basename(target)} "
          f"({', '.join(moved[:4])}{'...' if len(moved) > 4 else ''}) across {len(targets)} "
          f"target file(s) in ONE walk; {nfiles} files scanned, "
          f"{noutside} of them OUTSIDE TauCeti/ (where r491's miss lived); "
          f"{nhit} reference(s) still spell the dead `TauCeti.` path. Prose counts: #5953 was green "
          f"and code-clean with 2 such references, and three rubrics blocked on them. Matching is on "
          f"the FULL name -- a namespace-prefix grep returns import paths and unmoved siblings.",
          file=sys.stderr)
    return 1 if nhit else 0

if __name__ == '__main__':
    sys.exit(main())
