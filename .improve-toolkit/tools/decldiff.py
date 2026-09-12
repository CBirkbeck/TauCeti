#!/usr/bin/env python3
"""decldiff.py <base-ref> <file.lean>... -- which declarations did this PR add, remove or rename?

A rooting PR is supposed to do exactly one thing to the declaration set: turn `TauCeti.X.y` into
`X.y`.  Three CI failures came from a tool editing a line that merely LOOKED like a reference:

    r550  `@[ext]`                      -> `@[RootPairing.weylGroup.ext]`   (an attribute)
    r561  `structure on its functor…`   -> `structure _root_.AlgHom.on …`   (a docstring line)
    r563  `theorem map_injective`       -> `theorem IsCoveringMap.map_injective`  (a HEADER)

**This check covers the second and third, not the first.**  r561 and r563 changed what the file
DECLARES, so they show up here; r550 rewrote an attribute and left the declaration set untouched, so
nothing below would have seen it.  Saying so is the point -- a screen that is described as catching
more than it does is how the next one gets skipped.

`stalequal --base` catches the consequence -- a reference left pointing at the old name.  It cannot
catch a rename nothing happens to reference, and it says nothing about what was ADDED.  This asks
the question directly: **after pairing each removed `TauCeti.X.y` with the added `X.y` that
replaces it, is anything left over?**  On a clean rooting the residue is empty.  r563's residue
would have been one of each -- `HomotopyGroup.map_injective` gone,
`HomotopyGroup.IsCoveringMap.map_injective` arrived -- and neither is a rooting.

It reads only the changed files, so it costs a `git show` apiece and no tree walk.

A DE-ROOTING IS NOT UNEXPLAINED RESIDUE (r606).  This lane's PRs are sometimes asked to root LESS:
`api-design` on #6148 found six general private helpers that had been rooted into `IsCompactOperator`
without the linter ever flagging them, and the fix drops the prefix -- `TauCeti.IsCompactOperator.x`
out, `TauCeti.x` in.  That is a rename in the opposite direction, and pairing only
`TauCeti.X.y` -> `X.y` reported it as six VANISHED plus six APPEARED with the message *"no rooting
explains it"*, which was simply false: a de-rooting explains it exactly.

So the pass now pairs both directions and labels the second `DE-ROOTED`.  It still BLOCKS -- dropping
a namespace level is a real change to the declaration set and belongs in the PR body -- but the
operator is told what happened instead of being handed twelve rows of mystery.
"""
import sys, os, subprocess, tempfile, importlib.util

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("nss", os.path.join(HERE, "nsslice.py"))
nss = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(nss)

def names(path):
    return {f"{ns}.{short}" if ns else short for ns, short, _r in nss.walk(path)}

def base_names(base, path):
    r = subprocess.run(['git', 'show', f'{base}:{path}'], capture_output=True, text=True)
    if r.returncode:
        return None                                   # new file
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as tf:
        tf.write(r.stdout); tmp = tf.name
    try:
        return names(tmp)
    finally:
        os.unlink(tmp)

def main():
    base, targets = sys.argv[1], sys.argv[2:]
    missing = [t for t in targets if not os.path.isfile(t)]
    if missing:
        print(f"# UNRUN: {len(missing)} target(s) are not files, e.g. {missing[0][:100]!r}.",
              file=sys.stderr)
        return 2

    removed, added, nnew = set(), set(), 0
    for t in targets:
        b = base_names(base, t)
        if b is None:
            nnew += 1; continue
        h = names(t)
        removed |= b - h
        added |= h - b

    # Pair each rooting: `TauCeti.X.y` removed <-> `X.y` added. What is left is the residue.
    paired, explained = 0, set()
    for r in sorted(removed):
        if not r.startswith('TauCeti.'):
            continue
        rooted = r[len('TauCeti.'):]
        if rooted in added:
            added.discard(rooted)
            explained.add(r)
            paired += 1
    # A DE-ROOTING: `TauCeti.NS.y` out, `TauCeti.y` in -- the same rename in reverse (r606).
    derooted = []
    for r in sorted(removed - explained):
        if not r.startswith('TauCeti.'):
            continue
        tail = r[len('TauCeti.'):]
        if '.' not in tail:
            continue                                   # already at the top of `TauCeti`
        short = tail.rsplit('.', 1)[1]
        cand = f"TauCeti.{short}"
        if cand in added:
            added.discard(cand)
            explained.add(r)
            derooted.append((r, cand))

    residue_removed = sorted(removed - explained)
    residue_added = sorted(added)

    for old_n, new_n in derooted:
        print(f"DE-ROOTED `{old_n}` -> `{new_n}`: a namespace level was dropped, not added")
    for n in residue_removed:
        print(f"VANISHED  `{n}` was declared here and is not any more, and no rooting explains it")
    for n in residue_added:
        print(f"APPEARED  `{n}` is declared here and was not, and no rooting explains it")
    print(f"# FIRING CONTROL: {len(targets)} file(s), {nnew} new; {paired} declaration(s) rooted "
          f"`TauCeti.X.y` -> `X.y` as intended; {len(derooted)} DE-ROOTED the other way "
          f"(`TauCeti.NS.y` -> `TauCeti.y`, r606 -- legitimate when review asks a PR to root less, "
          f"but state it in the body); {len(residue_removed)} VANISHED and "
          f"{len(residue_added)} APPEARED unexplained. A clean rooting leaves NO residue -- r563's "
          f"would have shown one of each (`HomotopyGroup.map_injective` gone, "
          f"`HomotopyGroup.IsCoveringMap.map_injective` arrived).", file=sys.stderr)
    return 1 if (residue_removed or residue_added or derooted) else 0

if __name__ == '__main__':
    sys.exit(main())
