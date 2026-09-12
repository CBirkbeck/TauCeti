#!/usr/bin/env python3
"""tracepatch.py <lake-packages-dir> [--apply]

For every `<module>.trace.nobuild` diagnostic that `lake build … --no-build` left beside a
cached `<module>.trace`, adopt the *computed* depHash into the stored trace so Lake accepts the
cached artifacts as up to date.

ONLY sound when the cached artifacts are what a rebuild would produce. Establish that first by
rebuilding one stale leaf for real and `cmp`-ing every artifact (olean, olean.private,
olean.server, ilean) against the cached copy — round 119 did this for `Batteries.Logic` and
`Mathlib.Tactic.Linter.Header`. Without --apply it only reports what it would change.
A `.trace.orig` backup is written next to every patched trace.
"""
import json, os, sys, glob

root = sys.argv[1]
apply = '--apply' in sys.argv
patched = skipped = 0
for nb in glob.glob(os.path.join(root, '**', '*.trace.nobuild'), recursive=True):
    tr = nb[:-len('.nobuild')]
    if not os.path.exists(tr):
        skipped += 1; continue
    computed = json.load(open(nb))['depHash']
    stored = json.load(open(tr))
    if stored.get('depHash') == computed:
        continue
    if not stored.get('outputs'):
        skipped += 1; continue          # no cached outputs recorded: a real rebuild is needed
    if apply:
        if not os.path.exists(tr + '.orig'):
            os.replace(tr, tr + '.orig')
        stored['depHash'] = computed
        with open(tr, 'w') as f:
            json.dump(stored, f, separators=(',', ':'))
    patched += 1
print(f"{'patched' if apply else 'would patch'} {patched} traces; skipped {skipped}")
