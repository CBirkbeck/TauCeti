#!/usr/bin/env python3
"""siblingscan.py <file.lean> <namespace> -- would deleting this wrapper break a short reference?

THE r389 HAZARD, learned from a RED BUILD, and #5854 shipped five blocks without it and CI
rejected three.  Inside `namespace Foo`, a declaration written `_root_.Foo.bar` is reachable from a
later sibling as plain `bar`.  Delete the wrapper and those short references stop resolving:
`unknown identifier bar`.  So a wrapper may only be removed when NO declaration in the block refers
to a sibling by short name.

This wraps `vacuousns.short_sibling_refs` -- the same function, the same masking of comments and
backticks, the same r437 fix (it used to skip the whole declaration LINE, hiding a one-line term
body or a binder type).  It exists so `prepush.sh` can run the check on the block a PR is about to
unwrap, instead of the check living only inside a screen nobody remembers to run by hand -- which
is how r491, r493, r498, r499 and r503 all reached a reviewer.

Run it on the HEAD version, after rooting: the question is whether the ROOTED declarations are
still referred to by short name from inside the block.
"""
import sys, os, re, importlib.util

spec = importlib.util.spec_from_file_location(
    "vns", os.path.join(os.path.dirname(os.path.abspath(__file__)), "vacuousns.py"))
vns = importlib.util.module_from_spec(spec)
spec.loader.exec_module(vns)

def main():
    path, name = sys.argv[1], sys.argv[2]
    lines = open(path, encoding="utf-8").read().split("\n")
    # The block may be `namespace X`, or already replaced by `section` -- in which case the caller
    # is asking about the region that USED to be the wrapper.  Take the widest `section`/`namespace`
    # span that contains `_root_.<name>.` declarations.
    rooted = [i for i, L in enumerate(lines, 1)
              if re.match(r'^\s*(?:@\[[^\]]*\]\s*)?'
                          r'(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+)*'
                          r'(?:theorem|lemma|def|abbrev|instance|structure|class)\s+_root_\.'
                          + re.escape(name) + r'\.', L)]
    if not rooted:
        print(f"# FIRING CONTROL: no `_root_.{name}.` declaration in {os.path.basename(path)} -- "
              f"nothing to scan. If the file WAS rooted, the declaration pattern missed it: five "
              f"anchors have silently returned zero (r458/r481/r487/r490/r494).", file=sys.stderr)
        return 0
    s, e = min(rooted), max(rooted)
    # widen to the enclosing block so later siblings are seen
    while s > 1 and not re.match(r'^(namespace |section)', lines[s - 2]):
        s -= 1
    while e < len(lines) and not re.match(r'^end\b', lines[e]):
        e += 1
    hits = sorted(vns.short_sibling_refs(lines, s, e, wrapper=name))
    for h in hits:
        print(f"LOAD-BEARING  `{h}` is referenced by SHORT NAME inside the block\n"
              f"              qualify it as `{name}.{h}` before the wrapper goes")
    print(f"# FIRING CONTROL: {len(rooted)} `_root_.{name}.` declaration(s) in lines {s}-{e}; "
          f"{len(hits)} referenced by short name from inside the block. Comments and backticks are "
          f"masked (r389: a docstring naming a sibling is prose, and counting it excluded two "
          f"blocks #5838 had already merged green). #5953 had FOUR such references, two of them in "
          f"theorem STATEMENTS.", file=sys.stderr)
    return 1 if hits else 0

if __name__ == "__main__":
    sys.exit(main())
