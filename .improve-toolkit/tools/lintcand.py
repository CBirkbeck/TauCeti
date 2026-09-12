#!/usr/bin/env python3
"""lintcand.py <baseline.tsv> <snapshot> -- rank `lint-dot-notation` rows as rooting candidates.

WHY NAMESPACE-AWARE (r439).  The obvious way to locate a flagged declaration is to regex its short
name:

    re.search(r"\\b(theorem|lemma|def)\\s+" + short + r"\\b", line)

That is wrong whenever a file declares the same short name in two namespaces, which is common:
`Geometry/Symplectic/JHolomorphic/Line.lean` holds BOTH
`TauCeti.LinearMap.apply_stdComplexLine` (line 110, written `lemma LinearMap.apply_stdComplexLine`)
and `TauCeti.IsComplexLinearMap.apply_stdComplexLine` (line 188, written `lemma
apply_stdComplexLine` inside `namespace IsComplexLinearMap`).  The regex finds the SECOND -- the one
that is not flagged -- so the reported width and the "no unqualified references" verdict both
describe the wrong declaration.  Caught only because the docstring named a different namespace than
the finding did.

So: track the `namespace` stack, build each declaration's fully-qualified name, and match THAT
against the flagged name.  A declaration header may itself be dotted (`lemma LinearMap.foo` inside
`namespace TauCeti`), so the qualified name is the stack joined with the header's own dotted text.

Prints a firing control (r184): a screen that can return zero must say whether it fired.
"""
import json, os, re, sys

NS = re.compile(r'^\s*namespace\s+(\S+)\s*$')
END = re.compile(r'^\s*end\s+(\S+)\s*$')
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?'
                  r'(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+)*'
                  r'(?:theorem|lemma|def|abbrev|instance)\s+'
                  r'([^\W\d][\w.\'!?]*)')

def decl_line(lines, want):
    """Line index of the declaration whose FULLY-QUALIFIED name is `want`, else None."""
    stack, incomment = [], 0
    for i, l in enumerate(lines):
        o, c = l.count('/-'), l.count('-/')
        was = incomment
        incomment = max(0, incomment + o - c)
        if was or o > c:
            continue
        m = NS.match(l)
        if m:
            stack.append(m.group(1)); continue
        m = END.match(l)
        if m and stack and stack[-1] == m.group(1):
            stack.pop(); continue
        m = DECL.match(l)
        if m and ".".join(stack + [m.group(1)]) == want:
            return i
    return None

def main():
    base, snap = sys.argv[1], sys.argv[2]
    rows = [l.rstrip("\n").split("\t") for l in open(base) if l.strip()]
    # HOW MANY FLAGGED DECLARATIONS SHARE THIS NAMESPACE, TREE-WIDE (r466).  The single-finding-file
    # filter selects declarations isolated in their FILE, which is not the same as isolated in their
    # NAMESPACE.  `TauCeti.IsCoveringMap` carries ~60 flagged members across 9 files; exactly one of
    # them sits alone in its file, so it surfaces as a "clean" candidate.  Rooting 1 of 60 has no
    # answer to "why only this one?" -- the objection that cost #5905 three blocks.  Count the
    # namespace across the WHOLE baseline, not the file.
    ns_total = {}
    for _p, _n in rows:
        for full in json.loads(_n):
            if not full.startswith("TauCeti."):
                continue
            _ns = full[len("TauCeti."):].rsplit(".", 1)[0]
            ns_total[_ns] = ns_total.get(_ns, 0) + 1
    seen = found = 0
    out = []
    for p, njson in rows:
        names = json.loads(njson)
        if len(names) != 1:
            continue
        seen += 1
        want = names[0]
        short = want.rsplit(".", 1)[-1]
        ns = want[len("TauCeti."):].rsplit(".", 1)[0] if want.startswith("TauCeti.") else ""
        fp = p if os.path.isabs(p) else os.path.join(snap, p)
        try:
            lines = open(fp, encoding="utf-8").read().split("\n")
        except Exception:
            continue
        dl = decl_line(lines, want)
        if dl is None:
            continue
        found += 1
        # Width must count the WHOLE replacement, not just `_root_.` (r439).  A header written
        # bare inside `namespace Matrix` becomes `_root_.Matrix.det_mul_intCast` -- 14 added
        # characters, not 7.  Only an already-dotted header (`lemma LinearMap.foo` sitting
        # directly in `namespace TauCeti`) costs the bare 7.
        header = DECL.match(lines[dl]).group(1)
        target = want[len("TauCeti."):] if want.startswith("TauCeti.") else want
        width = len(lines[dl]) + len("_root_." + target) - len(header)
        # references that would have to change: bare short-name uses that are NOT dot-notation
        bare = [i + 1 for i, l in enumerate(lines) if i != dl and
                re.search(r'(?<![\w.])' + re.escape(short) + r'(?!\w)',
                          re.sub(r'`[^`]*`', '', re.sub(r'--.*$', '', l)))]
        out.append((width, len(bare), ns, short, p.replace(snap + "/", ""), dl + 1, bare[:4]))
    # `bare` counts UNQUALIFIED uses only.  A call site may still name the declaration in full as
    # `TauCeti.<ns>.<short>` -- that path disappears when the declaration is rooted, so those sites
    # MUST be rewritten too.  #5913's predecessor had bare=0 and two fully-qualified callers (r457).
    # One pass over the tree counts them for every candidate at once.
    wanted = {}
    for w, nb, ns, short, p_, ln, bare in out:
        wanted.setdefault("TauCeti." + ns + "." + short, []).append(short)
    qual = {k: 0 for k in wanted}
    for dp, _, fs in os.walk(snap):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            try:
                txt = open(os.path.join(dp, f), encoding="utf-8").read()
            except Exception:
                continue
            for k in qual:
                if k in txt:
                    qual[k] += txt.count(k)
    out = [(w, nb, ns, short, p_, ln, bare,
            max(0, qual.get("TauCeti." + ns + "." + short, 0)),
            ns_total.get(ns, 1))
           for (w, nb, ns, short, p_, ln, bare) in out]
    # rank by namespace isolation FIRST: a lone member of its namespace is the defensible target
    out.sort(key=lambda r: (r[8], r[1], r[0]))
    for w, nb, ns, short, p, ln, bare, nq, nsn in out:
        flag = "OK  " if (w <= 100 and nb == 0 and nsn == 1) else "    "
        # `qual` counts `TauCeti.<ns>.<short>` occurrences INCLUDING the module-doc bullet and any
        # declaration line, so it is an upper bound on call sites, not an exact count.
        print(f"{flag}w={w:3d} bare={nb:2d} qual={nq:2d} nsflag={nsn:3d} {ns:22s} {short[:30]:30s} {p}:{ln}"
              + (f"  bare@{bare}" if bare else ""))
    print(f"# FIRING CONTROL: {len(rows)} baseline rows, {seen} single-finding files, "
          f"{found} declarations located namespace-aware; "
          f"{sum(1 for r in out if r[0] <= 100 and r[1] == 0 and r[8] == 1)} clean candidates "
          f"(width <= 100 after `_root_.`, no bare short-name reference); "
          f"`qual` counts fully-qualified `TauCeti.<ns>.<short>` uses, which MUST be rewritten "
          f"when the declaration is rooted; `nsflag` is how many flagged declarations share the "
          f"namespace TREE-WIDE -- only nsflag=1 is marked OK.", file=sys.stderr)

if __name__ == "__main__":
    main()
