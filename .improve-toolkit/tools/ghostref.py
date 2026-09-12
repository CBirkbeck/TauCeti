#!/usr/bin/env python3
"""ghostref.py --base <ref> <repo-root> <mathlib-root> <changed.lean>... -- short references that
main still spells to a declaration this PR removed.

THE r679 RED BUILD, #6093.  The PR generalised `TauCeti.IsCoveringMap.fiberMap` into
`Function.fiberMap`.  Merging 354 commits of `main` was textually CLEAN -- and the build failed in
`Classification/FiberFunctor.lean`, a file the PR does not touch, which arrived on main in #6023 and
writes, inside `namespace TauCeti.CoveringSpace`:

    IsCoveringMap.fiberMap f.hom.left.hom (proj_hom_comp_hom_left_hom f) x0

AND IT DID NOT SAY `unknown identifier`.  `IsCoveringMap` is itself a TERM of function type, so once
`TauCeti.IsCoveringMap.fiberMap` was gone the reference silently re-read as GENERALIZED FIELD
NOTATION -- `Function.fiberMap IsCoveringMap ..` -- and surfaced as an application type mismatch far
from its cause.  **A removed declaration whose namespace is also a term does not announce its
absence.**

WHY THE TWO NEIGHBOURING SCREENS BOTH MISS IT:

  * `stalequal` walks the whole repository, but matches the FULL dead path `TauCeti.A.b`, and its
    substring prefilter keys on `TauCeti`.  The reference here is spelled SHORT -- `A.b` -- because
    the r389 rule resolves it from inside `namespace TauCeti.*`.  No `TauCeti` on the line, so the
    prefilter drops it before any regex runs.
  * `deadpath` resolves qualified names properly, but only in the files THIS PR CHANGED.  The stale
    reference lives in a file the PR never touched.

So the gap is exactly: SHORT references, in UNCHANGED files, to names this PR removed.  It can only
appear after `main` moves, because main is what supplies the new caller -- which is why r679's gate
read identical before and after the merge (`11 ok, 4 failed` both sides) while the build went red.
*Identical gate counts prove the merge introduced nothing; they do NOT make the standing findings
safe.*  A latent `nsjump` finding is one that is waiting for a caller.

SUPPRESSION.  A short `A.b` is only a ghost if nothing declares it any more.  Checked against the
repository at HEAD (root-level declarations) and against Mathlib, because `TauCeti.Set.foo` going
away is no problem at all when Mathlib's own `Set.foo` is what the reference meant.
"""
import sys, os, re, subprocess, tempfile, importlib.util

HERE = os.path.dirname(os.path.abspath(__file__))
def _load(n):
    s = importlib.util.spec_from_file_location(n, os.path.join(HERE, n + ".py"))
    m = importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
nss = _load("nsslice")
dp = _load("deadpath")


def full_names(path):
    out = set()
    for ns, short, _rooted in nss.walk(path):
        out.add(f"{ns}.{short}" if ns else short)
    return out


def short_forms(gone):
    """The short spelling each removed `TauCeti.A.b` was reachable by, per the r389 rule.

    Inside `namespace TauCeti.X` Lean tries `TauCeti.X.A.b`, then `TauCeti.A.b`, then root `A.b`.
    So `TauCeti.A.b` answers to a bare `A.b` anywhere under `namespace TauCeti`.  A name with
    nothing after the `TauCeti.` prefix has no such short form and is left to `stalequal`.
    """
    out = {}
    for n in gone:
        if n.startswith("TauCeti.") and n.count(".") >= 2:
            out[n[len("TauCeti."):]] = n
    return out


def declared_somewhere(short, root, mathlib):
    """Does `short` still name a declaration -- at root in the repo, or in Mathlib?"""
    tail = short.split(".")[-1]
    for base in (root, mathlib):
        if not base or not os.path.isdir(base):
            continue
        hits = subprocess.run(["grep", "-rl", "--include=*.lean", tail, base],
                              capture_output=True, text=True).stdout.split()
        for f in hits:
            try:
                if short in full_names(f):
                    return True
            except Exception:
                continue
    return False


def main():
    a = sys.argv[1:]
    base = None
    if a and a[0] == "--base":
        base = a[1]; a = a[2:]
    if len(a) < 3:
        print(__doc__.strip().split("\n")[0], file=sys.stderr); return 2
    root, mathlib, targets = a[0], a[1], a[2:]
    if not base:
        print("# UNRUN: ghostref needs --base; the removed set is a diff, not a property of HEAD.",
              file=sys.stderr)
        return 0
    if not os.path.isdir(os.path.join(root, "TauCeti")):
        print(f"ghostref: {root} has no TauCeti/ directory -- give the REPOSITORY ROOT (r493).",
              file=sys.stderr)
        return 2

    gone = set()
    for t in targets:
        r = subprocess.run(["git", "show", f"{base}:{t}"], capture_output=True, text=True)
        if r.returncode:
            continue                                      # new file: nothing could be stale
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tf:
            tf.write(r.stdout); tmp = tf.name
        try:
            gone |= full_names(tmp) - (full_names(t) if os.path.exists(t) else set())
        finally:
            os.unlink(tmp)

    cand = short_forms(gone)
    if not cand:
        print(f"# FIRING CONTROL: {len(gone)} declaration(s) removed, none of them under a "
              f"`TauCeti.<ns>.` path with a short form; nothing for ghostref to chase.",
              file=sys.stderr)
        return 0
    live = {s for s in cand if declared_somewhere(s, root, mathlib)}
    chase = {s: f for s, f in cand.items() if s not in live}
    if not chase:
        print(f"# FIRING CONTROL: all {len(cand)} short form(s) still resolve (repo root or "
              f"Mathlib); nothing is a ghost.", file=sys.stderr)
        return 0

    heads = {s.split(".")[0] for s in chase}
    nhit, nfiles = 0, 0
    for dpath, _, fs in os.walk(root):
        if os.sep + ".lake" in dpath or os.sep + ".git" in dpath:
            continue
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dpath, f)
            nfiles += 1
            try:
                raw = open(p, encoding="utf-8").read()
            except Exception:
                continue
            if "namespace TauCeti" not in raw:
                continue                                  # r389 short form is unreachable here
            if not any(h in raw for h in heads):
                continue
            for i, code in dp.code_lines(raw.split("\n")):
                for s in chase:
                    if s not in code:
                        continue
                    if re.search(r"(?<![\w.])" + re.escape(s) + r"(?![\w.'])", code):
                        nhit += 1
                        print(f"GHOST  {s}  (was {chase[s]}, removed by this PR)\n"
                              f"       {os.path.relpath(p, root)}:{i}\n"
                              f"       | {code.strip()[:100]}")
    print(f"# FIRING CONTROL: {len(gone)} removed, {len(cand)} with a short form, "
          f"{len(live)} still resolving, {len(chase)} chased across {nfiles} file(s); "
          f"{nhit} ghost reference(s). A removed declaration under a namespace that is ALSO a term "
          f"re-reads as generalized field notation instead of erroring (#6093).", file=sys.stderr)
    return 1 if nhit else 0


if __name__ == "__main__":
    sys.exit(main())
