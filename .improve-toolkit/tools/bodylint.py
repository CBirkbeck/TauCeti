#!/usr/bin/env python3
"""bodylint.py <pr> [<pr>...] -- re-measure the `N → M` lint claims in a PR body.

r509 and r510 found PR bodies carrying claims that were true at the first push and false three
commits later -- #5950 still said a declaration was *"untouched"* after r499 rooted it, and #5959
still opened with the exact sentence `documentation` had blocked on, fixed in the module docstring
two commits earlier.  r504 concluded that prose claims are not mechanically checkable.  **The
numbers are**, and every body this lane writes carries one.

A body's `lint-dot-notation: N → M` is a claim about a delta against the branch's MERGE BASE.  It
goes stale two ways: the branch gains commits that change the count, or -- the r518 trap -- it is
compared against the tip of main rather than the merge base, which reads backwards for a branch that
is behind.  Both are silent: no rubric re-reads the body's arithmetic.

Reports MISMATCH with both numbers, or `no claim` when a body states none.  It re-measures from the
worktree, so run it from the worktree root.
"""
import re, subprocess, sys, tempfile, shutil, os

# Anchored on EITHER side: the claim is written both as `lint-dot-notation: 985 → 981` and as
# `999 → 991 findings` (#5950).  The first pattern here missed the second form on its very first
# real run -- the same too-narrow-anchor family as r458/r481/r487/r490/r494/r511, in a tool written
# to catch stale claims.  Requiring one of the two words keeps a bare `N → M` from matching prose.
ARROW = re.compile(r'(?:lint-dot-notation[`\s:*]*|)(?<![\d.])([0-9]{2,5})\s*(?:\*\*)?\s*'
                   r'(?:→|->|to)\s*(?:\*\*)?\s*([0-9]{2,5})(?![\d.])'
                   r'(?=[^\n]{0,40}(?:findings|, 0 new|new)|)')

def sh(*a):
    return subprocess.run(a, capture_output=True, text=True).stdout.strip()

def count(rev):
    d = tempfile.mkdtemp()
    try:
        tar = subprocess.Popen(["git", "archive", rev, "TauCeti"], stdout=subprocess.PIPE)
        subprocess.run(["tar", "-x", "-C", d], stdin=tar.stdout, check=True)
        tar.wait()
        out = sh("python3", "scripts/lint-dot-notation.py", "--source-root", os.path.join(d, "TauCeti"))
        m = re.search(r'(\d+) total', out)
        return int(m.group(1)) if m else None
    finally:
        shutil.rmtree(d, ignore_errors=True)

def main():
    # `--claim <file>` extracts the claim from a body on disk and stops.  It exists so the anchor
    # can be controlled WITHOUT the network: the anchor is the part that failed on run one, and a
    # tool validated only against live PRs is validated only against the phrasings live PRs happen
    # to use today (r514).
    if len(sys.argv) > 2 and sys.argv[1] == "--claim":
        for f in sys.argv[2:]:
            m = ARROW.search(open(f, encoding="utf-8").read())
            print(f"{os.path.basename(f)}: " + (f"claim {m.group(1)} -> {m.group(2)}" if m
                                                else "NO CLAIM FOUND"))
        return 0
    bad = 0
    for pr in sys.argv[1:]:
        body = sh("gh", "pr", "view", pr, "--repo", "TauCetiProject/TauCeti", "--json", "body",
                  "--jq", ".body")
        head = sh("gh", "pr", "view", pr, "--repo", "TauCetiProject/TauCeti", "--json",
                  "headRefOid", "--jq", ".headRefOid")
        m = ARROW.search(body)
        if not m:
            print(f"#{pr}: no lint claim in the body")
            continue
        claimed = (int(m.group(1)), int(m.group(2)))
        subprocess.run(["git", "fetch", "fork", head, "-q"], capture_output=True)
        mb = sh("git", "merge-base", "origin/main", head)
        actual = (count(mb), count(head))
        ok = actual == claimed
        bad += not ok
        print(f"#{pr}: body says {claimed[0]} → {claimed[1]}; "
              f"merge base {mb[:10]} measures {actual[0]} → {actual[1]}  "
              f"{'ok' if ok else '<- MISMATCH'}")
    print(f"# FIRING CONTROL: {len(sys.argv) - 1} PR(s) checked, {bad} mismatch(es). The delta is "
          f"against the MERGE BASE, not the tip of main -- comparing to the tip reads BACKWARDS for "
          f"a branch behind main (r518: 983 -> 984 for a PR that removes one). Prose claims stay "
          f"unmechanised (r504); this covers the arithmetic, which every body in this lane carries.",
          file=sys.stderr)
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
