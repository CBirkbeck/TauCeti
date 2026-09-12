#!/usr/bin/env python3
"""minecount.py [--repo R] [--session S] -- how many improve/* PRs have merged, and how many are MINE.

WHY THIS EXISTS (r432).  Every merged-count in this ledger before r432 was WRONG, and wrong in a
way that hid itself for ~200 rounds:

    gh pr list --state merged --limit N --json headRefName | select(startswith("improve/")) | length

`--limit N` does NOT mean "the N most recently merged".  It means "fetch N PRs in whatever order
the API returns them, THEN filter".  So the count grows monotonically with the limit and is a
property of N, not of the repo:

    --limit  200 ->  26          --limit 1000 ->  90
    --limit  500 ->  47          --limit 4000 -> 102   (true value)

r378 saw this as a symptom -- "the merged count went 29 -> 28" -- and "fixed" it by raising the
limit from 200 to 500.  That did not fix anything; it moved the artifact to a new plateau, where
it sat looking stable.  A number that only ever drifts UPWARD when you look harder is not a count.

Two independent methods must agree before a total is trusted:
  1. fetch every merged PR (--limit 4000) and filter locally;
  2. the search API's `total_count` for `is:pr is:merged head:improve/`.
Both give 102.

ATTRIBUTION.  Every improve/* PR is authored by `CBirkbeck` -- that is the FORK account, shared by
every improver session, so `--author` cannot separate them.  The discriminator is the
`Claude-Session:` trailer this session writes into each commit message; the squash commit on main
carries it.  Of the 102, 36 are this session's and 66 belong to other sessions.

Report both numbers.  "102 merged" overclaims; "36 merged" understates the channel.
"""
import json, re, subprocess, sys, collections

REPO = "TauCetiProject/TauCeti"
MINE = "01TYwXN9WBAPasmBQXr6iQcp"
WT   = "/Users/mcu22seu/GitHub/TauCeti/.claude/worktrees/improver-1"

def sh(*a, **k):
    return subprocess.run(a, capture_output=True, text=True, **k).stdout

def main():
    argv = sys.argv[1:]
    repo = argv[argv.index("--repo")+1] if "--repo" in argv else REPO
    mine = argv[argv.index("--session")+1] if "--session" in argv else MINE

    prs = json.loads(sh("gh", "pr", "list", "--repo", repo, "--state", "merged",
                        "--limit", "4000", "--json", "number,headRefName,mergedAt") or "[]")
    imp = {p["number"]: p for p in prs if p["headRefName"].startswith("improve/")}

    # CROSS-CHECK against the search API.  If these disagree, the --limit is truncating again and
    # the local count is a floor, not a total -- say so rather than printing a confident number.
    sc = sh("gh", "api", "-X", "GET", "search/issues", "-f",
            f"q=repo:{repo} is:pr is:merged head:improve/", "--jq", ".total_count").strip()
    agree = sc.isdigit() and int(sc) == len(imp)

    log = sh("git", "log", "origin/main", "--since=2026-08-20", "--format=%s%x00%b%x00END", cwd=WT)
    ours, other = set(), set()
    for rec in log.split("\x00END\n"):
        p = rec.split("\x00")
        if len(p) < 2:
            continue
        m = re.search(r"\(#(\d+)\)\s*$", p[0].strip())
        if not m:
            continue
        n = int(m.group(1))
        if n in imp:
            (ours if mine in p[1] else other).add(n)

    print(f"improve/* merged, ALL sessions : {len(imp)}"
          f"   [search API says {sc}: {'AGREE' if agree else 'DISAGREE -- treat as a FLOOR'}]")
    print(f"  this session ({mine[:12]}…) : {len(ours)}")
    print(f"  other sessions               : {len(other)}")
    unmatched = len(imp) - len(ours) - len(other)
    if unmatched:
        print(f"  no squash commit matched     : {unmatched}  (branch merged, or subject lacks '(#N)')")
    if ours:
        print(f"  mine: #{min(ours)} … #{max(ours)}")
    if not agree:
        sys.exit(1)

if __name__ == "__main__":
    main()
