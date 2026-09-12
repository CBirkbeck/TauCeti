#!/usr/bin/env python3
"""sweep.py -- the four-field board sweep: label | CI | board head_sha | isDraft.

WHY FOUR FIELDS.  r650 lost 64 minutes on #6412: it sat green with no scoreboard because it was
still a DRAFT, while its label read `awaiting-review` the whole time.  *A label says what is
wanted, not what is reachable.*  So `isDraft` is swept beside the label, never inferred from it.

TWO DEFECTS THIS ENCODES, both found the hard way:

1.  A SUPERSEDED RUN IS NOT A RED BUILD (r653).  A commit's check-runs list carries EVERY run ever
    created for that SHA, including ones a re-dispatch cancelled.  The first version of this sweep
    reported #6188 as `RED:label` because a duplicate `label` job had been cancelled, while
    `sandboxed-build` was green and nothing had conclusion `failure` at all.  Judge each check by
    its LATEST run per name -- `ci_verdict` below -- and treat a cancelled latest run as suspect
    rather than as failure.

2.  THE PIPELINE *EDITS* ITS SCOREBOARD COMMENT (handover §3, and r655 the hard way).  The board is
    one comment that is rewritten in place, so the positionally-last comment is stale and the same
    comment id can carry a completely different finding an hour later.  Sort by `updated_at` and
    read the last.  `head_sha` from its `tauceti-meta:v1` payload is then compared to the PR head:
    BEHIND means the fix is already pushed, so do NOT re-fix.

The drive clock (step 4) is `max(CI-green, ready_for_review)`, not CI-green alone (r651), so the
`ready_for_review` timestamp is printed with its age.  Measured reviewable -> first board across
this watch: 32-67 min.  Driving inside that band reproduces a board the pipeline was about to post.
"""
import json, subprocess, sys, datetime, re

REPO = "TauCetiProject/TauCeti"


def gh(*a):
    return subprocess.run(["gh"] + list(a), capture_output=True, text=True).stdout


def ci_verdict(runs):
    """GREEN / RED:… / PENDING:… / NO-RUNS, judging each check by its LATEST run per name.

    Pure so the controls can exercise it on fixture data without touching the network.
    """
    latest = {}
    for r in runs:
        k = r["name"]
        stamp = r.get("started_at") or ""
        if k not in latest or stamp >= latest[k][0]:
            latest[k] = (stamp, r)
    runs = [r for _s, r in latest.values()]
    if not runs:
        return "NO-RUNS"
    bad = [r["name"] for r in runs if r.get("conclusion") in ("failure", "timed_out",
                                                             "action_required")]
    pend = [r["name"] for r in runs if r.get("status") != "completed"]
    canc = [r["name"] for r in runs if r.get("conclusion") == "cancelled"]
    if bad:
        return "RED:" + ",".join(sorted(bad))
    if pend:
        return "PENDING:" + ",".join(sorted(pend))
    if canc:
        return "RED:" + ",".join("cancelled:" + c for c in sorted(canc))
    return "GREEN"


def main():
    prs = json.loads(gh("pr", "list", "--state", "open", "--limit", "100", "--json",
                        "number,headRefName,isDraft,labels,headRefOid,title"))
    prs = [p for p in prs if p["headRefName"].startswith("improve/")]
    prs.sort(key=lambda p: p["number"])
    now = datetime.datetime.now(datetime.timezone.utc)
    for p in prs:
        n, head = p["number"], p["headRefOid"]
        lab = ",".join(x["name"] for x in p["labels"] if x["name"] != "roadmap/none") or "-"
        cr = json.loads(gh("api", f"repos/{REPO}/commits/{head}/check-runs", "--paginate"))
        ci = ci_verdict(cr.get("check_runs", []))
        cm = json.loads(gh("api", f"repos/{REPO}/issues/{n}/comments", "--paginate"))
        boards = [c for c in cm if "tauceti-meta:v1" in (c.get("body") or "")]
        boards.sort(key=lambda c: c["updated_at"])          # the pipeline EDITS; last-updated wins
        if boards:
            b = boards[-1]
            m = re.search(r'head_sha["\s:=]+([0-9a-f]{7,40})', b["body"])
            bsha = m.group(1) if m else "?"
            state = "ON-HEAD" if bsha and head.startswith(bsha[:10]) else "BEHIND"
            bd = f"{bsha[:10]} {state} upd={b['updated_at']}"
        else:
            bd = "NO BOARD"
        tl = json.loads(gh("api", f"repos/{REPO}/issues/{n}/timeline", "--paginate"))
        rfr = [e["created_at"] for e in tl if e.get("event") == "ready_for_review"]
        age = ""
        if rfr:
            t = datetime.datetime.fromisoformat(rfr[-1].replace("Z", "+00:00"))
            age = f" ({(now - t).total_seconds() / 60:.0f}m ago)"
        print(f"#{n}  draft={str(p['isDraft']):5s} label={lab:16s} CI={ci:22s} board={bd}")
        print(f"      head={head[:10]}  ready_for_review={rfr[-1] if rfr else '-'}{age}")
        print(f"      {p['title'][:96]}")


if __name__ == "__main__":
    main()
