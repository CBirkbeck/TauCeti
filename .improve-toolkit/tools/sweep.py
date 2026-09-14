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


LIST_LIMIT = 1000


def pr_list_cmd(limit=LIST_LIMIT):
    """The open-PR listing, with the repo and a generous limit both EXPLICIT (r691).

    The sweep printed NOTHING -- no rows, no error, exit 0 -- because it listed open PRs across the
    whole repository with `--limit 100`.  The repo carries well over a hundred open PRs from other
    lanes, and `gh pr list` returns newest first, so the long-lived `improve/*` PRs (#6093, #5950)
    were exactly the rows cut off.  An empty sweep reads like an empty board, which is the most
    misleading thing this tool can print.  Same failure as `queuepos.py` in r680, one tool over.
    """
    return ["pr", "list", "--repo", REPO, "--state", "open", "--limit", str(limit), "--json",
            "number,headRefName,isDraft,labels,headRefOid,title"]


class ApiError(Exception):
    """A `gh` read that returned no usable data (r722)."""


def api_pages(text, what):
    """Decode `gh api [--paginate]` stdout into its JSON pages, refusing error payloads (r722).

    At 17:16Z on 09-14 the REST quota was exhausted mid-round and `issues/<n>/comments` answered
    `{"message": "API rate limit exceeded ..."}`.  The sweep iterated that dict's KEYS as if they were
    comments and died with `'str' object has no attribute 'get'`; the check-runs read would have
    turned the same payload into `CI=NO-RUNS` without a word.  An unreadable field must say so, never
    look like an empty one.  `--paginate` without `--slurp` also concatenates pages (`[..][..]`), which
    one `json.loads` cannot read, so every page is decoded.
    """
    dec, pages, i, text = json.JSONDecoder(), [], 0, (text or "").strip()
    if not text:
        raise ApiError(f"{what}: empty response")
    while i < len(text):
        try:
            obj, i = dec.raw_decode(text, i)
        except json.JSONDecodeError as err:
            raise ApiError(f"{what}: unreadable JSON ({err.msg})")
        pages.append(obj)
        while i < len(text) and text[i].isspace():
            i += 1
    for pg in pages:
        if isinstance(pg, dict) and "message" in pg and "check_runs" not in pg:
            raise ApiError(f"{what}: {str(pg['message'])[:90]}")
    return pages


def api_list(text, what):
    """The items of a list endpoint, across every page."""
    out = []
    for pg in api_pages(text, what):
        if not isinstance(pg, list):
            raise ApiError(f"{what}: expected a list, got {type(pg).__name__}")
        out.extend(pg)
    return out


def api_check_runs(text, what):
    """The `check_runs` of a check-runs endpoint, across every page."""
    out = []
    for pg in api_pages(text, what):
        if not isinstance(pg, dict) or not isinstance(pg.get("check_runs"), list):
            raise ApiError(f"{what}: no check_runs in the response")
        out.extend(pg["check_runs"])
    return out


def main():
    failures = 0
    try:
        rows = api_list(gh(*pr_list_cmd()), "open-PR listing")
    except ApiError as err:
        print(f"# API ERROR: {err} -- no sweep. An unreadable listing is not an empty board.",
              file=sys.stderr)
        return 2
    if len(rows) >= LIST_LIMIT:
        print(f"# WARNING: the open-PR listing hit its {LIST_LIMIT}-row limit; raise it.",
              file=sys.stderr)
    prs = [p for p in rows if p["headRefName"].startswith("improve/")]
    if not prs:
        print(f"# FIRING CONTROL: {len(rows)} open PRs listed, none on an improve/* branch.",
              file=sys.stderr)
    prs.sort(key=lambda p: p["number"])
    now = datetime.datetime.now(datetime.timezone.utc)
    for p in prs:
        n, head = p["number"], p["headRefOid"]
        lab = ",".join(x["name"] for x in p["labels"] if x["name"] != "roadmap/none") or "-"
        try:
            ci = ci_verdict(api_check_runs(
                gh("api", f"repos/{REPO}/commits/{head}/check-runs", "--paginate"), f"#{n} check-runs"))
        except ApiError as err:
            ci = "API-ERROR"
            failures += 1
            print(f"# API ERROR: {err}", file=sys.stderr)
        try:
            cm = api_list(gh("api", f"repos/{REPO}/issues/{n}/comments", "--paginate"), f"#{n} comments")
        except ApiError as err:
            cm = None
            failures += 1
            print(f"# API ERROR: {err}", file=sys.stderr)
        if cm is None:
            bd = "API-ERROR (board unknown)"
        else:
            boards = [c for c in cm if "tauceti-meta:v1" in (c.get("body") or "")]
            boards.sort(key=lambda c: c["updated_at"])      # the pipeline EDITS; last-updated wins
            if boards:
                b = boards[-1]
                m = re.search(r'head_sha["\s:=]+([0-9a-f]{7,40})', b["body"])
                bsha = m.group(1) if m else "?"
                state = "ON-HEAD" if bsha and head.startswith(bsha[:10]) else "BEHIND"
                bd = f"{bsha[:10]} {state} upd={b['updated_at']}"
            else:
                bd = "NO BOARD"
        try:
            tl = api_list(gh("api", f"repos/{REPO}/issues/{n}/timeline", "--paginate"), f"#{n} timeline")
            rfr = [e["created_at"] for e in tl if e.get("event") == "ready_for_review"]
        except ApiError as err:
            rfr = None
            failures += 1
            print(f"# API ERROR: {err}", file=sys.stderr)
        age = ""
        if rfr:
            t = datetime.datetime.fromisoformat(rfr[-1].replace("Z", "+00:00"))
            age = f" ({(now - t).total_seconds() / 60:.0f}m ago)"
        shown = "API-ERROR" if rfr is None else (rfr[-1] if rfr else "-")
        print(f"#{n}  draft={str(p['isDraft']):5s} label={lab:16s} CI={ci:22s} board={bd}")
        print(f"      head={head[:10]}  ready_for_review={shown}{age}")
        print(f"      {p['title'][:96]}")
    if failures:
        print(f"# {failures} field(s) unreadable -- rerun the sweep before acting on this board.",
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
