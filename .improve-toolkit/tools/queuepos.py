#!/usr/bin/env python3
"""queuepos.py -- the fifth field the sweep cannot see: merge-queue membership.

WHY.  r679 lost a PR in plain sight.  #6093 was enqueued at 15:43:28Z, sat 3h11m without ever
receiving a `merge_group` run, and was dropped by `github-merge-queue[bot]` at 18:54:20Z -- the
instant the PR ahead of it merged.  No comment was posted.  Afterwards it still read:

    label=ready-to-merge   CI=GREEN   board=ON-HEAD   isDraft=false   mergeable=MERGEABLE

Every field `sweep.py` reads said healthy.  The PR was stranded, because `tauceti-review-bot`
enqueues on the `ready-to-merge` LABEL TRANSITION, which had already happened -- so nothing was
ever going to put it back.  Only queue membership distinguished it from a PR merely waiting.

AND IT IS USUALLY JUST WAITING.  The queue is one serialised worker at ~25-30 min per merge, 30
deep in r679; merges are strictly FIFO by enqueue time.  A label->merge latency of 2.5-3.5h is
NORMAL.  r676 read that wait as a "jam" on an unrelated PR and was wrong; r679 then read it as
`improve/*` discrimination and was wrong again.  Both theories came from reasoning over run lists
and merge timestamps.  The queue's own state was one API call away.  *Query the queue; do not
model it.*

So the only actionable signal is STRANDED: labelled `ready-to-merge` and absent from the queue.
QUEUED at position 18 is not a problem, however long it has been there.
"""
import json, subprocess, sys

REPO = "TauCetiProject/TauCeti"

_Q = """{repository(owner:"%s",name:"%s"){mergeQueue(branch:"%s"){entries(first:100){
  totalCount nodes{position state enqueuedAt pullRequest{number}}}}}}"""


def queue_verdict(label, in_queue, position=None, state=None):
    """STRANDED / QUEUED:… / NOT-READY / MERGING, from label plus queue membership.

    Pure so the controls can exercise it on fixture data without touching the network.

    STRANDED is the ONLY actionable verdict: the bot enqueues on the label transition, so a PR
    that is `ready-to-merge` and out of the queue will never be re-enqueued on its own.  The fix
    is to refresh the branch against `main` and re-gate (r679), which makes the bot re-review and
    re-label, and the new transition re-enqueues it.
    """
    if label != "ready-to-merge":
        return "NOT-READY"
    if not in_queue:
        return "STRANDED"
    if state in ("AWAITING_CHECKS", "MERGEABLE"):
        return "MERGING:pos=%s" % position
    return "QUEUED:pos=%s" % position


def fetch(owner_repo=REPO, branch="main"):
    owner, name = owner_repo.split("/")
    out = subprocess.run(
        ["gh", "api", "graphql", "-f", "query=" + _Q % (owner, name, branch)],
        capture_output=True, text=True).stdout
    try:
        q = json.loads(out)["data"]["repository"]["mergeQueue"]
    except Exception:
        return None, {}
    if not q:
        return None, {}
    e = q["entries"]
    return e.get("totalCount"), {n["pullRequest"]["number"]: n for n in e["nodes"]}


def main(argv):
    prs = [int(a.lstrip("#")) for a in argv[1:]]
    if not prs:
        out = subprocess.run(["gh", "pr", "list", "--author", "CBirkbeck", "--state", "open",
                              "--json", "number,headRefName"], capture_output=True, text=True).stdout
        prs = [p["number"] for p in json.loads(out or "[]")
               if p["headRefName"].startswith("improve/")]
    depth, entries = fetch()
    print("merge queue depth: %s" % (depth if depth is not None else "unavailable"))
    stranded = []
    for n in prs:
        out = subprocess.run(["gh", "pr", "view", str(n), "--json", "labels"],
                             capture_output=True, text=True).stdout
        labels = [l["name"] for l in json.loads(out or '{"labels":[]}')["labels"]]
        label = "ready-to-merge" if "ready-to-merge" in labels else ",".join(labels)
        e = entries.get(n)
        v = queue_verdict(label, e is not None,
                          e["position"] if e else None, e["state"] if e else None)
        if v == "STRANDED":
            stranded.append(n)
        print("  #%-6s %-22s %s" % (n, label, v))
    if stranded:
        print("\nSTRANDED: %s" % ", ".join("#%d" % n for n in stranded))
        print("  The bot enqueues on the label transition, so these will NOT return on their own.")
        print("  Merge origin/main into each, re-gate, push (r679).")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
