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

TWO WAYS TO BE OUT OF THE QUEUE, AND ONLY ONE IS MINE (found by running this tool, r679).  Its
first run flagged #5950 alongside #6093.  But #5950 has **no `merge_queue` timeline events at all**
-- the bot never managed to enqueue it, because it needs a human review on a human-owned file.
#6093 had `added_to_merge_queue` and then `removed_from_merge_queue`.  Same "labelled but absent",
opposite causes, and refreshing the branch is the fix for exactly one of them:

    EJECTED       enqueued, then dropped   -> read it; merge-sweep re-enqueues a green TauCeti/-only PR (r799)
    NEVER-QUEUED  no queue events ever     -> NOT mine: the bot could not enqueue it at all

So the enqueue history, not queue membership alone, is what makes the verdict actionable.
QUEUED at position 18 is not a problem, however long it has been there.
"""
import datetime, json, subprocess, sys

REPO = "TauCetiProject/TauCeti"

_Q = """{repository(owner:"%s",name:"%s"){mergeQueue(branch:"%s"){entries(first:100){
  totalCount nodes{position state enqueuedAt pullRequest{number}}}}}}"""


def queue_verdict(label, in_queue, position=None, state=None, ever_enqueued=False):
    """EJECTED / NEVER-QUEUED / QUEUED:… / MERGING:… / NOT-READY.

    Pure so the controls can exercise it on fixture data without touching the network.

    EJECTED is a verdict to READ, not to refresh on (r799).  auto-merge enqueues once per triggering
    event, but TauCetiReview's merge sweep (`runner/sweep.py`, run by `merge-sweep.yml`) re-enqueues a
    green, TauCeti/-only, mergeable PR that is out of the queue and reuses its head-pinned board, so a
    refresh (r679's old advice) only throws that board away.  A removal BY tauceti-review-bot (reason
    `manual`) is a Mathlib bump's queue reservation, not an eviction.  Act only where the sweep cannot:
    on a PR that is not TauCeti/-only, or one it flagged after two evictions at the same head.

    NEVER-QUEUED is the other shape and is NOT actionable here: the bot never got it into the
    queue, so the branch is not what is wrong.  #5950 is the standing example -- it needs a human
    review on a human-owned file, and refreshing it would achieve nothing.
    """
    if label != "ready-to-merge":
        return "NOT-READY"
    if not in_queue:
        return "EJECTED" if ever_enqueued else "NEVER-QUEUED"
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


def enqueued_since_ready(events):
    """True iff an `added_to_merge_queue` event falls at or after the LATEST `ready-to-merge` label.

    r700.  "Ever enqueued" was the wrong question.  #6093 was enqueued on 2026-09-12 and ejected that
    evening; two days later a fresh 10/10 board relabelled it `ready-to-merge`, and 90 seconds after
    that -- before any new enqueue -- this tool called it EJECTED and advised merging `main` and
    pushing.  Doing so would have thrown away the board it had just earned.  The history that
    matters is the history of the CURRENT transition: an ejection is an enqueue that followed the
    latest `ready-to-merge` label and then went away.  An old enqueue from a previous transition
    says nothing about this one.

    `events` are timeline entries, either raw (`label: {name: ...}`) or flattened (`label: "..."`).
    """
    def lab(e):
        l = e.get("label")
        return l.get("name") if isinstance(l, dict) else l
    ready = [e.get("created_at") or "" for e in events
             if e.get("event") == "labeled" and lab(e) == "ready-to-merge"]
    if not ready:
        return False
    last = max(ready)
    return any(e.get("event") == "added_to_merge_queue" and (e.get("created_at") or "") >= last
               for e in events)


def latest_ready_at(events):
    """Timestamp of the latest `ready-to-merge` label, or None."""
    ts = [e.get("created_at") for e in events if e.get("event") == "labeled"
          and ((e.get("label") or {}).get("name") if isinstance(e.get("label"), dict)
               else e.get("label")) == "ready-to-merge"]
    return max(ts) if ts else None


def timeline_events(n, owner_repo=REPO):
    r = subprocess.run(
        ["gh", "api", "repos/%s/issues/%d/timeline" % (owner_repo, n), "--paginate", "--jq",
         '.[]|{event, created_at, label: (.label.name // null)}'],
        capture_output=True, text=True)
    # An unreadable timeline is None, NOT an empty one (r722): no events reads as never enqueued.
    if r.returncode != 0:
        return None
    out = r.stdout
    evs = []
    for line in out.splitlines():
        line = line.strip()
        if line:
            try:
                evs.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return evs


def pr_list_cmd(author="CBirkbeck", limit=200):
    """The listing command, with an EXPLICIT limit.

    r679, second time in one round a default hid something: `gh pr list` returns **30** rows by
    default, and this repo carries 30+ open PRs from other lanes (elliptic/, modular/, cft/, ...).
    The bare call silently reported on 2 of 4 `improve/*` PRs -- #6093 and #5950 fell off the end.
    For a tool whose whole job is spotting a SILENTLY stranded PR, silently dropping PRs is the
    one failure it must not have: the older a PR gets, the further down the list it sits, and a
    stranded PR is by definition an old one.
    """
    return ["gh", "pr", "list", "--author", author, "--state", "open",
            "--limit", str(limit), "--json", "number,headRefName"]


def main(argv):
    prs = [int(a.lstrip("#")) for a in argv[1:]]
    if not prs:
        r = subprocess.run(pr_list_cmd(), capture_output=True, text=True)
        try:
            rows = json.loads(r.stdout) if r.returncode == 0 else None
        except ValueError:
            rows = None
        if not isinstance(rows, list):
            print("# UNRUN: the PR listing could not be read -- no verdicts (r722).")
            return 2
        prs = [p["number"] for p in rows if p["headRefName"].startswith("improve/")]
        if len(rows) >= 200:
            print("  (warning: listing hit the 200-PR limit; raise it)", file=sys.stderr)
    depth, entries = fetch()
    print("merge queue depth: %s" % (depth if depth is not None else "unavailable"))
    # An unreadable queue makes every ready PR look absent, and absent-after-enqueue is the verdict
    # that says merge main and push. So no verdicts at all (r722).
    if depth is None:
        print("# UNRUN: the merge queue could not be read -- no verdicts. An unreadable queue is not an"
              " ejection (r722).")
        return 2
    ejected = []
    for n in prs:
        r = subprocess.run(["gh", "pr", "view", str(n), "--json", "labels"],
                           capture_output=True, text=True)
        try:
            labels = [l["name"] for l in json.loads(r.stdout)["labels"]] if r.returncode == 0 else None
        except (ValueError, KeyError, TypeError):
            labels = None
        if labels is None:
            print("  #%-6s %-22s UNKNOWN (labels unreadable)" % (n, "?"))
            continue
        label = "ready-to-merge" if "ready-to-merge" in labels else ",".join(labels)
        e = entries.get(n)
        age = ""
        if e is None and label == "ready-to-merge":
            evs = timeline_events(n)
            # r722: without the timeline, EJECTED and NEVER-QUEUED cannot be told apart.
            if evs is None:
                print("  #%-6s %-22s UNKNOWN (timeline unreadable)" % (n, label))
                continue
            enq, last = enqueued_since_ready(evs), latest_ready_at(evs)
            if last:
                t = datetime.datetime.fromisoformat(last.replace("Z", "+00:00"))
                mins = (datetime.datetime.now(datetime.timezone.utc) - t).total_seconds() / 60
                age = "  (ready-to-merge %.0fm ago)" % mins
        else:
            enq = e is not None
        v = queue_verdict(label, e is not None,
                          e["position"] if e else None, e["state"] if e else None, enq)
        if v == "EJECTED":
            ejected.append(n)
        print("  #%-6s %-22s %s%s" % (n, label, v, age))
    if ejected:
        print("\nEJECTED: %s" % ", ".join("#%d" % n for n in ejected))
        print("  merge-sweep (TauCetiReview runner/sweep.py; hourly at :40, throttled) re-enqueues a green,")
        print("  TauCeti/-only PR that is out of the queue, reusing its head-pinned board. A removal by")
        print("  tauceti-review-bot (reason `manual`) is a bump's queue reservation. Do NOT refresh: act only on")
        print("  a PR the sweep skips (not TauCeti/-only) or flags (evicted twice at one head) (r799).")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
