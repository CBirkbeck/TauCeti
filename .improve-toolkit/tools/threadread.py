#!/usr/bin/env python3
"""threadread.py <pr> [--repo owner/name] [--all] -- current rubric findings on a PR.

WHY THIS EXISTS (r450).  Reading a review thread by hand went wrong in the obvious way: the
pipeline **edits the existing thread comment in place** on re-review, so `created_at` is the
timestamp of the FIRST finding on that rubric while the body is the LATEST one.  #5905's
`documentation` comment read `created_at: 01:23:50Z` -- before the push that answered it -- with
completely new text.  Sorting a thread by `created_at`, or taking "the newest by `created_at`",
therefore shows current text under a stale timestamp and can hand back an older finding.

    ALWAYS sort review threads by `updated_at`.

The board sweep already did; the by-hand thread read did not, which is exactly the kind of
inconsistency that survives until it is written down as code.

Prints, per rubric, the CURRENT finding text and the `updated_at` that actually dates it.  With
`--all`, includes rubrics whose latest state is an approval; by default only unresolved ones are
shown, since those are the ones that need answering.

A firing control goes to stderr (r184): a screen that can return nothing must say whether it ran.
"""
import json, re, subprocess, sys

def sh(*a):
    r = subprocess.run(a, capture_output=True, text=True)
    return r.stdout

def main():
    argv = sys.argv[1:]
    if not argv:
        print(__doc__)
        return 2
    repo = "TauCetiProject/TauCeti"
    if "--repo" in argv:
        i = argv.index("--repo"); repo = argv[i + 1]; del argv[i:i + 2]
    # `--fixture DIR` reads board.json / threads.json instead of the network, so this can be
    # CONTROLLED (r451) -- same reason declinedguard grew `--ledger` at r446.
    fixture = None
    if "--fixture" in argv:
        i = argv.index("--fixture"); fixture = argv[i + 1]; del argv[i:i + 2]
    show_all = "--all" in argv
    if show_all:
        argv.remove("--all")
    pr = argv[0] if argv else "0"

    # THE SCOREBOARD IS THE AUTHORITY ON STATE; THE THREAD ONLY CARRIES TEXT (r451).  A thread
    # comment is NOT rewritten when its rubric flips to approve -- #5905's `api-design`,
    # `generality` and `placement` threads still read `request_changes` long after the board had
    # them green.  Deciding "unresolved" from the thread text therefore re-surfaces findings that
    # were already answered.  Take the state from the newest current-head scoreboard instead.
    board = (open(f"{fixture}/board.json").read() if fixture
             else sh("gh", "api", f"repos/{repo}/issues/{pr}/comments", "--paginate"))
    states, board_head = {}, None
    try:
        best = None
        for c in json.loads(board) if board.strip() else []:
            m = re.search(r"tauceti-meta:v1\s*(\{.*?\})\s*-->", c.get("body", ""), re.S)
            if not m:
                continue
            j = json.loads(m.group(1))
            if j.get("kind") != "scoreboard":
                continue
            if best is None or c["updated_at"] > best[0]:
                best = (c["updated_at"], j)
        if best:
            states = best[1].get("states", {})
            board_head = best[1].get("head_sha", "")[:10]
    except (json.JSONDecodeError, KeyError):
        pass

    raw = (open(f"{fixture}/threads.json").read() if fixture
           else sh("gh", "api", f"repos/{repo}/pulls/{pr}/comments", "--paginate"))
    try:
        comments = json.loads(raw) if raw.strip() else []
    except json.JSONDecodeError:
        print("threadread: could not parse the comments payload", file=sys.stderr)
        return 2

    # One entry per rubric, keeping the most recently UPDATED comment for that rubric.
    latest = {}
    for c in comments:
        m = re.search(r"tauceti-rubric:([\w-]+)", c.get("body", ""))
        if not m:
            continue
        rub = m.group(1).rstrip("-")
        if rub not in latest or c["updated_at"] > latest[rub]["updated_at"]:
            latest[rub] = c

    shown = 0
    for rub, c in sorted(latest.items(), key=lambda kv: kv[1]["updated_at"]):
        body = re.sub(r"<!--.*?-->", "", c["body"], flags=re.S)
        body = re.sub(r"<sub>.*?</sub>", "", body, flags=re.S)
        body = re.sub(r"Reply in this thread to contest.*?\)", "", body, flags=re.S)
        state = states.get(rub)
        # No board yet -> fall back to the thread text, and say so.
        unresolved = (state != "green") if states else ("request_changes" in body)
        if not unresolved and not show_all:
            continue
        shown += 1
        edited = c["updated_at"] != c["created_at"]
        print(f"=== {rub}  [{states.get(rub, 'no board')}]  updated={c['updated_at']}"
              + (f"  (EDITED IN PLACE; created={c['created_at']})" if edited else "") + " ===")
        print("\n".join("  " + l for l in body.strip().split("\n") if l.strip()))
        print()
    print(f"# FIRING CONTROL: {len(comments)} review comments, {len(latest)} rubric threads, "
          f"{shown} shown ({'all' if show_all else 'unresolved only'}); "
          f"state from board at {board_head or 'NO BOARD -- fell back to thread text'} "
          f"({len(states)} rubric states).", file=sys.stderr)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
