# Fixture ledger for declinedguard

## Round 1 — measurements

These rows are MEASUREMENTS, not declines. `grep -c` cannot tell them apart, which is why it was
replaced. A name appearing here must come back `no-record`.

| declaration | body | verdict |
|---|---|---|
| `tn_measuredOnly` | 128 | prime candidate, queued |
| `tn_alsoMeasured` | 64 | assembly |

## Round 2 — Declines

Rows under this heading are declines even when the text carries no decline vocabulary at all; the
heading test carries most of the weight (mechanism 5).

| declaration | reason |
|---|---|
| `tp_plainDecline` | nothing to lift |
| `tp_ellipsisDecl…` | the wrapper is load-bearing |

## Round 3 — assorted notes

A four-cell row outside any decline heading, carrying decline vocabulary (mechanisms 2 and 5):

| `tp_wideDecline` | 42 | 3 sites | declined: rename, not a defect |
