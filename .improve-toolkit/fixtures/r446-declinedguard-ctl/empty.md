# A ledger holding only measurements

Two traps this file exists to avoid, both hit while writing it:
  * the heading must not contain the stem `declin` — `DECLINE_SECTION` matches it, and a heading
    that merely mentions the word marks its whole table as a decline section;
  * nor may the declaration NAME contain it — `DECLINE_WORDS` is matched against the whole row, so
    a name like `tn_neverDeclined` marks its own row as a decline.
Fixture names must avoid the instrument's own vocabulary, the same way they must avoid being
substrings of one another (r318).

| declaration | body |
|---|---|
| `tn_plainMeasure` | 12 |
