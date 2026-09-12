#!/usr/bin/env python3
"""declinedguard.py <decl> [<decl> ...]

Has this declaration been declined before, and why?

READ THIS BEFORE TRUSTING A `no-record` VERDICT.
-------------------------------------------
This tool's failure mode is asymmetric. A `DECLINED` verdict is strong: it shows you the ledger
row. A `no-record` verdict is WEAK -- it means "no decline record matched", not "never declined".
It is printed as `no-record` for exactly that reason. Five mechanisms produce false `no-record`s,
all of them observed live in this ledger:

  1. ELLIPSIS. Declines are often written truncated: `classNumber_le_five_…`, `RowExchangeable…`,
     `exists_mem_subgroup_mul_eqOn…`, `Reindex.lean …degree_eq_three`. Handled below by matching
     an elided token as a prefix/suffix against the query.
  2. MULTI-COLUMN ROWS. Declines appear in 2-, 3- and 4-column tables
     (`| decl | 189 | already declined |`). An earlier version of this tool matched only
     2-column rows and therefore missed those. Handled: any row with >= 2 cells is considered.
  3. NAME DRIFT. `linearIndependent_mul_pow_of_linearIndependent_residue` was declined; the
     declaration is now `linearIndependent_mul_pow_of_forall_linearIndependent_residue`. A
     decline recorded under an old name cannot be found by the new one. NOT handled -- no tool
     can be -- so a `no-record` on a plausible-looking name still deserves a `git log -S` check.
  4. PROSE DECLINES. Declines written in paragraphs rather than table rows are invisible here.
     Mitigation is a convention, not code: EVERY DECLINE GOES IN A TABLE ROW.
  5. VOCABULARY. A row is taken as a decline if it sits under a `Declines`/`deferrals` heading OR
     its text uses decline vocabulary. The heading test carries most of the weight: obstacles are
     frequently stated without any keyword ("nothing to lift"), and a vocabulary-only filter
     silently dropped `lie_typeDRootProduct_of_not_adjacent`.

The instrument that this replaced was `grep -c name ledger.md`, which is broken in BOTH
directions: the ledger records its own control names (so a negative control returns a hit and
poisons itself), and it contains pasted candidate/measurement tables (so a hit means "mentioned",
not "declined").

Exit status: 1 if any queried name has a decline record, 0 if none did (so it can gate a script).
"""
import re
import sys
import os

LEDGER = os.path.normpath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "ledger.md"))

# Vocabulary that marks a table row as recording a DECLINE rather than a measurement.
DECLINE_WORDS = re.compile(
    r"declin|closure|residual|contended|skipped|deferr|rename, not|out of .*scope|"
    r"needs? `?/decompose|blocked|do not re-derive|ledger wins", re.I)

ELIDE = re.compile(r"[…]|\.\.\.")
TOKEN = re.compile(r"`([^`]+)`")
MIN_PREFIX = 12  # an elided stem shorter than this is too generic to match on


HEADING = re.compile(r"^#{1,6}\s+(.*)$")
DECLINE_SECTION = re.compile(r"declin|deferral", re.I)


def rows(path):
    """Yield (lineno, first_cell, full_row, in_decline_section) for markdown rows with >= 2 cells.

    Section-awareness matters as much as the row text: a decline written under a
    `### Declines / deferrals` heading often states its obstacle without ever using a word like
    "declined" ("four symmetric branches share only a 2-line preamble ... nothing to lift"), so a
    vocabulary filter alone silently drops it. That was observed live on
    `lie_typeDRootProduct_of_not_adjacent`.
    """
    section = ""
    for lineno, line in enumerate(open(path, encoding="utf-8"), 1):
        line = line.rstrip("\n")
        h = HEADING.match(line)
        if h:
            section = h.group(1)
            continue
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 2:
            continue
        if set("".join(cells)) <= set("-: "):      # separator row
            continue
        yield lineno, cells[0], line, bool(DECLINE_SECTION.search(section))


def stems(cell):
    """Backticked tokens in a cell, plus the bare tail of each dotted name."""
    out = []
    for tok in TOKEN.findall(cell):
        for piece in re.split(r"[\s,]+", tok):
            piece = piece.strip()
            if piece:
                out.append(piece)
    return out


def matches(query, cell):
    """Does this row's first cell refer to `query`? Handles elision in either direction."""
    bare = query.rsplit(".", 1)[-1]
    if query in cell or bare in cell:
        return True
    for st in stems(cell):
        if not ELIDE.search(st):
            continue
        for part in ELIDE.split(st):
            part = part.strip().strip("`")
            if len(part) >= MIN_PREFIX and (part in query or part in bare):
                return True
    return False


def main(argv):
    # `--ledger PATH` exists so this tool can be CONTROLLED (r446).  Without it the ledger path is
    # fixed relative to this file, and the only way to test the matcher would be to run a COPY of
    # the script beside a fixture ledger -- which tests the copy, not the instrument (r320).
    ledger = LEDGER
    argv = list(argv)
    if "--ledger" in argv:
        i = argv.index("--ledger")
        ledger = argv[i + 1]
        del argv[i:i + 2]
    if len(argv) < 2:
        print(__doc__)
        return 2
    allrows = list(rows(ledger))
    declines = [(ln, c, r) for ln, c, r, insec in allrows
                if insec or DECLINE_WORDS.search(r)]
    if not declines:
        print("declinedguard: parsed ZERO decline rows -- refusing to answer (an empty rule set "
              "would clear every name, which is the dangerous direction).", file=sys.stderr)
        return 2
    print(f"# {len(declines)} decline rows (of {len(allrows)} table rows) in {ledger}")
    print("# a `no-record` verdict is WEAK: see this file's header for its five blind spots")
    any_declined = False
    for query in argv[1:]:
        hits = [(ln, r) for ln, c, r in declines if matches(query, c)]
        if hits:
            any_declined = True
            print(f"DECLINED   {query}")
            for ln, r in hits[:3]:
                print(f"           ledger.md:{ln}  {r[:150]}")
        else:
            print(f"no-record  {query}")
    return 1 if any_declined else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
