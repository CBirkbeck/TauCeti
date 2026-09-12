#!/usr/bin/env python3
"""deadprivate.py <dir> -- `private` declarations no live code references.

A `private` declaration is invisible outside its file, so "is it used?" is decidable from
that one file.  What it is NOT is a decision about whether the declaration should go: a
private declaration may exist to be *elaborated* (a regression instance, a worked example),
and one may be the only surviving statement of a fact about a PUBLIC definition.  Those
calls need a human read; this tool only finds candidates.

Confounds handled, each found by checking a suspicious result rather than by assumption:

* ATTRIBUTE REGISTRATION -- `@[simp]`, `@[ext]`, `@[aesop]` … enter a declaration into a
  discrimination tree, and tactics consume it without naming it.  Skipped, not reported.
* DOT NOTATION -- `private theorem IsCosetSelection.exists_lt` is invoked `hm.exists_lt`,
  and a `private lemma foo` inside a namespace is invoked `W.foo`.  Note this is the exact
  OPPOSITE of unusedscan's rule: there, `foo.h` is not a use of a local `h`; here these
  names are global and `W.foo` IS a use of `foo`.
* BARE LEAF under `open Foo` -- `ReducedTensorWords.gradedCoderivSummand` used as
  `gradedCoderivSummand`.
* TRANSITIVITY -- a helper whose only consumer is itself dead is dead, but looks used until
  that consumer goes.  The dead set is therefore a FIXPOINT: mark, hide the marked bodies,
  re-mark, repeat.  Computed here because the first PR built from this tool would otherwise
  have left newly-dead code behind (r215/r216).

Identifier boundaries follow unusedscan: modifier letters (`Vᵀ`, `Sᶜ`) are postfix notation
and end an identifier; subscripts (`h₀`) do not.

FIRING CONTROL on stderr: files, private declarations, attribute-skipped, dot-notation uses.
"""
import re, sys, os, unicodedata

SUB = set("₀₁₂₃₄₅₆₇₈₉ₐₑₒₓₔₕₖₗₘₙₚₛₜᵢⱼ")

CMD = re.compile(r'^(?:@\[|/-|(?:theorem|lemma|def|abbrev|instance|structure|class|example|'
                 r'namespace|end|section|variable|open|attribute|private|protected|'
                 r'noncomputable|nonrec|deriving|macro|syntax|notation|import|set_option|'
                 r'omit|include|suppress_compilation)\b)')

PRIV = re.compile(r'^private\s+(?:noncomputable\s+|nonrec\s+|protected\s+|unsafe\s+)*'
                  r'(theorem|lemma|def|abbrev|structure|inductive)\s+'
                  r'([A-Za-z_Ͱ-Ͽ][^\s(){}\[\]:]*)')


def is_ident_char(c):
    if c in SUB:
        return True
    if unicodedata.category(c) == "Lm":
        return False
    return c.isalnum() or c in "_'!?"


def occurs(name, text):
    """Any boundary-delimited occurrence, INCLUDING after a dot (these names are global)."""
    i = text.find(name)
    while i != -1:
        before = text[i - 1] if i > 0 else " "
        after = text[i + len(name)] if i + len(name) < len(text) else " "
        if not is_ident_char(before) and not is_ident_char(after):
            return True
        i = text.find(name, i + 1)
    return False


def span_end(L, i):
    end = i + 1
    while end < len(L) and not (L[end] and not L[end][0].isspace() and CMD.match(L[end])):
        end += 1
    return end


def collect(L, stats):
    """Private declarations that are not attribute-registered, as (line, kind, name)."""
    out, incomment = [], 0
    for i, line in enumerate(L):
        opens, closes = line.count("/-"), line.count("-/")
        was = incomment
        incomment = max(0, incomment + opens - closes)
        if was or opens > closes:
            continue
        m = PRIV.match(line)
        if not m:
            continue
        stats["priv"] += 1
        if i > 0 and L[i - 1].lstrip().startswith("@["):
            stats["attr"] += 1
            continue
        j = i - 1
        while j >= 0 and L[j].rstrip().endswith("-/") and not L[j].lstrip().startswith("/--"):
            j -= 1
        if j >= 0 and L[j].lstrip().startswith("/--") and j - 1 >= 0 \
                and L[j - 1].lstrip().startswith("@["):
            stats["attr"] += 1
            continue
        out.append((i, m.group(1), m.group(2)))
    return out


def scan(path, rows, stats):
    L = open(path, encoding="utf-8").read().split("\n")
    cands = collect(L, stats)
    if not cands:
        return
    spans = {i: span_end(L, i) for i, _, _ in cands}
    dead = set()
    while True:
        hidden = set()
        for i in dead:
            hidden |= set(range(i, spans[i]))
        grew = False
        for i, kind, name in cands:
            if i in dead:
                continue
            own = set(range(i, spans[i]))
            rest = "\n".join(x for k, x in enumerate(L) if k not in own and k not in hidden)
            if occurs(name, rest):
                continue
            if "." in name:
                leaf = name.rsplit(".", 1)[1]
                if occurs(leaf, rest):
                    stats["dot"] += 1
                    continue
            dead.add(i)
            grew = True
        if not grew:
            break
    for i, kind, name in cands:
        if i in dead:
            rows.append((path, i + 1, kind, name))


def main():
    root = sys.argv[1]
    rows, stats = [], {"files": 0, "priv": 0, "attr": 0, "dot": 0}
    for dp, _, fs in os.walk(root):
        for f in fs:
            if f.endswith(".lean"):
                stats["files"] += 1
                scan(os.path.join(dp, f), rows, stats)
    for p, ln, kind, nm in rows:
        print(f"{p}:{ln}\t{kind} {nm}")
    print(f"# FIRING CONTROL: {stats['files']} files, {stats['priv']} private declarations; "
          f"{stats['attr']} skipped (attribute-registered), {stats['dot']} used via dot "
          f"notation. dead={len(rows)}", file=sys.stderr)


if __name__ == "__main__":
    main()
