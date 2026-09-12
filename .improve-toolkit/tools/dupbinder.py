#!/usr/bin/env python3
"""dupbinder.py <dir> -- two binders in ONE signature with identical type text.

The last member of the scope-constant family (r225): everything inside a single signature
shares one namespace, one `variable` block and one local context, so identical type TEXT here
really is an identical hypothesis -- the ambiguity that sinks cross-declaration comparison
(r224, r226) cannot arise.  A declaration carrying `(h₁ : P) (h₂ : P)` has a redundant binder.

Only EXPLICIT `( )` and strict-implicit `{ }` binders are compared:

* `[ ]` instance binders are excluded -- repeating an instance is sometimes deliberate
  (a second, definitionally different path to the same class), and typeclass resolution, not
  the text, decides whether it matters;
* a binder group naming several variables at once (`(a b : ℕ)`) is not a duplicate of itself;
* types are compared after whitespace collapse and nothing else, for the reason r224 records:
  normalising further is how a text screen starts claiming to know what Lean means.

FIRING CONTROL on stderr: declarations scanned, declarations carrying 2+ comparable binders.
"""
import re, sys, os
from collections import defaultdict

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*'
                  r'(theorem|lemma|def|abbrev)\s+([A-Za-z_Ͱ-Ͽ][^\s(){}\[\]:]*)')


def top_level_assign(text):
    depth = 0
    for i, ch in enumerate(text):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and text[i:i + 2] == ":=":
            return i
    return -1


def binders(sig):
    """Top-level ( ) and { } groups as (kind, names, type)."""
    out, depth, start, kind = [], 0, None, None
    for i, c in enumerate(sig):
        if c in "([{⟨":
            if depth == 0 and c in "({":
                start, kind = i + 1, c
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
            if depth == 0 and start is not None:
                inner = sig[start:i]
                if ":" in inner:
                    names, typ = inner.split(":", 1)
                    if not any(ch in names for ch in "()[]{}⟨⟩"):
                        out.append((kind, names.split(), " ".join(typ.split())))
                start = None
        elif c == ":" and depth == 0:
            break
    return out


def main():
    root = sys.argv[1]
    rows, stats = [], {"files": 0, "decls": 0, "comparable": 0}
    for dp, _, fs in os.walk(root):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            stats["files"] += 1
            L = open(os.path.join(dp, f), encoding="utf-8").read().split("\n")
            incomment = 0
            for i, line in enumerate(L):
                o, c = line.count("/-"), line.count("-/")
                was = incomment
                incomment = max(0, incomment + o - c)
                if was or o > c:
                    continue
                m = DECL.match(line)
                if not m:
                    continue
                stats["decls"] += 1
                chunk, j = [], i
                while j < len(L) and j < i + 200:
                    chunk.append(L[j]); j += 1
                    t = "\n".join(chunk)
                    if re.search(r':=(\s|$)', t) and t.count("(") <= t.count(")"):
                        break
                head = "\n".join(chunk)
                cut = top_level_assign(head)
                if cut == -1:
                    continue
                name = m.group(2)
                sig = head[head.index(name) + len(name):cut]
                bs = binders(sig)
                if len(bs) >= 2:
                    stats["comparable"] += 1
                seen = defaultdict(list)
                # Only PROPOSITIONS can be redundantly repeated.  Two DATA binders of the
                # same type are normal and necessary -- `{s t : Set α}` needs both.  The
                # discriminator is the one unusedscan uses: a hypothesis type carries a
                # relation.  (My first control expected `{s : Set α} {t : Set α}` to fire;
                # the expectation was the error, not the code. r227)
                # `→` is the FUNCTION arrow: `ℝ → ℂ` is a curve, not a proposition, and two
                # curves in one signature are normal.  `≃`/`≅` likewise form a TYPE of
                # equivalences.  Including them turned 17 hits into 66, all data binders.
                # The relational test is a proxy for "is a Prop" and it leaks on every
                # type-FORMING operator. (r227)
                REL = set("=≤<∈≠∣⊆⊂≥>∉∤↔∧∨")
                for kind, names, typ in bs:
                    # length guard was arbitrary and suppressed `s ⊆ t` (5 chars), a
                    # perfectly good duplicated hypothesis; the relational test is the
                    # real filter, so keep only a minimal sanity floor. (r227)
                    # A relational glyph must be SPACE-DELIMITED to be an infix relation.
                    # `ℝ≥0` embeds `≥` inside NOTATION for the nonnegative reals and is a
                    # data type; two of them in one signature are two numbers.  Fourth leak
                    # in this same proxy, after `→`, `≃` and the length guard. (r227)
                    rel = any(f' {ch} ' in typ for ch in REL)
                    if len(typ) >= 3 and rel:
                        seen[typ].append((kind, names))
                for typ, hits in seen.items():
                    if len(hits) >= 2:
                        rows.append((os.path.join(dp, f), i + 1, name, typ, hits))
    for path, ln, name, typ, hits in rows:
        who = " | ".join(f"{k}{' '.join(n)}{'}' if k == '{' else ')'}" for k, n in hits)
        print(f"{path}:{ln}\t{name}\t{who}\ttype: {typ[:90]}")
    print(f"# FIRING CONTROL: {stats['files']} files, {stats['decls']} declarations scanned; "
          f"{stats['comparable']} carry 2+ comparable binders. duplicates={len(rows)}",
          file=sys.stderr)


if __name__ == "__main__":
    main()
