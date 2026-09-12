#!/usr/bin/env python3
"""deadhave.py <snapshot> [min_body_lines] [--set]

--set: instead of `have`, scan the `with h` clause of `set x := e with h`.
That clause binds the defining equation; when nothing consumes it the clause
is dead and deleting it is the whole fix.  The binding is an equation by
construction, so the class-typed test does not apply -- every other
suppression (context-searching tactics, comment stripping, shadowing) does.

Find a NAMED `have` in a proof body whose name is never used afterwards --
dead code INSIDE a proof.  Same family as deadprivate.py (dead declarations)
and unusedscan.py (unused binders): the reviewer VERIFIES it by deleting the
line and rebuilding, rather than weighing a judgement.

DOMINANT FALSE POSITIVE.  Many tactics consume hypotheses from the local
context BY SEARCH rather than by name -- `omega`, `linarith`, `simp_all`,
`aesop`, `assumption`, `positivity`, ...  A `have` feeding one of those is
load-bearing while being nameless at the point of use.  So ANY such tactic
appearing after the `have` suppresses it.  This over-suppresses: one
`linarith` late in a long proof hides an unrelated dead `have` early on.
That is deliberate -- a false negative costs nothing, a false positive costs
a review round.

Other suppressions:
  * CLASS-TYPED haves.  In Lean 4 any local hypothesis whose type is a class is
    an instance candidate, found by typeclass SEARCH and never by name -- so an
    unreferenced `have hproj : Projective P` is load-bearing.  Reusing the rule
    unusedscan.py validated in r207: a type carrying a SPACE-DELIMITED relational
    glyph (= <= < in != ...) cannot be an instance and is the only kind worth
    reading; everything else is suppressed.  Space-delimiting is r227's
    correction (`R>=0` is not a relation).  A `have` with no type ascription
    has no type to test, so it is suppressed too.
  * STRANDED BINDERS (r289, learned from a failed CI run).  A `have` can be
    genuinely dead while its PROOF TERM is the sole consumer of one of the
    declaration's own binders; deleting it leaves that binder unreferenced and
    the Mathlib linter errors with "Variable name `x` is not explicitly
    referenced".  Such a hit is still a finding, but it cannot be shipped as a
    lone deletion -- it needs the binders removed with it, which is a statement
    change and a separate topic.  Those rows are marked STRANDS.
  * destructuring `have ⟨a, b⟩ := ...` -- the binder is not a single ident
  * a later `have` rebinding the name counts as an occurrence, so a dead
    binding shadowed by a live one is skipped (safe direction)
  * `.name` is a projection/global suffix, not a use of the local
  * comments are stripped before the token search
"""
import re, sys, os

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*'
    r'(theorem|lemma|def|instance|abbrev|example)\b')
STOP = re.compile(r'^(?:@\[|/--|/-!|--|open\b|namespace\b|end\b|section\b|variable\b|'
                  r'import\b|universe\b|attribute\b|local\b|set_option\b|omit\b|include\b|'
                  r'private\b|protected\b|noncomputable\b|theorem\b|lemma\b|def\b|'
                  r'instance\b|abbrev\b|example\b|structure\b|inductive\b|class\b|'
                  r'deriving\b|macro\b|syntax\b|notation\b|declare\b|suppress\b)')

# a named have: `have foo`, `have foo :`, `have foo (n : N) :`, `have foo :=`
HAVE = re.compile(r'^\s*have\s+([^\s:=(\[⟨{]+)')
# `set x := e with h`, `set x : T := e with ← h`
SET = re.compile(r'^\s*set\s+.*\swith\s+(?:←\s*)?([^\W\d][\w\'!?]*)\s*$')
# `let x := e` / `let x : T := e` in a tactic proof.  Anonymous `let : T := e` has no name and is
# skipped by construction.  A named let of CLASS type feeds instance search (r301: FinitePaths.lean
# binds `let pathFinite ... : Finite ...`), so the class-typed test applies exactly as for `have`.
# `let rec f ...` and `let mut x := ...` are Lean keywords, not binding names (r301: the first
# pass captured `rec` from `let rec` and reported it as a dead binding).
LET = re.compile(r'^\s*let\s+(?!rec\b|mut\b)([^\s:=(\[⟨{]+)')

# tactics that read the local context by search, not by name
SCAN = re.compile(r'(?<!\w)('
    r'omega|linarith|nlinarith|polyrith|positivity|simp_all|aesop|tauto|itauto|'
    r'assumption|decide|norm_num|norm_cast|field_simp|gcongr|bound|cc|trivial|'
    r'rwa|simpa|subst|subst_vars|contradiction|simp_arith|omega_nat|'
    r'grobner|congr|congrm|convert|lia|lra|nlia|nlra|field|'
    r'hint|fin_cases|interval_cases|order|grind|solve_by_elim|tfae_finish|'
    r'measurability|fun_prop|continuity|differentiability|finiteness|'
    r'infer_instance|subsingleton|exact\?|apply\?|constructor_ext'
    r')(?!\w)')

REL = set("=≤<∈≠∣⊆⊂≥>∉∤")

def toplevel(t):
    """Blank out bracketed groups: a relation inside `Nonempty {v // a = b}` is the
    subtype's predicate, not the have's own relation (r289)."""
    out, depth = [], 0
    for ch in t:
        if ch in '([{⟨': depth += 1; out.append(' ')
        elif ch in ')]}⟩': depth -= 1; out.append(' ')
        else: out.append(ch if depth == 0 else ' ')
    return ''.join(out)

def relational(t):
    """A top-level relational glyph, space-delimited (r227: `ℝ≥0` is not one)."""
    t = toplevel(t)
    for i, c in enumerate(t):
        if c in REL:
            before = t[i-1] if i > 0 else ' '
            after = t[i+1] if i+1 < len(t) else ' '
            if before == ' ' and (after == ' ' or after in REL):
                return True
    return False

def have_type(body, bi, kw='have'):
    """Type text of the have on line bi: between its top-level `:` and `:=`.
    Returns None when there is no ascription (nothing to test -> suppress)."""
    txt, base = [], indent(body[bi])
    for s in body[bi:]:
        if s.strip() and len(txt) and indent(s) <= base:
            break
        txt.append(s)
        if re.search(r':=', s):
            break
    joined = ' '.join(x.strip() for x in txt)
    joined = joined[joined.index(kw) + len(kw):]
    depth, colon = 0, -1
    for i, ch in enumerate(joined):
        if ch in '([{⟨': depth += 1
        elif ch in ')]}⟩': depth -= 1
        elif ch == ':' and depth == 0:
            if joined[i:i+2] == ':=':
                return joined[colon+1:i].strip() if colon >= 0 else None
            if colon < 0: colon = i
    return joined[colon+1:].strip() if colon >= 0 else None

def strip_comments(text):
    text = re.sub(r'/-.*?-/', ' ', text, flags=re.S)
    return re.sub(r'--[^\n]*', ' ', text)

def is_idch(c):
    return c.isalnum() or c in "_'!?"

def occurs(name, text):
    n, start = len(name), 0
    while True:
        k = text.find(name, start)
        if k < 0:
            return False
        before = text[k-1] if k > 0 else ' '
        after = text[k+n] if k+n < len(text) else ' '
        # `.name` is a projection or the tail of a global name, not our local
        if before != '.' and not is_idch(before) and not is_idch(after):
            return True
        start = k + 1

def indent(line):
    n = 0
    for ch in line:
        if ch == ' ': n += 1
        elif ch == '\t': n += 2
        else: break
    return n

stats_tc = [0]
set_mode = "--set" in sys.argv
let_mode = "--let" in sys.argv

def scan_file(path, minbody):
    try:
        lines = open(path, encoding='utf-8').read().split('\n')
    except Exception:
        return [], 0
    out, ndecl = [], 0
    i = 0
    while i < len(lines):
        if indent(lines[i]) == 0 and DECL.match(lines[i]):
            start = i
            m = DECL.match(lines[i])
            after = lines[i][m.end():].strip()
            dname = after.split()[0].rstrip(':') if after else '?'
            j, by_line = i, None
            while j < len(lines) and j < start + 400:
                if re.search(r':=\s*by\b', lines[j]):
                    by_line = j; break
                if j > start and indent(lines[j]) == 0 and STOP.match(lines[j]):
                    break
                j += 1
            if by_line is None:
                i += 1; continue
            sig = '\n'.join(lines[start:by_line + 1])
            # r302: a declaration whose TYPE opens with `let x := ...` is entered in tactic mode
            # by a matching `let x := ...`, which DISCHARGES the goal's binder rather than making
            # a fresh one.  Such a tactic let is load-bearing even though nothing names it.
            sig_lets = set(re.findall(r'(?:^|\s)let\s+([^\W\d][\w\'!?]*)\s*(?::|:=)', sig))
            binders = []
            for grp in re.findall(r'[({\[]([^:()\[\]{}]*?):', sig):
                binders += [t for t in grp.split() if t and t[0].isalpha()]
            k, body = by_line + 1, []
            while k < len(lines):
                s = lines[k]
                if s.strip() and indent(s) == 0 and STOP.match(s):
                    break
                body.append(s); k += 1
            while body and not body[-1].strip():
                body.pop()
            if len([s for s in body if s.strip()]) >= minbody:
                ndecl += 1
                for bi, bl in enumerate(body):
                    if set_mode:
                        sm = SET.match(bl)
                        if not sm:
                            continue
                        hname = sm.group(1)
                        rest = strip_comments('\n'.join(body[bi+1:]))
                        if SCAN.search(rest) or '[*]' in rest or 'at *' in rest:
                            continue
                        if occurs(hname, rest):
                            continue
                        out.append((path, by_line + 2 + bi, dname, hname,
                                    'set-equation', len([s for s in body if s.strip()]), []))
                        continue
                    hm = (LET if let_mode else HAVE).match(bl)
                    if not hm:
                        continue
                    hname = hm.group(1)
                    if hname in ('this',) or not hname[0].isalpha() and hname[0] != '_':
                        continue
                    if hname.startswith('_'):
                        continue
                    htype = have_type(body, bi, 'let' if let_mode else 'have')
                    if let_mode:
                        if hname in sig_lets:
                            stats_tc[0] += 1
                            continue
                        # r209's lesson, recurring: the relational partition was tuned for Prop
                        # HYPOTHESES and does not transfer to a DATA population.  A `let` binds
                        # data, so `let c : Nat := ...` is not a class-suspect.  Report every row
                        # and MARK the ones whose type could be a class, never hide them.
                        if htype is None: htype = '?'
                        # strip a leading `∀ x y,` so `∀ i, Module.Finite ...` is tested on its
                        # HEAD (r302: hFin went unmarked only because `∀` is not ASCII-upper)
                        head = re.sub(r'^∀[^,]*,\s*', '', htype)
                        if not relational(head) and head[:1].isascii() and head[:1].isupper():
                            htype = '?TC-check ' + htype
                    elif htype is None or not relational(htype):
                        stats_tc[0] += 1
                        continue
                    rest = strip_comments('\n'.join(body[bi+1:]))
                    if SCAN.search(rest) or '[*]' in rest or 'at *' in rest:
                        continue
                    if occurs(hname, rest):
                        continue
                    # does deleting this have strand one of the declaration's binders?
                    base = indent(bl); j2 = bi + 1
                    while j2 < len(body) and (not body[j2].strip() or indent(body[j2]) > base):
                        j2 += 1
                    without = strip_comments('\n'.join(body[:bi] + body[j2:]))
                    inblock = strip_comments('\n'.join(body[bi:j2]))
                    # stranded == used HERE and nowhere else.  A binder absent from both
                    # is a signature-parse artifact, not something this deletion strands.
                    stranded = [b for b in set(binders)
                                if b != hname and occurs(b, inblock) and not occurs(b, without)]
                    out.append((path, by_line + 2 + bi, dname, hname, htype,
                                len([s for s in body if s.strip()]), sorted(stranded)))
            i = k; continue
        i += 1
    return out, ndecl

def main():
    root = sys.argv[1]
    minbody = int(sys.argv[2]) if len(sys.argv) > 2 and not sys.argv[2].startswith("--") else 1
    hits, total = [], 0
    for dp, _, fns in os.walk(root):
        for fn in fns:
            if fn.endswith('.lean'):
                h, n = scan_file(os.path.join(dp, fn), minbody)
                hits += h; total += n
    for p, ln, d, h, ty, bl, st in sorted(hits):
        mark = f"  STRANDS {' '.join(st)}" if st else ""
        print(f"{os.path.relpath(p, root)}:{ln}  {d}  have {h} : {ty}  (body {bl}){mark}")
    print(f"-- FIRING CONTROL: {total} proof bodies scanned, {len(hits)} dead have(s), "
          f"{stats_tc[0]} class-suspect suppressed", file=sys.stderr)

main()
