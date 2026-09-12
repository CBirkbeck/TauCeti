#!/usr/bin/env python3
"""unusedscan.py <dir> -- explicit binders that are never referenced again.

Finds `theorem foo (h : P) ... : C := by ...` where the name `h` appears nowhere in
the REST OF THE STATEMENT and nowhere in the PROOF BODY.  Such a binder is dead
weight: deleting it is a strict generalisation.

Design notes (each guards a defect that has actually cost a round in this ledger):

* **Explicit `( )` binders only.**  An implicit `{n : ℕ}` unused in statement and
  body could never be inferred, so compiling code cannot contain one; and `[Inst]`
  binders are consumed by typeclass search, never by name.  Scanning them is pure
  noise.
* **Lean-aware word boundaries** (r172/r173): `h` must not match inside `hm`, `h'`,
  `h₀`, `h!`.  Identifier chars include unicode letters, digits, `_ ' ! ?` and
  subscripts.  A plain `in`/`\b` regex gets this wrong.
* **Context-consuming tactics disqualify the declaration.**  `omega`, `linarith`,
  `simp_all`, `assumption`, `aesop`, `fun_prop`, `field_simp`, ... read the whole
  local context, so a binder they use is invisible to any textual scan.  A hit
  inside such a proof is a false positive, not a finding.
* **Statement-side use counts.**  `(n : ℕ) (h : 0 < n)` uses `n` in a later binder;
  a dependent type or the conclusion may be the only consumer.

Prints a FIRING CONTROL to stderr: how many declarations were scanned, how many
carried at least one explicit binder, and how many were disqualified.  A screen
that can return zero must be able to say whether it fired (r184).
"""
import re, sys, os, unicodedata

SUB = set("₀₁₂₃₄₅₆₇₈₉"
          "ₐₑₒₓₔₕₖₗₘₙ"
          "ₚₛₜᵢⱼ")

def is_ident_char(c):
    # Unicode MODIFIER LETTERS (category Lm) are postfix NOTATION, not name characters:
    # `Vᵀ` is `Matrix.transpose V` and `Sᶜ` is `Sᶜ`, so the identifier is `V` / `S`.
    # Subscripts stay in (h₀ really is one name), which is why SUB is listed explicitly.
    if c in SUB:
        return True
    if unicodedata.category(c) == "Lm":
        return False
    return c.isalnum() or c in "_'!?"

def occurs(name, text):
    """True if `name` appears in `text` as a whole Lean identifier."""
    i = text.find(name)
    while i != -1:
        before = text[i-1] if i > 0 else " "
        after = text[i+len(name)] if i+len(name) < len(text) else " "
        # a leading '.' means it is a projection/field of something else
        # A leading '.' means a projection (`f.symm`) ONLY when something identifier-like
        # precedes the dot.  In `∫ t in (2 : ℝ)..x` the char before `x` is '.' and the char
        # before THAT is '.', so `x` is a genuine occurrence -- three r209 false positives
        # (`logIntegral`, `halfLinePrimitive`, ...) came from rejecting it.
        proj = (before == "." and i >= 2 and is_ident_char(text[i-2]))
        if not is_ident_char(before) and not proj and not is_ident_char(after):
            return True
        i = text.find(name, i+1)
    return False

# tactics that read the entire local context
CTX = ["assumption", "simp_all", "omega", "tauto", "aesop", "linarith", "nlinarith",
       # `simpa` finishes with `assumption`; `subst b` consumes the equation by naming the
       # VARIABLE, not the hypothesis; `contradiction`/`interval_cases` scan the context.
       # Each of these produced a false positive on the first full-tree run (r207).
       "simpa", "subst", "contradiction", "interval_cases", "assumption'", "apply_assumption",
       # THIS REPO'S OWN vocabulary, found by tabulating the tactics that actually occur in
       # hit bodies rather than by recalling Mathlib's (r207): `lia` alone accounted for 37
       # occurrences and every one of the 11 GradedRing false positives.
       "lia", "grobner", "rwa",
       # `congr` closes its residual subgoals with `assumption`: `theorem ext (h : P.val = Q.val)
       # : P = Q := by cases P; cases Q; congr` compiles ONLY because `congr` consumes `h`.
       # `convert` runs `congr!` and does the same.
       "congr", "convert",
       "polyrith", "decide", "field_simp", "fun_prop", "measurability", "continuity",
       "solve_by_elim", "exact?", "apply?", "hint", "trivial", "order", "bound",
       "gcongr", "positivity", "norm_num", "cfc_tac", "finiteness", "contextual",
       "simp [*", "simp[*", "simp_arith", "grind", "duper", "aesop_cat", "infer_instance"]

# `--defs` widens the scan to definitions.  A dead parameter on a `def` is a STRONGER finding
# than on a theorem: it is live API surface that every call site must supply, and term-mode
# bodies contain no tactics, so most of the context-consuming mechanisms cannot fire.
# `instance` is deliberately NOT included: its arguments exist for typeclass resolution.
KINDS = r'theorem|lemma|def|abbrev' if "--defs" in sys.argv else r'theorem|lemma'
CTX_LIT = [t for t in CTX if not t.replace("_", "").replace("'", "").isalnum()]
CTX_WORD = [t for t in CTX if t not in CTX_LIT]
# a tactic name is not preceded by an identifier char or a dot (`Foo.trivial` is a term)
CTX_RE = re.compile(r"(?<![\w.'])(?:" + "|".join(sorted(map(re.escape, CTX_WORD),
                    key=len, reverse=True)) + r")(?!['\w])")

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+)*'
                  r'(' + KINDS + r')\s+([A-Za-z_Ͱ-Ͽ][^\s(){}\[\]:]*)')

def split_binders(sig):
    """Top-level bracket groups of a signature, as (kind, inner) pairs."""
    out, depth, start, kind = [], 0, None, None
    for i, c in enumerate(sig):
        if c in "({[":
            if depth == 0:
                start, kind = i+1, c
            depth += 1
        elif c in ")}]":
            depth -= 1
            if depth == 0 and start is not None:
                out.append((kind, sig[start:i], start, i))
                start = None
        elif c == ":" and depth == 0:
            break                      # conclusion begins
    return out

def scan_file(path, rows, stats):
    try:
        L = open(path, encoding="utf-8").read().split("\n")
    except Exception:
        return
    incomment = 0
    for i, line in enumerate(L):
        # Track block-comment depth.  Module docstrings contain sentences like
        # "a companion theorem also places the endpoints", which DECL matches as
        # `theorem also` and whose URLs then parse as binders (r207).
        opens = line.count("/-"); closes = line.count("-/")
        was = incomment
        incomment = max(0, incomment + opens - closes)
        if was or opens > closes:
            continue
        m = DECL.match(line)
        if not m:
            continue
        stats["decls"] += 1
        # gather the declaration text until the top-level ':=' (signature) then body
        chunk, j, depth = [], i, 0
        while j < len(L) and j < i + 400:
            chunk.append(L[j])
            j += 1
            txt = "\n".join(chunk)
            if re.search(r':=(\s|$)', txt) and txt.count("(") <= txt.count(")"):
                break
        head = "\n".join(chunk)
        cut = head.rfind(":=")
        if cut == -1:
            continue
        sig = head[:cut]
        # body: from the ':=' to the next declaration / end
        # The body ends at the next column-0 COMMAND, not merely the next column-0 line.
        # This repo writes `theorem foo ... :=` / newline / `by` with `by` in column 0; a naive
        # column test captures an EMPTY body, so every binder looks unused and the tactic filter
        # never fires.  Four false positives in CofinalIdeal/Restrict.lean came from this (r207).
        CMD = re.compile(r'^(?:@\[|/-|theorem|lemma|def|abbrev|instance|structure|class|example|'
                         r'namespace|end|section|variable|open|attribute|private|protected|'
                         r'noncomputable|nonrec|deriving|macro|syntax|notation|import|set_option)\b')
        k = j
        while k < len(L):
            if L[k] and not L[k][0].isspace() and CMD.match(L[k]):
                break
            k += 1
        body = head[cut:] + "\n" + "\n".join(L[j:k])
        # Match a tactic as a TOKEN, not a substring.  `"order" in body.lower()` fires on
        # `Ordered`, `"trivial"` on `Nontrivial`, `"decide"` on `DecidableEq`, `"congr"` on
        # `congrArg` -- all of which DISQUALIFY a declaration that uses no such tactic, hiding
        # genuine findings.  Literals containing punctuation (`simp [*`, `exact?`) stay as
        # substring tests. (r210)
        if CTX_RE.search(body) or any(t in body for t in CTX_LIT):
            stats["ctx"] += 1
            continue
        groups = split_binders(sig[sig.index(m.group(2)) + len(m.group(2)):])
        expl = [g for g in groups if g[0] == "("]
        if not expl:
            continue
        stats["withbinder"] += 1
        for kind, inner, s, e in expl:
            if ":" not in inner:
                continue
            names, typ = inner.split(":", 1)
            if any(ch in names for ch in "()[]{}"):
                continue
            for nm in names.split():
                # a leading `_` is the author declaring the binder unused on purpose
                if not nm or nm.startswith("_") or not nm[0].isalpha():
                    continue
                rest_sig = sig[sig.index(m.group(2)) + len(m.group(2)) + e:]
                if occurs(nm, rest_sig) or occurs(nm, body):
                    continue
                rows.append((path, i+1, m.group(2), nm, typ.strip()[:60], m.group(1)))

def main():
    root = sys.argv[1]
    rows, stats = [], {"decls": 0, "withbinder": 0, "ctx": 0, "files": 0}
    for dp, _, fs in os.walk(root):
        for f in fs:
            if f.endswith(".lean"):
                stats["files"] += 1
                scan_file(os.path.join(dp, f), rows, stats)
    # A binder whose type is CLASS-HEADED is consumed by typeclass search and never named:
    # `epi_δ (h₂ : Subsingleton (F.H' n₁ S.X₂))` feeds the `_` in `isZero_of_subsingleton _`.
    # These are not findings.  Relational types (`= ≤ < ∈ ≠ ∣ ⊆`) cannot be instances, so they
    # are the only rows worth a human read.  (r207: this split is what took 15 hits to 0.)
    # NOTE (r209): this partition was tuned for Prop HYPOTHESES, where "no relation symbol"
    # is good evidence of a class.  It does not transfer to `def` parameters -- `(junk : ℕ)`
    # and `(dead : Type)` are DATA, not instances, and the rule suppressed 100% of the true
    # positives in the --defs control.  So suppression applies to theorems only; in --defs
    # mode a class-suspect row is MARKED, never hidden.
    REL = set("=≤<∈≠∣⊆⊂≥>∉∤")
    defs_mode = "--defs" in sys.argv
    def relational(r): return any(c in r[4] for c in REL)
    if defs_mode:
        real = [r for r in rows if relational(r) or r[5] in ("def", "abbrev")]
        susp = [r for r in rows if r not in real]
    else:
        real = [r for r in rows if relational(r)]
        susp = [r for r in rows if r not in real]
    for p, ln, decl, nm, typ, kind in real:
        # only a capitalised head could be a class; `(junk : ℕ)` is plainly data
        mark = "" if relational((p,ln,decl,nm,typ,kind)) or not (typ[:1].isascii()
                    and typ[:1].isupper()) else "?TC-check "
        print(f"{p}:{ln}\t{kind} {decl}\t{mark}({nm} : {typ})")
    if susp:
        print(f"\n# {len(susp)} class-headed binder(s) suppressed as local instances "
              f"(not findings); pass --all to see them.")
        if "--all" in sys.argv:
            for p, ln, decl, nm, typ, kind in susp:
                print(f"#   SUSPECT {p}:{ln}\t{kind} {decl}\t({nm} : {typ})")
    print(f"# FIRING CONTROL: {stats['files']} files, {stats['decls']} theorems scanned; "
          f"{stats['withbinder']} carry an explicit binder and survived the tactic filter; "
          f"{stats['ctx']} disqualified (context-consuming tactic). "
          f"hits={len(real)} (+{len(susp)} class-headed suppressed)",
          file=sys.stderr)

if __name__ == "__main__":
    main()
