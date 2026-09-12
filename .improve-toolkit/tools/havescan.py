#!/usr/bin/env python3
"""havescan.py <dir> <min_block_lines>

Find `have <name> : <type> := by ...` steps sitting at a proof's BASE indentation
whose proof block is large.  Such a step is a lemma that already has its statement
written down -- the cleanest possible extraction.

Round 110's finding: blockprof's `prime` verdict cannot distinguish a genuine
lemma-in-a-have-costume from a `by_cases` case-arm or an iff-direction, because all
three "dominate the body without swallowing it".  What actually predicts a clean
extraction is:
  (a) the statement is already explicit  -> the `have` has a type ascription, and
  (b) it leans on few EARLIER-BOUND locals -> few hypotheses to thread into a lemma.

So for each candidate we report `deps`: how many names bound earlier in the same
proof (by have/obtain/intro/set/let/rcases/rintro) actually occur in the candidate's
own text.  deps=0 means it depends only on the theorem's own binders and global
lemmas: lift it and it stands alone.

Counts are CHARACTER-based (unicode-safe), never bytes.
"""
import re, sys, os

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*'
    r'(theorem|lemma|def|instance|abbrev|example)\b')
STOP = re.compile(r'^(?:@\[|/--|/-!|--|open\b|namespace\b|end\b|section\b|variable\b|'
                  r'import\b|universe\b|attribute\b|local\b|set_option\b|'
                  r'private\b|protected\b|noncomputable\b|theorem\b|lemma\b|def\b|'
                  r'instance\b|abbrev\b|example\b|structure\b|inductive\b|class\b|'
                  r'deriving\b|macro\b|syntax\b|notation\b|declare\b|suppress\b)')
IDENT = re.compile(r"[^\W\d][\w'!?]*")
# a `have foo : ...` step (named, with an explicit type ascription)
HAVE = re.compile(r"^have\s+([^\W\d][\w'!?]*)\s*:(?!=)")
# names bound by a step, so later candidates can be scored against them
BINDERS = re.compile(r"^(?:have|obtain|intro|rintro|set|let|rcases|cases|induction)\b")

def indent(line):
    n = 0
    for ch in line:
        if ch == ' ': n += 1
        elif ch == '\t': n += 2
        else: break
    return n

def bound_names(text):
    """names a binder step introduces (approximate, deliberately generous)"""
    out = set()
    m = re.match(r"^have\s+([^\W\d][\w'!?]*)", text)
    if m: out.add(m.group(1)); return out
    m = re.match(r"^(?:set|let)\s+([^\W\d][\w'!?]*)", text)
    if m: out.add(m.group(1)); return out
    # obtain/intro/rintro/rcases-with: take every identifier in the binder part
    head = text.split(':=')[0]
    if re.match(r"^(?:obtain|intro|rintro)\b", head):
        out |= set(IDENT.findall(head)[1:])
    elif re.match(r"^(?:rcases|cases|induction)\b", head) and ' with ' in head:
        out |= set(IDENT.findall(head.split(' with ',1)[1]))
    return out

def profile_file(path, minblk):
    try:
        lines = open(path, encoding='utf-8').read().split('\n')
    except Exception:
        return []
    out, i = [], 0
    while i < len(lines):
        if indent(lines[i]) == 0 and DECL.match(lines[i]):
            decl_start = i
            m = DECL.match(lines[i])
            after = lines[i][m.end():].strip()
            dname = after.split()[0].rstrip(':') if after else '?'
            j, by_line = i, None
            while j < len(lines) and j < decl_start + 400:
                if re.search(r':=\s*by\b', lines[j]): by_line = j; break
                if j > decl_start and indent(lines[j]) == 0 and STOP.match(lines[j]): break
                j += 1
            if by_line is None:
                i += 1; continue
            k, body = by_line + 1, []
            while k < len(lines):
                s = lines[k]
                if s.strip() and indent(s) == 0 and STOP.match(s): break
                body.append(s); k += 1
            while body and not body[-1].strip(): body.pop()
            nonblank = [s for s in body if s.strip()]
            if nonblank:
                base = min(indent(s) for s in nonblank)
                # split into base-indent blocks, tracking earlier-bound names
                blocks, cur, seen = [], [], set()
                for off, s in enumerate(body):
                    if s.strip() and indent(s) == base:
                        if cur: blocks.append(cur)
                        cur = [(off, s)]
                    elif cur: cur.append((off, s))
                if cur: blocks.append(cur)
                for b in blocks:
                    txt = b[0][1].strip()
                    hm = HAVE.match(txt)
                    size = len([x for _, x in b if x.strip()])
                    if hm and size >= minblk:
                        blob = '\n'.join(x for _, x in b)
                        ids = set(IDENT.findall(blob))
                        deps = sorted(seen & ids)
                        out.append(dict(path=path, line=by_line + 1 + b[0][0] + 1,
                                        decl=dname, have=hm.group(1), size=size,
                                        body=len(nonblank), deps=deps,
                                        stmt=txt[:90]))
                    seen |= bound_names(txt)
            i = k
        else:
            i += 1
    return out

VENDORED = re.compile(r'vendored from', re.I)


def is_vendored(path):
    """A file the project vendors from an upstream PR is scheduled for deletion, so
    restructuring it diverges the copy from upstream and makes the eventual
    migrate-and-delete a manual diff.  Round 115: TauCeti PR #2053 was closed by the
    owner for exactly this, after a full analysis had already been spent on it --
    'my mistake was procedural: I ran the contention pre-flight but did not check the
    file's own docstring for a vendoring notice before starting.'  146 of 4203 files
    (1 in 29) carry the notice, so this is a routine hazard, not a rare one."""
    try:
        with open(path, encoding="utf-8") as f:
            return bool(VENDORED.search(f.read(4000)))
    except OSError:
        return False


root, MINBLK = sys.argv[1], int(sys.argv[2])
res = []
skipped = []
for dp, _, fns in os.walk(root):
    for fn in fns:
        if fn.endswith('.lean'):
            fp = os.path.join(dp, fn)
            if is_vendored(fp):
                skipped.append(fp)
                continue
            res += profile_file(fp, MINBLK)
res.sort(key=lambda r: (len(r['deps']), -r['size']))
for r in res:
    print(f"deps={len(r['deps']):2d} size={r['size']:3d} body={r['body']:3d} "
          f"{r['path']}:{r['line']} {r['decl']} :: have {r['have']}  [{','.join(r['deps'])}]")
print(f"# vendored files skipped={len(skipped)}", file=sys.stderr)
for s in skipped:
    print(f"#   VENDORED-SKIP {s}", file=sys.stderr)
print(f"# total={len(res)} deps0={sum(1 for r in res if not r['deps'])} "
      f"deps<=1={sum(1 for r in res if len(r['deps'])<=1)}", file=sys.stderr)
