#!/usr/bin/env python3
"""misplaced.py <mathlib-root> <file.lean>... -- `private` declarations that are general, not local.

THE ONE CLASS `prepush.sh` HAS NEVER CHECKED, and it has blocked twice (r535):

  #5959  api-design: two `private` tensor-product lemmas "mention only Mathlib tensor-product and
         basis APIs, require no centrality or simplicity, and are nevertheless `private`".
  #6022  api-design AND placement: `IsCompl.prod` "is a generic submodule-complement result with no
         totally-real hypotheses, so `private` does not justify placing it in `TotallyReal/Basic`".

Both were right, both cost a round, and `prepush` is silent on them by construction: its checks are
MECHANICAL -- dead paths, half-rooted namespaces, redundant imports, widths -- and none of them has
an opinion about whether a declaration belongs in the file it is in.

THE SIGNAL.  A `private` helper earns its place by being ABOUT the file's own subject.  So read the
declaration's STATEMENT ONLY -- header through the `:=` -- and ask whether it names anything the file
itself declares, or anything in the file's own namespace.  If the statement mentions only names from
elsewhere, the helper is general, and `private` is hiding reusable API rather than protecting a local
step.

WHY THE STATEMENT AND NOT THE PROOF.  A proof may use anything; that says nothing about where the
result belongs.  #6022's proof cites `Submodule.prod_inf_prod` and friends -- all Mathlib -- and its
statement mentions `Submodule` and `IsCompl` and nothing local.  The proof would have been noise.

MEASURED, AND **NOT GOOD ENOUGH TO GATE ON** (r536).  Against the three files whose verdicts are
known:

    #6022 `TotallyReal/Basic.lean`   1 row -- `IsCompl.prod`             TRUE  (both rubrics blocked)
    #5959 `CentralSimple/TensorProduct.lean`  1 row                      TRUE  (api-design blocked)
    #5995 `LegendreSymbol/Frobenius.lean`     4 rows                     ALL FALSE -- review
                                                                          objected to none of them

Two true positives against four false ones **in a single file**.  Those four helpers really do state
only Mathlib notions; what makes them local is a judgement about the proof they serve, which no
reading of the statement recovers.  So this is NOT wired into `prepush.sh`: r528's "a row is a
QUESTION" only works while rows are rare, and here they would be the norm on any file with private
helpers.  Run it by hand when a placement finding is plausible; do not let it gate.

A row is a QUESTION.  A genuinely local helper can be general in form (`natCard_quotient_under` in
`LegendreSymbol/Frobenius.lean` is arithmetic, stayed private, and passed review clean).  Judge it,
and if it stays, say why in the body.
"""
import sys, os, re

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?'
                  r'(?:public\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+)*private\s+'
                  r'(?:theorem|lemma|def|abbrev|instance)\s+'
                  r"(?:_root_\.)?([^\W\d][\w.'!?]*)")
ANY = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?'
                 r'(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|scoped\s+)*'
                 r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+'
                 r"(?:_root_\.)?([^\W\d][\w.'!?]*)")
IDENT = re.compile(r"(?<![\w.'])([A-Za-z_][\w']*)")

def statement(lines, i):
    """The declaration's statement: from its header to `:= by`/`:=`/`where`, exclusive."""
    out = []
    for L in lines[i:]:
        cut = re.split(r':=|\bwhere\b', L, 1)[0]
        out.append(cut)
        if re.search(r':=|\bwhere\b', L):
            break
        if len(out) > 30:
            break
    return '\n'.join(out)

def main():
    _mathlib, targets = sys.argv[1], sys.argv[2:]
    rows = nprivate = 0
    for t in targets:
        lines = open(t, encoding='utf-8').read().split('\n')
        own = set()
        for L in lines:
            m = ANY.match(L)
            if m:
                own.update(m.group(1).split('.'))
        # the file's own subject, from its module path: TauCeti/A/B/C.lean -> {A, B, C}
        subject = set(os.path.normpath(t)[:-5].split(os.sep)[1:])
        local = own | subject
        for i, L in enumerate(lines):
            m = DECL.match(L)
            if not m:
                continue
            nprivate += 1
            short = m.group(1).split('.')[-1]
            st = statement(lines, i)
            # Do NOT exclude the declaration's own dotted prefix: for
            # `AlgHom.IsArithFrobAt.sub_pow_mem` the prefix `IsArithFrobAt` is exactly the local
            # notion that makes it local, and excluding it flagged all four helpers in a file
            # where review objected to none.
            hits = {n for n in IDENT.findall(st) if n in local and n != short}
            if not hits:
                rows += 1
                print(f"GENERAL?  {t}:{i + 1}  private {m.group(1)}\n"
                      f"          statement names nothing local -- it may be reusable API kept "
                      f"private, which is what blocked #5959 and #6022")
    print(f"# FIRING CONTROL: {nprivate} private declaration(s) in {len(targets)} file(s); "
          f"{rows} whose STATEMENT names nothing the file declares and nothing from its own module "
          f"path. The proof is deliberately ignored -- it may cite anything. A row is a QUESTION: a "
          f"local helper can be general in form (`natCard_quotient_under` stayed private and passed "
          f"clean). Judge it, and if it stays, say why in the body.", file=sys.stderr)
    return 1 if rows else 0

if __name__ == '__main__':
    sys.exit(main())
