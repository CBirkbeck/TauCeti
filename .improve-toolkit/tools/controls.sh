#!/usr/bin/env bash
# controls.sh -- run every instrument against its stored fixture and assert the EXPECTED ROWS.
#
# Counts are not enough: a patched tool can emit the right number of wrong rows.  Each check
# below names the declarations it expects, so a regression that swaps one finding for another
# fails here rather than silently corrupting a delta screen.
#
# Every instrument in this directory has been patched since its controls were written
# (`dupsig` twice, `deadprivate` three times), and r216 showed a patch can leave a file that
# parses and is wrong.  Run this after touching any instrument.
set -u
T="$(cd "$(dirname "$0")" && pwd)"
# Fixtures live beside this script, NOT in the session scratchpad.  Until r320 they lived only in
# /private/tmp/.../scratchpad, so 11 of the 17 checks would have vanished with the session and the
# suite would have kept printing a smaller "N passed" without saying anything had gone. An argument
# still overrides, for testing against a modified copy.
SP="${1:-$(cd "$(dirname "$0")/../fixtures" && pwd)}"
[ -d "$SP" ] || { echo "controls.sh: no fixture dir at $SP" >&2; exit 2; }
# Assert every fixture is present BEFORE running anything.  r320: deleting one fixture made its
# POSITIVE check fail but its NEGATIVE check pass -- vacuously, because `neg` sees empty output and
# finds nothing wrongly reported.  A missing fixture must abort, not quietly halve a check's value.
for d in r207-ctl r209-ctl r211-ctl r216-ctl r218-ctl r224-ctl r227-ctl r355-importnarrow-ctl r437-vacuousns-ctl r438-dupinproof-ctl r440-lintcand-ctl r442-strictscan-ctl r445-impliedscan-ctl r446-declinedguard-ctl r448-blockprof-ctl r451-threadread-ctl r453-docghost-ctl r491-stalequal-ctl r498-movedopens-ctl r499-parallelns-ctl r514-mathlibns-ctl r515-nscand-subtree-ctl r519-bodylint-ctl r527-nsslice-ctl r550-xsibling-ctl r551-nsbalance-ctl r552-deadpath-ctl r555-wrap100-ctl r555-rootns-ctl r564-stalequal-base-ctl r592-nsslice-base-ctl r593-parallelns-base-ctl r594-deadpath-base-ctl r600-rootns-nested-ctl r605-rootsurplus-ctl r606-decldiff-deroot-ctl r622-nsjump-ctl r625-rootedin-ctl r643-rootedin-suffix-ctl r646-nsjump-prose-ctl r637-dupsig-varctx-ctl; do
  [ -d "$SP/$d" ] || { echo "controls.sh: missing fixture $SP/$d -- refusing to run a partial suite" >&2; exit 2; }
done
# Results go to a FILE, not shell variables: every chk/neg below is invoked through a PIPE,
# so it runs in a subshell and any `pass=$((pass+1))` is discarded when that subshell exits.
# The first version of this script printed "0 passed, 0 failed" while all 11 checks passed --
# and its exit status was therefore success no matter what. A control suite that cannot fail
# is worse than none. (r237)
RES="$(mktemp)"; trap 'rm -f "$RES"' EXIT
chk() {  # chk <label> <expected-rows...> -- reads stdout on fd 0
  local label="$1"; shift
  local out; out="$(cat)"
  local missing=""
  for want in "$@"; do grep -q -- "$want" <<<"$out" || missing="$missing $want"; done
  if [ -z "$missing" ]; then printf '  PASS  %s\n' "$label"; echo P >> "$RES"
  else printf '  FAIL  %s -- missing:%s\n' "$label" "$missing"; echo F >> "$RES"; fi
}
python3 "$T/unusedscan.py"  "$SP/r207-ctl"          2>/dev/null | chk "unusedscan: dead hypotheses"        "tp_unused" "hdead" "hn"
python3 "$T/unusedscan.py"  "$SP/r209-ctl" --defs   2>/dev/null | chk "unusedscan --defs: dead params"     "tp_dead_param" "junk" "tp_dead_abbrev"
python3 "$T/deadprivate.py" "$SP/r211-ctl"          2>/dev/null | chk "deadprivate: dead + dotted-dead"    "tp_dead" "Foo.dotted_dead"
python3 "$T/deadprivate.py" "$SP/r216-ctl"          2>/dev/null | chk "deadprivate: transitive fixpoint"   "helper_only_used_by_dead" "dead_consumer" "dead_consumer_two"
python3 "$T/dupsig.py"      "$SP/r224-ctl"          2>/dev/null | chk "dupsig: same-file duplicate"        "dup_one" "dup_two"
python3 "$T/dupbinder.py"   "$SP/r227-ctl"          2>/dev/null | chk "dupbinder: repeated hypothesis"     "tp_dup" "tp_implicit_prop"
python3 "$T/redundantimport.py" "$SP/r218-ctl"      2>/dev/null | chk "redundantimport: public chain"      "RedundantPublic" "RedundantPlain"
# NEGATIVE assertions -- these must NOT appear
neg() { local label="$1"; shift; local out; out="$(cat)"
  local bad=""; for w in "$@"; do grep -q -- "$w" <<<"$out" && bad="$bad $w"; done
  if [ -z "$bad" ]; then printf '  PASS  %s\n' "$label"; echo P >> "$RES"
  else printf '  FAIL  %s -- wrongly reported:%s\n' "$label" "$bad"; echo F >> "$RES"; fi }
python3 "$T/deadprivate.py" "$SP/r211-ctl"          2>/dev/null | neg "deadprivate: spares attributed/used" "tn_attributed" "tn_used" "namespaced_used"
python3 "$T/dupbinder.py"   "$SP/r227-ctl"          2>/dev/null | neg "dupbinder: spares data binders"      "tn_data_same_type" "tn_distinct" "tn_instances"
python3 "$T/redundantimport.py" "$SP/r218-ctl"      2>/dev/null | neg "redundantimport: spares plain cover" "NotRedundant"
python3 "$T/unusedscan.py"  "$SP/r207-ctl"          2>/dev/null | neg "unusedscan: spares used/ctx"         "tn_used" "tn_ctx_omega" "tn_subscript"
# deadhave -- THREE modes, EIGHT suppressions, four merged PRs (#5727 #5730 #5733 #5740) and,
# until r318, NO control at all.  Its fixture is written here rather than stored, so these checks
# survive a lost scratchpad (the fixtures above do not -- a separate debt).
# NOTE: chk/neg match by SUBSTRING.  A negative token that is a substring of a positive
# expectation can never pass -- the first draft used `hd`, which occurs inside `hdead`, and the
# check failed against a correct instrument.  Keep fixture names mutually non-substring.
DH="$SP/r318-deadhave-ctl"
mkdir -p "$DH"; cat > "$DH/F.lean" <<'LEAN'
theorem tp_dead_have (a b : Nat) : a + b = b + a := by
  have hdead : a = a := rfl
  exact Nat.add_comm a b

theorem tn_used_have (a b : Nat) : a + b = b + a := by
  have hlive : a = a := rfl
  rw [Nat.add_comm]
  exact hlive ▸ rfl

theorem tn_ctx_omega (a b : Nat) : a + b = b + a := by
  have hscan : a = a := rfl
  omega

theorem tn_rwa (a b : Nat) (hq : a = b) : a + b = b + a := by
  have hrwa_consumed : a = b := hq
  rwa [Nat.add_comm]

theorem tn_class_typed (P : Type) : P = P := by
  have hproj : Projective P := inferInstance
  rfl

theorem tp_dead_set (a b : Nat) : a + b = b + a := by
  set c := a + b with hcdead
  exact Nat.add_comm a b

theorem tn_used_set (a b : Nat) : a + b = b + a := by
  set c := a + b with hcused
  rw [hcused]
  exact Nat.add_comm a b

theorem tp_dead_let (a b : Nat) : a + b = b + a := by
  let cdeadlet : Nat := a + b
  exact Nat.add_comm a b

def tn_stmt_let (a : Nat) :
    let cmirror := a + 1
    cmirror = a + 1 := by
  let cmirror := a + 1
  rfl
LEAN
python3 "$T/deadhave.py" "$DH" 1        2>/dev/null | chk "deadhave: dead named have"            "tp_dead_have" "hdead"
python3 "$T/deadhave.py" "$DH" 1        2>/dev/null | neg "deadhave: spares used/ctx/rwa/class"  "hlive" "hscan" "hrwa_consumed" "hproj"
python3 "$T/deadhave.py" "$DH" 1 --set  2>/dev/null | chk "deadhave --set: dead with-equation"   "hcdead"
python3 "$T/deadhave.py" "$DH" 1 --set  2>/dev/null | neg "deadhave --set: spares used equation" "hcused"
python3 "$T/deadhave.py" "$DH" 1 --let  2>/dev/null | chk "deadhave --let: dead let"             "cdeadlet"
python3 "$T/deadhave.py" "$DH" 1 --let  2>/dev/null | neg "deadhave --let: spares statement-let" "cmirror"
# importnarrow -- the narrowing step that turns `redundantimport`'s rows into DEFENSIBLE
# drops.  Its whole value is the use test, and the use test has exactly one way to go wrong:
# excluding a preceding dot.  In r355 that defect rated 29 live rows as findings (the real
# answer was 0), because Lean writes most uses dotted (`W.comap`, `Graphon.comap_apply`).
# The negative below is the regression guard; keep the two fixture names mutually
# non-substring (r318).
IN="$SP/r355-importnarrow-ctl"
python3 "$T/importnarrow.py" "$IN" < "$IN/rows.tsv" 2>/dev/null | chk "importnarrow: unreferenced drop" "UserUnref"
python3 "$T/importnarrow.py" "$IN" < "$IN/rows.tsv" 2>/dev/null | neg "importnarrow: spares dotted use" "UserDotted"
# vacuousns -- the instrument that caused a RED BUILD (r389, #5854: three wrappers removed whose
# siblings referenced them by short name).  Until r437 it had NO fixture and NO entry here: its
# docstring cited a "historical control" that was a one-time run against the live tree and existed
# only as a memory.  Writing the fixture immediately exposed a hole in the very check the red build
# had bought -- `short_sibling_refs` skipped the ENTIRE declaration line, so a short sibling
# reference sharing a line with its header (a one-line term body, or a binder type) was invisible.
# The four assertions below pin all four judgements the tool has to make.
VN="$SP/r437-vacuousns-ctl"
python3 "$T/vacuousns.py" "$VN" 2>/dev/null | chk "vacuousns: vacuous wrapper + docstring-only ref" "Warped" "Docmask"
python3 "$T/vacuousns.py" "$VN" 2>/dev/null | neg "vacuousns: spares load-bearing + self-declaring" "Loadbear" "Ownkid"

# dupinproof -- RANKING is the whole instrument.  r85 established that `score` (size*times, raw
# lines saved) is the wrong order for this lane, and r360/r361 chased exactly the rows r85 had
# declined because the tool still printed them first.  The fixture encodes that trap directly:
# `tn_highscore` has the HIGHEST score (42) but leaves a 125-line body at 100, while `tp_crosser`
# scores only 16 and takes a 56-line body to exactly 50.  A score sort would invert these.
DI="$SP/r438-dupinproof-ctl"
python3 "$T/dupinproof.py" "$DI" 20 2>/dev/null | grep '^CROSSES' | chk "dupinproof: marks the crossing row" "tp_crosser"
python3 "$T/dupinproof.py" "$DI" 20 2>/dev/null | grep '^CROSSES' | neg "dupinproof: spares high-score non-crossers" "tn_highscore" "tn_underbar"
python3 "$T/dupinproof.py" "$DI" 20 2>/dev/null | grep -E '^(CROSSES|   -   )' | head -1 | chk "dupinproof: crossing row ranks FIRST" "tp_crosser"

# lintcand -- the target picker.  Two defects in its first hour (r439): it matched the flagged
# declaration by SHORT NAME, so in a file declaring that name in two namespaces it measured the
# wrong theorem; and it costed rooting at a flat `_root_.` when a header written bare inside
# `namespace X` actually costs `_root_.X.`.  Both produced confident numbers about the wrong thing.
# Output is space-squeezed here so the assertions do not depend on column widths.
LC="$SP/r440-lintcand-ctl"
lc() { python3 "$T/lintcand.py" "$LC/base.tsv" "$LC" 2>/dev/null | tr -s ' '; }
lc | chk "lintcand: locates the flagged twin, not the short-name match" "Twin.lean:11"
lc | neg "lintcand: ignores the unflagged same-short-name sibling"     "Twin.lean:17"
lc | chk "lintcand: bare header costs the namespace prefix too"        "w= 52 bare= 0 qual= 0 nsflag= 1 Wrapped"
# `Guarded` legitimately has TWO flagged members in the fixture baseline, so nsflag=2 here --
# which is itself a check that the column counts the NAMESPACE, not the file.
lc | chk "lintcand: dot-notation and prose are not references"         "bare= 0 qual= 0 nsflag= 2 Guarded tn_dotOnly"
lc | chk "lintcand: a bare use IS a reference"                         "bare= 1 qual= 0 nsflag= 2 Guarded tn_bareUse"

# strictscan -- drove #5784 and #5794, and a false positive here proposes weakening a hypothesis
# that IS used strictly, i.e. a red build.  It had TWO defects and no control (r442):
#   1. `o = count('/--') + count('/-!') + count('/-')` double-counted an opener, because `/--`
#      CONTAINS `/-`.  A one-line `/-- text -/` scored o=2,c=1, latching the masker ON and deleting
#      the declaration that followed -- and nearly every public declaration has one.
#   2. `body` started at line `j`, the LAST signature line, dragging the binders in: `(h : a < b)`
#      contributed a bare `h`, so `all(u == '.le')` was False unless the signature happened to wrap.
# Together they held the screen to 2 findings on main where there are 6.
SS="$SP/r442-strictscan-ctl"
python3 "$T/strictscan.py" "$SS" 2>/dev/null | chk "strictscan: weakenable, incl. prose-masked" "tp_onlyLe" "tp_proseMasked"
python3 "$T/strictscan.py" "$SS" 2>/dev/null | neg "strictscan: spares strict use + opaque tactic" "tn_realStrict" "tn_opaqueTactic"

# impliedscan -- proposes REMOVING a hypothesis, so a false positive deletes something a proof
# needs.  Its soundness claim is that it only ever uses transitivity, and that a reported hypothesis
# is implied by a path "at least as strict"; `tn_weakChain` pins exactly that, since a `≤` chain
# must NOT license a `<` conclusion.  Every declaration here carries a ONE-LINE docstring, so the
# scan-count assertion doubles as a regression test for the r442/r444 masker bug.
IS="$SP/r445-impliedscan-ctl"
python3 "$T/impliedscan.py" "$IS" 2>/dev/null | chk "impliedscan: transitive + membership-expanded" "tp_transitive" "tp_membership"
python3 "$T/impliedscan.py" "$IS" 2>/dev/null | neg "impliedscan: spares independent + weak chain"  "tn_independent" "tn_weakChain"
# NOTE: impliedscan prints its firing control to STDOUT (no `file=sys.stderr`), unlike the other
# tools here -- so read stdout, not stderr.  Checking that interactively is misleading: this
# session's shell is zsh, whose MULTIOS DUPLICATES output under `2>&1 >/dev/null` so both
# streams appear to carry it; controls.sh runs under bash, where the redirect is POSIX and
# stderr comes back empty.  (r445)
python3 "$T/impliedscan.py" "$IS" 2>/dev/null | chk "impliedscan: masker lets one-line docstrings through" "4 declarations scanned"

# declinedguard -- the guard against re-proposing work already declined.  Its predecessor was
# `grep -c name ledger.md`, broken in BOTH directions; the negatives below are exactly that trap:
# `tn_measuredOnly` appears in a MEASUREMENT table and must come back `no-record`.  The positives
# cover three documented mechanisms: a row under a `Declines` heading carrying no decline
# vocabulary at all, an ELLIPSIS-truncated name, and a four-cell row outside any decline heading.
# `--ledger` was added at r446 purely so this could be controlled against a fixture rather than the
# live ledger.  Output is space-squeezed so the assertions do not depend on column padding.
DG="$SP/r446-declinedguard-ctl"
dg() { python3 "$T/declinedguard.py" --ledger "$DG/ledger.md" \
         tp_plainDecline tp_ellipsisDeclineName tp_wideDecline tn_measuredOnly 2>/dev/null | tr -s ' '; }
dg | chk "declinedguard: heading, ellipsis and wide-row declines" \
        "DECLINED tp_plainDecline" "DECLINED tp_ellipsisDeclineName" "DECLINED tp_wideDecline"
dg | neg "declinedguard: a measurement row is NOT a decline"      "DECLINED tn_measuredOnly"
# FAIL-SAFE: with no decline rows parsed it must REFUSE, not clear every name (the dangerous way).
python3 "$T/declinedguard.py" --ledger "$DG/empty.md" tn_plainMeasure 2>&1 \
  | chk "declinedguard: refuses to answer from an empty rule set" "refusing to answer"

# blockprof -- its `prime` count is quoted in every round's screen, and `dupinproof` imports it.
# The whole instrument is a four-way classification, and the thresholds are ORDER-DEPENDENT
# (`relocate` is tested before `assembly` before `prime`), so a reordering silently relabels rows
# rather than erroring.  One fixture proof per class, each sized to sit squarely inside its band:
#   prime    30 of 80  (25..60, and under 75% of the body)     relocate 32 of 40  (>= 75%)
#   assembly  8 of 60  (< 12)                                  partial  15 of 60 (12..24)
BP="$SP/r448-blockprof-ctl"
bp() { python3 "$T/blockprof.py" "$BP" 10 2>/dev/null | tr -s ' ' | awk '{print $1, $NF}'; }
bp | chk "blockprof: classifies all four bands" \
        "prime tp_prime" "relocate tn_relocate" "assembly tn_assembly" "partial tn_partial"
# `tn_overlap` (largest 11 of body 14) is the ONLY row that can tell the two orderings apart: it
# satisfies BOTH `largest < 12` and `largest >= 0.75*body`.  Without it the four rows above pass
# under either order, so the order-dependence claim above would be untested (r440's lesson: the
# injected failure must exercise the property asserted).  Shipped order gives `relocate`.
bp | chk "blockprof: relocate is tested BEFORE assembly" "relocate tn_overlap"

# threadread -- codifies two traps that bit a by-hand thread read:
#   r450: the pipeline EDITS a thread comment in place, so `created_at` dates the FIRST finding on
#         that rubric while the body is the LATEST.  Sorting by `created_at` can return older text.
#   r451: a thread is NOT rewritten when its rubric flips to approve, so thread text is useless for
#         state.  The SCOREBOARD is authoritative for state; the thread only carries the text.
# `--fixture` reads board.json / threads.json instead of the network (cf. declinedguard's --ledger).
TR="$SP/r451-threadread-ctl"
tr_() { python3 "$T/threadread.py" 1 --fixture "$TR" 2>/dev/null; }
tr_ | chk "threadread: current text, flagged as edited in place" "CURRENT finding text" "EDITED IN PLACE"
tr_ | neg "threadread: no superseded text, no board-green rubric" "SUPERSEDED older text" "tn_greenThread"
# r681: a block HALTS the run, so every rubric behind it comes back `absent` -- not judged on this
# head. Their threads still carry text from an older revision, and the old `state != green` test
# showed that text alongside the live block under one "unresolved" heading. #6093's `naming` thread
# was seven revisions stale; acting on it is work against a dead verdict, and any edit to a PR
# mid-review risks drawing new findings.
TRD="$SP/r681-threadread-deferred-ctl"
trd() { python3 "$T/threadread.py" 1 --fixture "$TRD" 2>&1; }
# NB: chk/neg feed these to plain `grep`, so `[...]` is a CHARACTER CLASS, not a literal -- keep
# expected rows bracket-free or they match nothing and the neg passes for the wrong reason.
trd | chk "threadread: a rubric deferred behind a block reads NOT-RUN, not a finding (r681)" \
          "NOT JUDGED ON THIS HEAD" "do NOT act): tn_deferred" \
          "LIVE (answer these): tp_blocking"
trd | neg "threadread: the deferred rubric is not listed as live work" \
          "LIVE (answer these): tn_deferred" "LIVE (answer these): tp_blocking, tn_deferred"

# docghost -- three-way, and only the NARROWED bucket is the #5579 defect:
#   advertised + declared in a file this one does NOT import  -> the defect
#   advertised + declared in an IMPORTED file                 -> legitimate
#   advertised + declared nowhere                             -> a stale name, a DIFFERENT defect
# The fixture is run with the SNAPSHOT root (not `<snap>/TauCeti`), which is the shape every other
# screen tool takes -- so it also pins the r453 auto-correction.  Handed the wrong root this tool
# built every module name as `TauCeti.TauCeti.X`, no import matched, and the live tree reported
# **118 findings instead of 4**.
DGH="$SP/r453-docghost-ctl"
dgh() { python3 "$T/docghost.py" "$DGH" 2>/dev/null | sed -n '/^# NARROWED/,/^$/p'; }
dgh | chk "docghost: reports the unreachable advertisement" "tp_unreachableName"
dgh | neg "docghost: spares imported and declared-nowhere names" "tn_reachableName" "tn_staleName"

# stalequal -- the #5953 defect: a rooting kills `TauCeti.<ns>.<short>`, and references still
# spelling it IN PROSE survive every code-level check.  The PR was green and had zero unqualified
# sibling references; three rubrics blocked on two docstring lines.  The fixture carries the real
# shape plus the three near-misses that must stay silent: a module IMPORT PATH sharing the prefix,
# an unmoved MEMBER of the same namespace, and a LONGER name containing the moved one's full text.
# A namespace-prefix grep reports all three -- it returned 10+ false hits on #5959.
SQ="$SP/r491-stalequal-ctl"
sq() { python3 "$T/stalequal.py" "$SQ" "$SQ/TauCeti/Moved.lean" 2>/dev/null; }
sq | chk "stalequal: the dead path, prose included"      "Consumer.lean:6" "Moved.lean:4"
sq | neg "stalequal: spares imports, kin, longer names"  "TnImportMod" "tn_unmoved_kin" "tp_danglerXtra"
# r493: the SECOND blocking round from this class.  r491 scanned snapshots built with
# `git archive <rev> TauCeti` and pronounced #5950 clean; `naming` then blocked on
# `web/examples/Examples.lean:45`, a CODE reference in a separate lake project the sandboxed build
# never compiles -- so CI was green on a name that cannot resolve.  Scan the REPOSITORY, not the
# subtree where the declarations happen to live.
sq | chk "stalequal: reaches outside TauCeti/"           "web/examples/Examples.lean:6"
python3 "$T/stalequal.py" "$SQ/TauCeti" "$SQ/TauCeti/Moved.lean" 2>&1 >/dev/null \
  | chk "stalequal: REFUSES the TauCeti/ subtree"        "no TauCeti/ directory"

# nsslice -- r527, the gap I told Chris was already covered.  `slice` and `parallelns` are both
# FILE-LOCAL: a probe that rooted 9 of `IsCoveringMap`'s 67 declarations passed both while leaving 58
# in eight other files.  This asks the cross-file question instead.  The fixture roots TWO namespaces
# in one file: `TpSplitNs`, which still has declarations in a second file, and `TnWholeNs`, which
# does not -- plus an unrelated nested namespace that is not this PR's business.
NSL="$SP/r527-nsslice-ctl"
python3 "$T/nsslice.py" "$NSL/TauCeti" "$NSL/TauCeti/TpRooted.lean" 2>/dev/null \
  | chk "nsslice: a namespace left half-rooted elsewhere"  "HALF-ROOTED" "TpSplitNs"
python3 "$T/nsslice.py" "$NSL/TauCeti" "$NSL/TauCeti/TpRooted.lean" 2>/dev/null \
  | neg "nsslice: spares whole moves and other namespaces"  "TnWholeNs" "TnOtherNs"

# bodylint anchor -- r519.  The first pattern demanded a literal `lint-dot-notation` immediately
# before the arrow, so it reported "no lint claim" for #5950, whose body writes
# `999 → 991 findings, 0 new`.  A tool written to catch STALE CLAIMS, defeated by a too-narrow
# anchor -- r458/r481/r487/r490/r494/r511 again, inside the fix.  The fixture carries BOTH phrasings
# this lane actually writes, plus a body full of unrelated numbers that must not match.
BL="$SP/r519-bodylint-ctl"
python3 "$T/bodylint.py" --claim "$BL/tp_prefixed.md" "$BL/tp_suffixed.md" "$BL/tn_prose_only.md" 2>/dev/null \
  | chk "bodylint: both claim phrasings parse"   "claim 985 -> 981" "claim 999 -> 991"
# The fixture is NOT named `tn_noclaim` -- `chk`/`neg` match by SUBSTRING, and the filename is
# echoed in the output, so "claim" inside the NAME would fail the check against a correct tool.
# This file warns about exactly that trap (the r320 `hd`/`hdead` note) and I walked into it.
python3 "$T/bodylint.py" --claim "$BL/tn_prose_only.md" 2>/dev/null \
  | neg "bodylint: prose numbers are not a claim"  "claim "

# nscand SUBTREE span -- r515.  `SheafOfModules.LocalGeneratorsData` reported "spans 1 file" while
# its SUBTREE spanned three: `…LocalGeneratorsData.IsInvertible` is a CHILD namespace that two other
# files declare into.  Rooting the parent alone would have split a structure's own API across files
# -- r499's defect with the pieces in different files.  The fixture puts two flagged declarations in
# `TpNs.TpSub` in one file and a child namespace `TpNs.TpSub.TpGrandchild` in another: the exact
# span is 1 and the answer must be 2.
NC="$SP/r515-nscand-subtree-ctl"
python3 "$T/nscand.py" "$NC" "$NC/findings.txt" 2>/dev/null \
  | chk "nscand: subtree span counts child namespaces" "SUBTREE spans 2" "TauCeti.TpNs.TpSub"
python3 "$T/nscand.py" "$NC" "$NC/findings.txt" 2>/dev/null \
  | neg "nscand: does not report the exact-namespace span" "SUBTREE spans 1"

# mathlibns -- r511: the ROOT-in-Mathlib question, which `nscand` says it cannot answer, so it was a
# grep every round -- and the grep was WRONG ON FIVE OF SIX candidates, in both directions.
# `^namespace A.B$` cannot see a namespace opened as nested `namespace A`/`namespace B`
# (RootPairing.InvariantForm: "not a namespace", truth 10 declarations), and a bare `^namespace B$`
# match says nothing about what ENCLOSES it (`Basis`: "found", truth `Module.Basis`).  The fixture
# carries both shapes plus the enclosing-namespace false positive.
MN="$SP/r514-mathlibns-ctl"
python3 "$T/mathlibns.py" "$MN" TpOuter.TpInner TpCompound.TpPart 2>/dev/null \
  | chk "mathlibns: finds nested and compound namespaces"  "ROOT" "TpOuter.TpInner" "TpCompound.TpPart"
python3 "$T/mathlibns.py" "$MN" TnLooksRoot 2>/dev/null \
  | neg "mathlibns: a nested name is not a root namespace"  "ROOT"

# parallelns -- r499, `api-design` on #5950: rooting `BialgHom` while `namespace BialgHomClass` kept
# `map_antipode` split ONE interface across two namespaces.  Neither instrument could raise it:
# `lint-dot-notation` never flags an instance-binder receiver (999->991 across that PR is exactly the
# eight BUNDLED theorems, the ninth counted zero), and r490's flagged/TOTAL filter asks about ONE
# namespace, so `BialgHom` 8/8 was true and still incomplete.  The fixture pairs the real shape with
# the two that must stay silent: a file that roots NOTHING, and one that roots with no nested block.
PN="$SP/r499-parallelns-ctl"
pn() { python3 "$T/parallelns.py" "$PN" 2>/dev/null; }
pn | chk "parallelns: rooted beside a nested sibling"   "TpSplit.lean" "FooClass"
pn | neg "parallelns: spares unrooted and un-nested"    "TnNoRoot" "TnTopLevelOnly" "TnOwnType"
# r501: a PRIVATE nested declaration is not an interface inconsistency -- nothing outside the
# file can name it.  Counting them made `GlobalSections.lean` (12 rooted / 1 nested, that one
# `private def restrictGlobal`) the top candidate and `EulerCharacteristic.lean` (11/9, ALL
# NINE private) the second.  Two of the three best rows were wrong.
pn | neg "parallelns: a private nested decl is not a row" "TnPrivateNested" "BazClass"

# movedopens -- r498, three CI cycles and two wrong diagnoses.  #5959 moved two lemmas whose binder
# says `Basis ι K B`; the SOURCE file resolves that through its `open Module` (Mathlib's type is
# `Module.Basis`).  The new file had no `open Module`, so the name AUTO-BOUND and the build said
# `Function expected at Basis / but this term has type ?m.5`.  I read `?m.5` as a missing import and
# spent two rounds on import chains that were correct both times.  `lint-dot-notation` says it
# outright -- "Watch for `open` and `variable` commands that must move with it" -- so make it
# mechanical.  The fixture carries the real shape plus the two that must stay silent: a name
# declared at Mathlib's ROOT, and one in a namespace the source does NOT open.
MO="$SP/r498-movedopens-ctl"
mo() { python3 "$T/movedopens.py" "$MO/mathlib" "$MO/src/Source.lean" 13 16 2>/dev/null; }
mo | chk "movedopens: the name that needs the source's open" "NEEDS \`open Module\`" "Basis"
mo | neg "movedopens: spares root names and unopened ones"   "TnRootType" "tn_other_ns_decl"

# CLASS GUARD (r497).  Lean identifiers are not ASCII.  An ASCII-only identifier class does not
# FAIL on `eval_Ψ₃_of_a₁_eq_zero` -- it matches `eval_` and stops, so the tool carries on with a
# WRONG NAME.  Found in ten tools at once (r494 caught it in `nscand` by an arithmetic tell: a
# namespace reported 26 flagged of 22 total, a ratio above 1).  Sweeping it recovered 18 invisible
# `strictscan` rows (`hν`, `hε` -- hypotheses are routinely named after their Greek variable) and
# removed a `dupstate` FALSE POSITIVE where `D₁`/`D₂`/`D₃` all truncated to `D`, making two
# unrelated statements look identical.
# The surviving ASCII forms are deliberate and do not match this guard: module paths
# (`[A-Za-z0-9_.]+`) and the Greek-aware `[A-Za-z_<Greek>][^\s(){}\[\]:]*` heads.
grep -l '\[A-Za-z_\]\[A-Za-z0-9_' "$T"/*.py 2>/dev/null | grep -v 'pubimport\.py' | sed 's|.*/||' \
  | neg "toolkit: no live tool uses an ASCII-only identifier class" ".py"
grep -l '(?<!\[A-Za-z0-9_\])\|(?!\[A-Za-z0-9_\])' "$T"/*.py 2>/dev/null | grep -v 'pubimport\.py' \
  | sed 's|.*/||' | neg "toolkit: no live tool uses an ASCII-only word boundary" ".py"

# CLASS GUARD (r444).  The docstring double-count -- `count('/--') + count('/-!') + count('/-')`,
# which counts one opener two or three times because `/--` CONTAINS `/-` -- was found in strictscan
# (r442) and then in THREE more tools it had been copy-pasted into: impliedscan, dupstate, nsshadow.
# A one-line `/-- text -/` latches the masker ON and deletes the declaration below it, so the effect
# is silent under-reporting: impliedscan was seeing 35,646 of 48,049 declarations (26% invisible).
# This guard fails if any LIVE tool re-introduces the idiom.  `pubimport.py` is exempt: it is
# RETIRED and must never be run, and is kept only as a record of a failed approach.
grep -l "count('/--')" "$T"/*.py 2>/dev/null | grep -v 'pubimport\.py' | sed 's|.*/||' \
  | neg "toolkit: no live tool re-introduces the docstring double-count" ".py"

# xsibling / siblingscan suffixes -- THE r550 RED BUILD, both halves.
# #6056 passed `prepush.sh` 14 ok / 0 failed and CI returned six errors. Two independent misses:
#   (a) `siblingscan` reduced `_root_.Wrap.Sib.foo` to its LAST component `foo`, while the
#       reference that breaks is the partially qualified `Sib.foo` -- and the search refuses a
#       name preceded by a dot, so the nested case was unreachable by construction;
#   (b) both `siblingscan` and `vacuousns` are FILE-LOCAL ON BOTH ENDS, so a name declared in
#       Decl.lean and used bare in Use.lean was outside their universe entirely.
# The fixture holds both, plus the three shapes that must NOT block: a docstring reference, an
# attribute name, and a tactic. Blocking on the attribute is not hypothetical -- it is the second
# defect in the same PR, where qualifying `@[ext]` produced `Unknown attribute`.
XS="$SP/r550-xsibling-ctl"
python3 "$T/xsibling.py" "$XS/TauCeti" HEAD "$XS/TauCeti/Use.lean" 2>/dev/null | grep '^BREAKS' \
  | chk "xsibling: cross-file and nested-suffix references" "tp_crossfile" "Inner.tp_nested"
python3 "$T/xsibling.py" "$XS/TauCeti" HEAD "$XS/TauCeti/Use.lean" 2>/dev/null | grep '^BREAKS' \
  | neg "xsibling: spares prose, attributes and tactics" "tn_docmask_target" '`ext`' "tn_header_name"
python3 "$T/xsibling.py" "$XS/TauCeti" HEAD "$XS/TauCeti/Use.lean" 2>/dev/null \
  | chk "xsibling: classifies the non-blocking shapes" "ATTRIBUTE" "TACTIC"
# r661: `_root_.TauCeti.Foo.bar` is rooted INTO TauCeti, so no wrapper is lost. The old guard read
# `'TauCeti.TauCeti' not in h` -- vacuously true -- and reported `TauCeti` itself as lost, turning
# every bare use of a `TauCeti.*` name into a BREAK. It fired on #6188 against code `origin/main`
# carries verbatim and builds.
python3 "$T/xsibling.py" "$XS/TauCeti" HEAD "$XS/TauCeti/Use.lean" 2>/dev/null | grep '^BREAKS' \
  | neg "xsibling: rooting INTO TauCeti is not a lost wrapper (r661)" "tn_into_tauceti"
python3 "$T/xsibling.py" "$XS/TauCeti" HEAD "$XS/TauCeti/Use.lean" 2>/dev/null | grep '^BREAKS' \
  | chk "xsibling: still finds the real breakage with that case present" "tp_crossfile" "Inner.tp_nested"
python3 "$T/siblingscan.py" "$XS/TauCeti/Use.lean" Wrap 2>/dev/null \
  | chk "siblingscan: nested suffix, not just the last component" "Sib.tp_samefile_nested"
python3 "$T/siblingscan.py" "$XS/TauCeti/Use.lean" Wrap 2>/dev/null \
  | neg "siblingscan: a header's own name is not a reference" "tn_local_header"

# nsbalance -- THE r551 RED BUILD, #6056's third defect and its second failing CI run.
# The wrapper conversion renamed "the next `end`" instead of the MATCHING one, so a nested
# `section Inner` was closed by a bare `end` and the wrapper's own `end Wrap` was left standing.
# Lean answers with `Missing name after 'end'` AND five follow-on errors -- overlapping instance
# parameters, unused section variables -- that look like real findings and are not.
# `Tn.lean` carries the two shapes that must NOT fire: `public section`, which green `main` leaves
# unclosed 4600 times, and `end A.B` closing a compound namespace.
NB="$SP/r551-nsbalance-ctl"
python3 "$T/nsbalance.py" HEAD "$NB/TauCeti/Tp.lean" 2>/dev/null \
  | chk 'nsbalance: the renamed end and its orphaned partner' "expected \`end Inner\`" "end Wrap"
python3 "$T/nsbalance.py" HEAD "$NB/TauCeti/Tn.lean" 2>/dev/null \
  | neg 'nsbalance: spares public section and compound end A.B' "UNBALANCED"

# deadpath -- THE r552 RED BUILD, #6065.  Two shapes no other screen can reach:
#   (a) a name OVER-QUALIFIED with the wrapper's name rather than the declaration's own.
#       `xsibling` hunts BARE references and refuses a name preceded by a dot, so an
#       over-qualified name is outside its universe by construction; `stalequal` tracks dead
#       `TauCeti.` paths, and this is a dead `Wrap.` one.
#   (b) an `open` of the namespace the PR has just EMPTIED -- and six of the nine such files in
#       #6065 were not in its diff, so that half has to walk the whole tree.
# The negatives matter as much: a correctly qualified name, a MATHLIB name, and a bare namespace
# token (`Wrap.Inner`, which is a namespace and not a declaration) must all stay silent.
DP="$SP/r552-deadpath-ctl"
python3 "$T/deadpath.py" "$DP/TauCeti" "$DP/Mathlib" "$DP/TauCeti/Use.lean" 2>/dev/null \
  | chk 'deadpath: over-qualified name and emptied namespace' "Wrap.tp_target" "TauCeti.Wrap"
python3 "$T/deadpath.py" "$DP/TauCeti" "$DP/Mathlib" "$DP/TauCeti/Use.lean" 2>/dev/null \
  | neg 'deadpath: spares correct, Mathlib and namespace tokens' "tn_correct" "mathlib_side" "\`Wrap.Inner\`" "rooted_side"

# rootns / wrap100 -- the extraction and width halves of the pipeline, neither of which had a
# control when they shipped in r554.
#
# `rootns` must root BOTH header shapes (a bare `theorem` inside `namespace Wrap`, and a dotted
# `theorem Wrap.x` written directly inside `namespace TauCeti` -- r547 shipped a script that matched
# only the first, rooted 37 of 67 and reported success), must match the wrapper's `end` BY STACK so
# a nested `section Inner` keeps its own `end Inner` (r551, a red build), and must refuse a file
# holding an anonymous `instance`, whose home would silently change when the wrapper goes.
RN="$SP/r555-rootns-ctl"
RND="$(mktemp -d)"; cp "$RN/TauCeti/Ok.lean" "$RN/TauCeti/Anon.lean" "$RN/TauCeti/Compound.lean" "$RND/"
python3 "$T/rootns.py" Wrap "$RND/Ok.lean" >/dev/null 2>&1
cat "$RND/Ok.lean" \
  | chk "rootns: roots both header shapes, keeps the nested end" \
        "_root_.Wrap.tp_bare" "_root_.Wrap.tp_dotted" "_root_.Wrap.tp_second_block" "end Inner"
cat "$RND/Ok.lean" | neg "rootns: retires the wrapper itself"    "^end Wrap$" "^namespace Wrap$"
python3 "$T/rootns.py" Wrap "$RND/Anon.lean" 2>/dev/null \
  | chk "rootns: refuses a block holding an anonymous instance" "anonymous instance"
# r561: a COMPOUND `namespace TauCeti.Wrap` is the wrapper too -- matching only a scope named
# exactly `Wrap` silently skipped three of AlgHom's eleven files (71 of 83 rooted). And a docstring
# line that merely BEGINS with a keyword is prose: `structure on its functor...` was rewritten into
# `structure _root_.Wrap.on its functor...`, which is r497 and r555 for the third time.
python3 "$T/rootns.py" Wrap "$RND/Compound.lean" >/dev/null 2>&1
cat "$RND/Compound.lean" \
  | chk "rootns: compound wrapper rooted and retired" "_root_.Wrap.tp_compound" "^section$"
cat "$RND/Compound.lean" \
  | neg "rootns: never rewrites a keyword inside a docstring" "structure _root_" "^namespace TauCeti.Wrap$"
cat "$RND/Anon.lean" | neg "rootns: leaves that file untouched"  "_root_"

# `wrap100` was WRONG THREE TIMES before it was right, and every one was caught by reading the
# output rather than by a check -- which is what this fixture is for. The three negatives ARE the
# three wrong rules: breaking at any space split `[NontriviallyNormedField` from its argument;
# breaking only at depth zero stranded `rw` alone above its own bracket; and not tracking comment
# depth split a `*` bullet inside `/-! ... -/` away from its URL (r497 all over again).
WP="$SP/r555-wrap100-ctl"
WPD="$(mktemp -d)"; cp "$WP/W.lean" "$WPD/"
python3 "$T/wrap100.py" "$WPD/W.lean" >/dev/null 2>&1
cat "$WPD/W.lean" \
  | chk "wrap100: breaks at a binder boundary and at a list comma" \
        "^    .AClassWithSeveralArguments K K K K K K K K K. : True := by" \
        "^    ContinuousLinearMap.toLinearMap_neg" "one hundred columns.(https"
cat "$WPD/W.lean" \
  | neg "wrap100: no split binder, no stranded rw, no split docstring" \
        "^    K\] : True" "^  rw$" "^  columns\](https" "^\*$"
python3 "$T/wrap100.py" "$WPD/W.lean" 2>/dev/null \
  | chk "wrap100: reports the line it cannot break" "tn_unbreakable\|someVeryLongNameIndeed"

# stalequal --base -- r564. Without `--base` the tool ASSUMES a rooted declaration used to be
# `TauCeti.<new name>`. #6093 renamed `HomotopyGroup.map_injective`, a top-level declaration whose
# old path had no `TauCeti.` prefix at all, and the assumption could not express it: CI caught the
# code reference, and a prose one would have survived to a reviewer. `--base` derives the stale set
# instead -- every full name a target declared at the base and no longer declares.
# The control needs real git history, so it builds a throwaway repo.
SB="$SP/r564-stalequal-base-ctl"
SBD="$(mktemp -d)"; cp -R "$SB/." "$SBD/"
( cd "$SBD" && git init -q . && git add -A && git -c user.email=c@x -c user.name=c commit -qm base )
BASEREV="$(cd "$SBD" && git rev-parse HEAD)"
sed -i.bak 's/^theorem map_injective : True := trivial$/theorem IsCoveringMap.map_injective : True := trivial/' \
  "$SBD/TauCeti/Base.lean" && rm -f "$SBD/TauCeti/Base.lean.bak"
( cd "$SBD" && python3 "$T/stalequal.py" --base "$BASEREV" . TauCeti/Base.lean 2>/dev/null ) \
  | chk 'stalequal --base: finds a renamed-away name with no TauCeti prefix' \
        "HomotopyGroup.map_injective" "Base.lean:8" "Base.lean:15"
( cd "$SBD" && python3 "$T/stalequal.py" . TauCeti/Base.lean 2>/dev/null ) \
  | neg 'stalequal without --base cannot see it' "HomotopyGroup.map_injective"

# decldiff -- r565. Reuses the r564 base fixture: renaming `map_injective` into
# `IsCoveringMap.map_injective` is not a rooting, so one name VANISHES and one APPEARS. The
# negative matters as much: a genuine rooting (`TauCeti.X.y` -> `X.y`) must leave NO residue, or
# the check fires on every PR it is meant to pass.
DDD="$(mktemp -d)"; cp -R "$SB/." "$DDD/"
( cd "$DDD" && git init -q . && git add -A && git -c user.email=c@x -c user.name=c commit -qm base )
DDREV="$(cd "$DDD" && git rev-parse HEAD)"
sed -i.bak 's/^theorem map_injective : True := trivial$/theorem IsCoveringMap.map_injective : True := trivial/' \
  "$DDD/TauCeti/Base.lean" && rm -f "$DDD/TauCeti/Base.lean.bak"
( cd "$DDD" && python3 "$T/decldiff.py" "$DDREV" TauCeti/Base.lean 2>/dev/null ) \
  | chk 'decldiff: a rename that is not a rooting leaves residue' \
        "VANISHED  .HomotopyGroup.map_injective" "APPEARED  .HomotopyGroup.IsCoveringMap.map_injective"
# and a REAL rooting leaves none
DDE="$(mktemp -d)"; cp -R "$SB/." "$DDE/"
( cd "$DDE" && git init -q . && git add -A && git -c user.email=c@x -c user.name=c commit -qm base )
DDEREV="$(cd "$DDE" && git rev-parse HEAD)"
sed -i.bak 's/^theorem to_root : True := trivial$/theorem _root_.Rooted.to_root : True := trivial/' \
  "$DDE/TauCeti/Base.lean" && rm -f "$DDE/TauCeti/Base.lean.bak"
( cd "$DDE" && python3 "$T/decldiff.py" "$DDEREV" TauCeti/Base.lean 2>/dev/null ) \
  | neg 'decldiff: a genuine rooting leaves no residue' "VANISHED" "APPEARED"

# CRASH GUARD (r540).  `chk`/`neg` read STDOUT ONLY.  A tool that prints the right rows and then
# dies on a NameError still PASSES every check -- which is exactly what happened: a half-applied
# edit left `stalequal` printing correct rows and then crashing on an undefined name, and the suite
# reported 63/0.  That is the empty-control family (r440/r448/r451) in a new disguise: the control
# was not vacuous, it was BLIND TO THE FAILURE MODE.  Assert the tool exits cleanly, not merely that
# its output looks right.
python3 "$T/stalequal.py" "$SQ" "$SQ/TauCeti/Moved.lean" 2>&1 >/dev/null \
  | neg "stalequal: exits without a traceback"            "Traceback"
python3 "$T/nsslice.py" "$NSL/TauCeti" "$NSL/TauCeti/TpRooted.lean" 2>&1 >/dev/null \
  | neg "nsslice: exits without a traceback"              "Traceback"
python3 "$T/parallelns.py" "$PN" 2>&1 >/dev/null \
  | neg "parallelns: exits without a traceback"           "Traceback"
python3 "$T/nscand.py" "$NC" "$NC/findings.txt" 2>&1 >/dev/null \
  | neg "nscand: exits without a traceback"               "Traceback"
python3 "$T/xsibling.py" "$XS/TauCeti" HEAD "$XS/TauCeti/Use.lean" 2>&1 >/dev/null \
  | neg "xsibling: exits without a traceback"             "Traceback"
python3 "$T/nsbalance.py" HEAD "$NB/TauCeti/Tp.lean" 2>&1 >/dev/null \
  | neg "nsbalance: exits without a traceback"            "Traceback"
python3 "$T/deadpath.py" "$DP/TauCeti" "$DP/Mathlib" "$DP/TauCeti/Use.lean" 2>&1 >/dev/null \
  | neg "deadpath: exits without a traceback"             "Traceback"
python3 "$T/rootns.py" Wrap "$RND/Ok.lean" 2>&1 >/dev/null \
  | neg "rootns: exits without a traceback"               "Traceback"
python3 "$T/wrap100.py" "$WPD/W.lean" 2>&1 >/dev/null \
  | neg "wrap100: exits without a traceback"              "Traceback"

# nsslice --base -- r592. The docstring always said "for every `_root_.X.y` declaration these files
# INTRODUCE", but the code collected every namespace holding a rooted declaration in the target
# files, absolute.  `Algebra/Module/Lattice.lean` has carried `_root_.Submodule.toAddSubgroup_
# submoduleOf` since before this lane existed, so a PR rooting LinearEquiv there was told
# "Submodule: 24 declaration(s) still in TauCeti.Submodule across 7 other file(s)" -- a defect
# report about main.  This is r551 one tool over.  The fixture pins BOTH sides: the pre-existing
# namespace must vanish from the report, and the genuinely half-rooted one must survive it.
NSB="$SP/r592-nsslice-base-ctl"
NSBD="$(mktemp -d)"; cp -R "$NSB/." "$NSBD/"
( cd "$NSBD" && git init -q . && git add -A && git -c user.email=c@x -c user.name=c commit -qm base )
NSBREV="$(cd "$NSBD" && git rev-parse HEAD)"
sed -i.bak 's/^theorem extendOfIsLattice : True := trivial$/theorem _root_.LinearEquiv.extendOfIsLattice : True := trivial/' \
  "$NSBD/TauCeti/Lattice.lean" && rm -f "$NSBD/TauCeti/Lattice.lean.bak"
( cd "$NSBD" && python3 "$T/nsslice.py" --base "$NSBREV" . TauCeti/Lattice.lean 2>/dev/null ) \
  | chk 'nsslice --base: reports the namespace THIS PR half-roots' \
        "HALF-ROOTED  LinearEquiv" "Elsewhere.lean"
( cd "$NSBD" && python3 "$T/nsslice.py" --base "$NSBREV" . TauCeti/Lattice.lean 2>/dev/null ) \
  | neg 'nsslice --base: silent about a namespace main had already rooted' "Submodule"
( cd "$NSBD" && python3 "$T/nsslice.py" . TauCeti/Lattice.lean 2>/dev/null ) \
  | chk 'nsslice without --base still shows the r592 false positive' \
        "HALF-ROOTED  Submodule" "HALF-ROOTED  LinearEquiv"

# parallelns --base -- r593. The row is a property of the FILE, and `prepush` filters rows to the
# PR's changed files, so a file that already had the shape on `main` indicts any PR that opens it.
# 24 files on green `main` carry a row. The suppression compares the SAME-namespace BALANCE, not
# the row text: rooting an UNRELATED namespace in the file moves the text (that namespace leaves
# the nested list) while the `[SAME Submodule: rooted 1 / nested 4]` claim stays entirely main's.
PLB="$SP/r593-parallelns-base-ctl"
PLBD="$(mktemp -d)"; cp -R "$PLB/." "$PLBD/"
( cd "$PLBD" && git init -q . && git add -A && git -c user.email=c@x -c user.name=c commit -qm base )
PLBREV="$(cd "$PLBD" && git rev-parse HEAD)"
( cd "$PLBD" && python3 "$T/parallelns.py" . 2>/dev/null ) \
  | chk 'parallelns without --base blames a row main already had' "SAME Submodule" "Lattice.lean"
# root an UNRELATED namespace: the row TEXT changes, the `SAME Submodule` claim does not
sed -i.bak 's/^theorem extendOfIsLattice : True := trivial$/theorem _root_.LinearEquiv.extendOfIsLattice : True := trivial/' \
  "$PLBD/TauCeti/Lattice.lean" && rm -f "$PLBD/TauCeti/Lattice.lean.bak"
( cd "$PLBD" && python3 "$T/parallelns.py" . --base "$PLBREV" 2>/dev/null ) \
  | neg 'parallelns --base: silent when only an unrelated namespace moved' "SAME Submodule"
# now root ONE of the four nested `Submodule` theorems: the claim itself changes, so it must fire
sed -i.bak 's/^theorem nested_one : True := trivial$/theorem _root_.Submodule.nested_one : True := trivial/' \
  "$PLBD/TauCeti/Lattice.lean" && rm -f "$PLBD/TauCeti/Lattice.lean.bak"
( cd "$PLBD" && python3 "$T/parallelns.py" . --base "$PLBREV" 2>/dev/null ) \
  | chk 'parallelns --base: fires when THIS PR moves the same-namespace balance' \
        "SAME Submodule" "Lattice.lean"

# deadpath --base -- r594. `prepush` says "every qualified name this PR writes resolves", but the
# scan was absolute: a reference already dead in a file blamed whoever next opened it. A 250-file
# sample of green `main` carries 11 rows across 5 files (an older snapshot: 95 across 33). Fourth
# instance of r551/r592/r593. The fixture pins both directions -- an untouched pre-existing dead
# path stays silent, and a dead path the PR ADDS still fires.
DPB="$SP/r594-deadpath-base-ctl"
DPBD="$(mktemp -d)"; cp -R "$DPB/." "$DPBD/"
( cd "$DPBD" && git init -q . && git add -A && git -c user.email=c@x -c user.name=c commit -qm base )
DPBREV="$(cd "$DPBD" && git rev-parse HEAD)"
( cd "$DPBD" && python3 "$T/deadpath.py" TauCeti Mathlib TauCeti/Dirty.lean 2>/dev/null ) \
  | chk 'deadpath without --base blames a dead path main already had' "Gone.vanished_lemma"
( cd "$DPBD" && python3 "$T/deadpath.py" --base "$DPBREV" TauCeti Mathlib TauCeti/Dirty.lean 2>/dev/null ) \
  | neg 'deadpath --base: silent about a pre-existing dead path' "Gone.vanished_lemma"
# a dead path this PR ADDS must still fire
printf '\ntheorem _root_.Gone.added_one : True := Gone.brand_new_lemma\n' \
  >> "$DPBD/TauCeti/Dirty.lean"
( cd "$DPBD" && python3 "$T/deadpath.py" --base "$DPBREV" TauCeti Mathlib TauCeti/Dirty.lean 2>/dev/null ) \
  | chk 'deadpath --base: still fires on a dead path THIS PR wrote' "Gone.brand_new_lemma"

# rootns nested wrapper -- r600. Both rewrite paths built the rooted name from the namespace
# ARGUMENT, dropping any wrapper between `TauCeti` and the target. `rootns LocalGeneratorsData` on a
# file opening `namespace TauCeti` / `namespace SheafOfModules` produced
# `_root_.LocalGeneratorsData.IsInvertible` -- a namespace Mathlib does not have -- and reported
# "3 declaration(s) rooted" (r598). The name is now computed from the declaration's own position.
RNN="$SP/r600-rootns-nested-ctl"
RNND="$(mktemp -d)"; cp "$RNN/TauCeti/Nested.lean" "$RNN/TauCeti/Plain.lean" "$RNND/"
python3 "$T/rootns.py" LocalGeneratorsData "$RNND/Nested.lean" 2>/dev/null \
  | chk 'rootns: keeps a wrapper between TauCeti and the target' \
        "ROOTED   _root_.SheafOfModules.LocalGeneratorsData.IsInvertible" \
        "ROOTED   _root_.SheafOfModules.LocalGeneratorsData.ofIso"
cat "$RNND/Nested.lean" \
  | neg 'rootns: never roots to the bare tail' "_root_.LocalGeneratorsData."
# the COMPOUND name (what `nscand` and `mathlibns` print) must select the same declarations
RNND2="$(mktemp -d)"; cp "$RNN/TauCeti/Nested.lean" "$RNND2/"
python3 "$T/rootns.py" SheafOfModules.LocalGeneratorsData "$RNND2/Nested.lean" 2>/dev/null \
  | chk 'rootns: a compound namespace argument selects the same declarations' \
        "ROOTED   _root_.SheafOfModules.LocalGeneratorsData.IsInvertible"
# and the ordinary shape is unchanged
python3 "$T/rootns.py" Wrap "$RNND/Plain.lean" 2>/dev/null \
  | chk 'rootns: declarations directly under TauCeti still root to the bare namespace' \
        "ROOTED   _root_.Wrap.tp_dotted" "ROOTED   _root_.Wrap.tp_bare"

# rootsurplus -- r605. `rootns` moves a whole `namespace` block, so a PR roots every member of the
# wrapper, not the subset the linter flagged. #6148 rooted 17 where 11 were flagged and `api-design`
# blocked the six -- all private, all general, none flagged. None of the other twelve checks asks
# this: `slice`, `decldiff` and `nsslice` are all satisfied by rooting too MUCH.
RSP="$SP/r605-rootsurplus-ctl"
RSPD="$(mktemp -d)"; cp -R "$RSP/." "$RSPD/"
( cd "$RSPD" && git init -q . && git add -A && git -c user.email=c@x -c user.name=c commit -qm base )
RSPREV="$(cd "$RSPD" && git rev-parse HEAD)"
python3 "$T/rootns.py" Wrap "$RSPD/TauCeti/Wrap.lean" >/dev/null 2>&1
( cd "$RSPD" && python3 "$T/rootsurplus.py" --base "$RSPREV" flagged.txt TauCeti/Wrap.lean 2>/dev/null ) \
  | chk 'rootsurplus: catches a declaration rooted but never flagged' "SURPLUS  \`Wrap.tp_unflagged\`"
( cd "$RSPD" && python3 "$T/rootsurplus.py" --base "$RSPREV" flagged.txt TauCeti/Wrap.lean 2>/dev/null ) \
  | neg 'rootsurplus: silent about the declaration that WAS flagged' "Wrap.tp_flagged\` is rooted"
# an empty flagged set must UNRUN, not call every rooted declaration surplus (r184/r552)
: > "$RSPD/empty.txt"
( cd "$RSPD" && python3 "$T/rootsurplus.py" --base "$RSPREV" empty.txt TauCeti/Wrap.lean 2>&1 >/dev/null ) \
  | chk 'rootsurplus: UNRUN on an empty flagged set' "UNRUN"

# decldiff de-rooting -- r606. This lane's PRs are sometimes asked to root LESS (#6148: six general
# private helpers had been rooted into `IsCompactOperator` without ever being flagged). The fix drops
# the prefix, and pairing only `TauCeti.X.y` -> `X.y` reported that as six VANISHED plus six APPEARED
# with the message "no rooting explains it" -- false, since a de-rooting explains it exactly.
DR="$SP/r606-decldiff-deroot-ctl"
DRD="$(mktemp -d)"; cp -R "$DR/." "$DRD/"
( cd "$DRD" && git init -q . && git add -A && git -c user.email=c@x -c user.name=c commit -qm base )
DRREV="$(cd "$DRD" && git rev-parse HEAD)"
python3 - "$DRD/TauCeti/Base.lean" <<'PYEOF'
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
s = s.replace("theorem Wrap.tp_rooted :", "theorem _root_.Wrap.tp_rooted :")     # a rooting
s = s.replace("private theorem Wrap.tp_derooted :", "private theorem tp_derooted :")  # a DE-rooting
open(p, 'w', encoding='utf-8').write(s)
PYEOF
( cd "$DRD" && python3 "$T/decldiff.py" "$DRREV" TauCeti/Base.lean 2>/dev/null ) \
  | chk 'decldiff: labels a de-rooting instead of calling it unexplained' \
        "DE-ROOTED \`TauCeti.Wrap.tp_derooted\` -> \`TauCeti.tp_derooted\`"
( cd "$DRD" && python3 "$T/decldiff.py" "$DRREV" TauCeti/Base.lean 2>/dev/null ) \
  | neg 'decldiff: no unexplained residue when both directions are paired' \
        "no rooting explains it"

# nsjump -- r622. `xqualify`/`deadfix` match a candidate by TAIL (r556); on #6188 that produced
# `Submodule.rationalizationEquiv` -> `LieSubalgebra.rationalizationEquiv`, which passed six gate
# runs over 29 rounds and failed the FIRST build. Three cases must be distinguished: a rooting
# (truncation) is fine, a rearrangement that re-adds the same name is fine, and a jump to an
# unrelated namespace is the defect.
NJ="$SP/r622-nsjump-ctl"
NJD="$(mktemp -d)"; cp -R "$NJ/." "$NJD/"
( cd "$NJD" && git init -q . && git add -A && git -c user.email=c@x -c user.name=c commit -qm base )
NJREV="$(cd "$NJD" && git rev-parse HEAD)"
python3 - "$NJD/TauCeti/Use.lean" <<'PYEOF'
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
s = s.replace("TauCeti.Submodule.foo", "Submodule.foo")                 # a ROOTING: truncation, fine
s = s.replace("theorem uses_jump : True := Submodule.rationalizationEquiv",
              "theorem uses_jump : True := LieSubalgebra.rationalizationEquiv")   # a JUMP: the defect
open(p, 'w', encoding='utf-8').write(s)
PYEOF
( cd "$NJD" && python3 "$T/nsjump.py" "$NJREV" TauCeti/Use.lean 2>/dev/null ) \
  | chk 'nsjump: catches a reference moved to an unrelated namespace' \
        "NS-JUMP  \`Submodule.rationalizationEquiv\` became \`LieSubalgebra.rationalizationEquiv\`"
( cd "$NJD" && python3 "$T/nsjump.py" "$NJREV" TauCeti/Use.lean 2>/dev/null ) \
  | neg 'nsjump: a rooting truncation is not a jump' "Submodule.foo\` became"
( cd "$NJD" && python3 "$T/nsjump.py" "$NJREV" TauCeti/Use.lean 2>/dev/null ) \
  | neg 'nsjump: an unchanged sibling is not a jump' "MulEquiv.trans_apply\` became"
# a ONE-LETTER head is a local binder, not a namespace (r623): `S.comp`, `W.polynomial.eval`.
# Auditing seven MERGED, CI-green PRs with the r622 cut produced three "jumps" that were all binders.
printf '\ntheorem uses_binder : True := S.comp\n' >> "$NJD/TauCeti/Use.lean"
( cd "$NJD" && git add -A && git -c user.email=c@x -c user.name=c commit -qm binder )
python3 - "$NJD/TauCeti/Use.lean" <<'PYEOF'
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
open(p, 'w', encoding='utf-8').write(s.replace("S.comp", "ContinuousLinearMap.isInvertible_equiv.comp"))
PYEOF
( cd "$NJD" && python3 "$T/nsjump.py" HEAD TauCeti/Use.lean 2>/dev/null ) \
  | neg 'nsjump: a one-letter binder head is not a namespace' "S.comp\` became"

# rootedin -- r625, from the r609 RED BUILD. `siblingscan`/`xsibling` model a wrapper being REMOVED;
# this is the dual -- the wrapper SURVIVES and a declaration is rooted out of it, so a bare reference
# inside the block stops resolving. Three cases: the bare reference is a breakage, a qualified one is
# fine, and a same-named declaration in the enclosing stack shadows the rooted one (not a breakage).
RI="$SP/r625-rootedin-ctl"
python3 "$T/rootedin.py" "$RI/TauCeti/Keep.lean" 2>/dev/null \
  | chk 'rootedin: a bare reference stranded by a surviving wrapper' \
        "bare \`tp_moved\` cannot reach \`Wrap.tp_moved\`"
python3 "$T/rootedin.py" "$RI/TauCeti/Keep.lean" 2>/dev/null \
  | neg 'rootedin: a qualified reference is not a breakage' "bare \`Wrap.tp_moved\`"
python3 "$T/rootedin.py" "$RI/TauCeti/Keep.lean" 2>/dev/null \
  | neg 'rootedin: a shadowing declaration in the stack is not a breakage' "\`tp_shadowed\` cannot reach"
python3 "$T/rootedin.py" "$RI/TauCeti/Keep.lean" 2>/dev/null \
  | neg 'rootedin: an attribute is not a reference (r550)' "Keep.lean:2[0-9]*  bare \`tp_moved\`.*attribute"
python3 "$T/rootedin.py" "$RI/TauCeti/Keep.lean" 2>/dev/null \
  | chk 'rootedin: still finds the real breakage with the attribute present' \
        "bare \`tp_moved\` cannot reach \`Wrap.tp_moved\`"

# dupsig variable context -- r637. r226 labelled cross-FILE collisions and r236 cross-NAMESPACE ones;
# both because identical signature TEXT can denote different things. A `section` with different
# `variable` lines does the same one level down: `Bochner/Gaussian/Basic.lean` states
# `posSemidef_cexp_neg_mul_sq_norm` privately under `[FiniteDimensional ℝ V]` and publicly without
# it -- the finite-dimensional case and the general one, byte-identical after the name.
DVC="$SP/r637-dupsig-varctx-ctl"
python3 "$T/dupsig.py" "$DVC" 2>/dev/null \
  | chk 'dupsig: labels a pair whose `variable` context differs' \
        "DIFFERENT \`variable\` CONTEXT" "tp_result_of_finiteDimensional"
# The complement: a real duplicate in ONE context must still be REPORTED, and unlabelled.
python3 "$T/dupsig.py" "$DVC" 2>/dev/null \
  | chk 'dupsig: still reports a real duplicate in one context' "tp_dup_one" "tp_dup_two"
# and a named `section` must not be mistaken for a namespace (r551 one tool over)
python3 "$T/dupsig.py" "$DVC" 2>/dev/null \
  | neg 'dupsig: a named section does not pop the namespace stack' "DIFFERENT NAMESPACES"

# rootedin -- r643, from #6406's RED BUILD, which this check watched in silence. It compared only
# the LAST component of a rooted name, so `LocalGeneratorsData.IsInvertible` under a surviving
# `namespace TauCeti.SheafOfModules` went unseen while the build failed with `Unknown identifier`.
# A check that reports ok on the defect it exists to catch is worse than no check: it was read, and
# believed, and the branch was pushed on its authority.
RIS="$SP/r643-rootedin-suffix-ctl"
python3 "$T/rootedin.py" "$RIS/TauCeti/Keep.lean" 2>/dev/null \
  | chk 'rootedin: a PARTIALLY QUALIFIED reference is stranded too (r643)' \
        "partially qualified \`Inner.tp_deep\` cannot reach \`Wrap.Inner.tp_deep\`"
python3 "$T/rootedin.py" "$RIS/TauCeti/Keep.lean" 2>/dev/null \
  | neg 'rootedin: the FULL name resolves at root and is not a breakage' \
        "\`Wrap.Inner.tp_deep\` cannot reach"

# nsjump -- r646. A DOCSTRING that names a declaration is prose, not a reference. r640 rooted
# `IsCoveringMap.isOpenQuotientMap` and the check reported a jump to
# `IsQuotientCoveringMap.isOpenQuotientMap` on the strength of ONE added docstring sentence naming
# Mathlib's companion theorem; no code in that PR ever wrote it. Backticks are the discriminator --
# a docstring writes `Foo.bar`, code never does. The second assertion is the guard that matters:
# masking prose must not blind the check to a real move.
NJP="$SP/r646-nsjump-prose-ctl"
NJPD="$(mktemp -d)"; cp -R "$NJP/." "$NJPD/"
( cd "$NJPD" && git init -q . && git add -A && git -c user.email=c@x -c user.name=c commit -qm base )
NJPREV="$(cd "$NJPD" && git rev-parse HEAD)"
python3 - "$NJPD/TauCeti/Use.lean" <<'PYEOF'
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
s = s.replace("theorem uses_code : True := CodeOld.widget",
              "theorem uses_code : True := CodeNew.widget")          # CODE move: a real jump
s = s.replace("theorem uses_prose : True := ProseOld.gadget",
              "/-- Compare `ProseNew.gadget`. -/\ntheorem uses_prose : True := trivial")  # PROSE only
s = s.replace("theorem uses_survivor : True := Keep.widget",
              "theorem uses_survivor : True := Fresh.widget Keep.widget")   # survivor re-emitted
open(p, 'w', encoding='utf-8').write(s)
PYEOF
( cd "$NJPD" && python3 "$T/nsjump.py" "$NJPREV" TauCeti/Use.lean 2>/dev/null ) \
  | neg 'nsjump: a backticked docstring mention is not a reference (r646)' "ProseNew.gadget"
( cd "$NJPD" && python3 "$T/nsjump.py" "$NJPREV" TauCeti/Use.lean 2>/dev/null ) \
  | chk 'nsjump: masking prose does not blind it to a real code move' \
        "NS-JUMP  \`CodeOld.widget\` became \`CodeNew.widget\`"
# A NAME ON BOTH SIDES OF THE DIFF DID NOT MOVE (r649). Rewriting a line re-emits every name on
# it, so the removed set fills with survivors; offering one as the ORIGIN of a jump reports the
# r556 defect on a line where it did not happen.
( cd "$NJPD" && python3 "$T/nsjump.py" "$NJPREV" TauCeti/Use.lean 2>/dev/null ) \
  | neg 'nsjump: a name present on both sides is not a jump source (r649)' \
        "\`Keep.widget\` became"

# prepush's own premise -- r664, from a red #6432.  Every screen in prepush.sh reads HEAD
# (`git diff BASE...HEAD`, `git archive HEAD`), so uncommitted work is invisible to all of them and
# the run reports on the PREVIOUS commit.  The rename that broke #6432 was gated while unstaged:
# `lint-dot-notation` archived HEAD, saw the OLD declaration names, and said `0 new`; CI saw the new
# names, un-grandfathered by a baseline that keys on name, and said `3 new`.
# A stale pass is worse than no pass, so the gate must refuse. Built as a throwaway git repo,
# because the defect is about git state rather than file content.
PPD=$(mktemp -d)
( cd "$PPD" && git init -q . && git config user.email c@e.invalid && git config user.name ctl \
    && mkdir -p TauCeti && printf 'theorem tp_a : True := trivial\n' > TauCeti/A.lean \
    && git add -A && git commit -qm base ) >/dev/null 2>&1
( cd "$PPD" && bash "$T/prepush.sh" HEAD 2>&1 ) \
  | neg "prepush: a clean tree is not refused (r664)" "UNCOMMITTED"
printf 'theorem tp_b : True := trivial\n' >> "$PPD/TauCeti/A.lean"
( cd "$PPD" && bash "$T/prepush.sh" HEAD 2>&1 ) \
  | chk "prepush: refuses to gate an uncommitted .lean change (r664)" "UNCOMMITTED"
rm -rf "$PPD"

# sweep's CI verdict -- r653, from a sweep that called a green PR red.  A commit's check-runs list
# carries EVERY run created for that SHA, so a re-dispatch leaves cancelled duplicates behind.
# #6188 read `RED:label` on a superseded `label` job while `sandboxed-build` was green and nothing
# had conclusion `failure`.  Judge each check by its LATEST run per name.  `ci_verdict` is pure so
# this runs without touching the network.
sweepv() { python3 -c "
import importlib.util, json, sys
spec = importlib.util.spec_from_file_location('sweep', '$T/sweep.py')
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
print('superseded:', m.ci_verdict([
  {'name':'label','started_at':'2026-01-01T00:00:00Z','status':'completed','conclusion':'cancelled'},
  {'name':'label','started_at':'2026-01-01T01:00:00Z','status':'completed','conclusion':'success'},
  {'name':'sandboxed-build','started_at':'2026-01-01T01:00:00Z','status':'completed','conclusion':'success'},
]))
print('realfail:', m.ci_verdict([
  {'name':'sandboxed-build','started_at':'2026-01-01T01:00:00Z','status':'completed','conclusion':'failure'},
]))
print('pending:', m.ci_verdict([
  {'name':'sandboxed-build','started_at':'2026-01-01T01:00:00Z','status':'in_progress','conclusion':None},
]))
print('lastcancelled:', m.ci_verdict([
  {'name':'sandboxed-build','started_at':'2026-01-01T01:00:00Z','status':'completed','conclusion':'cancelled'},
]))
print('noruns:', m.ci_verdict([]))
"; }
sweepv | chk "sweep: a superseded cancelled run is not a red build (r653)" "superseded: GREEN"
sweepv | chk "sweep: a real failure, a pending run and a live cancel still read red/pending" \
              "realfail: RED:sandboxed-build" "pending: PENDING:sandboxed-build" \
              "lastcancelled: RED:cancelled:sandboxed-build" "noruns: NO-RUNS"

# ---- r679: ghostref -- short references in files the PR does not touch ----------------------
# #6093's red build. `TauCeti.IsCoveringMap.fiberMap` was removed; `FiberFunctor.lean`, untouched
# by the PR and newly arrived on main, still said `IsCoveringMap.fiberMap` inside
# `namespace TauCeti.CoveringSpace`. stalequal prefilters on `TauCeti` and never saw the short
# spelling; deadpath only reads the PR's own files. The NEGATIVE matters as much: a removed name
# whose short form still resolves at root is not a ghost, or this fires on every move.
GRD="$(mktemp -d)"; cp -R "$SP/r679-ghostref/." "$GRD/"; GRML="$(mktemp -d)"
( cd "$GRD" && git init -q . && git add -A && git -c user.email=c@x -c user.name=c commit -qm base )
GRREV="$(cd "$GRD" && git rev-parse HEAD)"
# HEAD: both declarations leave Src.lean -- one has a root-level home, one does not.
grep -v '^theorem fiberMap\|^theorem keptElsewhere' "$GRD/TauCeti/Src.lean" > "$GRD/TauCeti/Src.new" \
  && mv "$GRD/TauCeti/Src.new" "$GRD/TauCeti/Src.lean"
grf() { ( cd "$GRD" && python3 "$T/ghostref.py" --base "$GRREV" . "$GRML" TauCeti/Src.lean 2>/dev/null ); }
grf | chk "ghostref: a short reference in an UNTOUCHED file to a removed name is a ghost (r679)" \
          "GHOST  IsCoveringMap.fiberMap" "TauCeti/Consumer.lean:6"
grf | neg "ghostref: a removed name whose short form still resolves at root is not a ghost" \
          "Shadowed.keptElsewhere"

# ---- r679: queuepos -- the fifth field, merge-queue membership -------------------------------
# #6093 read label=ready-to-merge / CI=GREEN / board=ON-HEAD / isDraft=false for 27 minutes after
# github-merge-queue[bot] had silently ejected it.  Only queue membership told them apart -- and
# only the ENQUEUE HISTORY tells an ejection (mine to fix) from a PR the bot never enqueued at all
# (#5950, blocked on a human review; refreshing it would achieve nothing).
qpos() { python3 -c "
import importlib.util as u
s=u.spec_from_file_location('q','$T/queuepos.py'); m=u.module_from_spec(s); s.loader.exec_module(m)
print('ejected:', m.queue_verdict('ready-to-merge', False, ever_enqueued=True))
print('neverq:', m.queue_verdict('ready-to-merge', False, ever_enqueued=False))
print('queued:', m.queue_verdict('ready-to-merge', True, 18, 'QUEUED'))
print('merging:', m.queue_verdict('ready-to-merge', True, 1, 'AWAITING_CHECKS'))
print('notready:', m.queue_verdict('awaiting-CI', False, ever_enqueued=True))
print('deep:', m.queue_verdict('ready-to-merge', True, 30, 'QUEUED'))
"; }
qpos | chk "queuepos: enqueued-then-absent is EJECTED, never-enqueued is not (r679)" \
            "ejected: EJECTED" "neverq: NEVER-QUEUED"
qpos | chk "queuepos: a deep queue position is not a fault, and an unready label is neither" \
            "queued: QUEUED:pos=18" "merging: MERGING:pos=1" "notready: NOT-READY" \
            "deep: QUEUED:pos=30"
# r679 again: `gh pr list` returns 30 rows by default and this repo has 30+ open PRs from other
# lanes, so the bare call reported on 2 of 4 improve/* PRs -- #6093 and #5950 fell off the end. A
# stranded PR is by definition an OLD one, i.e. exactly the row a default limit drops.
qlim() { python3 -c "
import importlib.util as u
s=u.spec_from_file_location('q','$T/queuepos.py'); m=u.module_from_spec(s); s.loader.exec_module(m)
c=m.pr_list_cmd()
print('haslimit:', '--limit' in c)
print('limit:', c[c.index('--limit')+1] if '--limit' in c else 'NONE')
print('big:', int(c[c.index('--limit')+1]) >= 100 if '--limit' in c else False)
"; }
qlim | chk "queuepos: the PR listing carries an explicit, generous limit (r679)" \
            "haslimit: True" "big: True"

p=$(grep -c P "$RES" || true); f=$(grep -c F "$RES" || true)
printf '\n  %d passed, %d failed\n' "$p" "$f"
[ "$f" -eq 0 ] && [ "$p" -gt 0 ]
