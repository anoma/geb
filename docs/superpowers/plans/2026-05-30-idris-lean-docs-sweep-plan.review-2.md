# Adversarial review 2 (confirmation): Idris/Lean docs-sweep plan

## Verdict

CONVERGED. All seven round-1 findings (1 BLOCKER, 2 MAJOR, 4 MINOR)
are resolved against the current plan text and the live repository.
The previously dead coverage script now runs end-to-end: extracted
verbatim from the plan and executed from the repo root, it reports 215
UNLINKED Lean sources (exit 1), 77 UNLINKED Idris sources (exit 1),
and a clean usage message for a bogus argument (exit 2) — no
fall-through to the `*)` arm on valid input. The Idris per-area counts,
the index-workstream count, the root-aggregator citation, the doctoc
sentinel, the jj move phrasing, and the CI-gate scope note are all
consistent with the authoritative matrices and the spec. The quick
consistency scan surfaced no new blocking inconsistency.

## Per-fix confirmation

### 1. BLOCKER (script brace bug) — CONFIRMED

The arg line is now `lang="${1:-}"` followed by an explicit
`[ -n "$lang" ] || { echo "usage: $0 {idris|lean}" >&2; exit 2; }`;
no `${1:?...{idris|lean}}` remains. Extracting the embedded script
(shebang → `exit "$status"`, 64 lines) to `/tmp/x.sh` and running it
from the repo root:

```text
$ bash /tmp/x.sh lean   # 215 UNLINKED listed, then:
== Assertion 2: disjointness (each file in <=1 area doc) ==
exit=1
$ bash /tmp/x.sh idris  # 77 UNLINKED listed, then:
== Assertion 2: disjointness (each file in <=1 area doc) ==
exit=1
$ bash /tmp/x.sh bogus
usage: /tmp/x.sh {idris|lean}
exit=2
```

UNLINKED-line counts verified mechanically: `lean` → 215, `idris` →
77. Both valid args reach the correct `case` arm and enumerate
sources; the bogus arm exits 2 with usage. Defect resolved.

### 2. MAJOR (Idris counts) — CONFIRMED

Task 4 Step 2 reads "`polynomial-functors.md` (I2, 14 modules)"
(line 563) and Step 8 reads "`foundational-cats.md` (I8, 13 modules
incl. …)" (line 579). Both now match the frozen matrix (I2 = 14,
I8 = 13) and the stated sum 4+14+24+7+3+4+0+13+8 = 77. No `16`/`11`
remnants.

### 3. MAJOR (index workstream count) — CONFIRMED

Task 2 Step 1 now says "The index has **eight** topical `##`
workstreams (plus `## Directory structure` and `## CSLib
integration`, which are not source areas)" and states that
`nno-arithmetic-topos` (A9) and `utilities` (A10) "have **no** index
workstream; they are built entirely from the unmentioned-file list in
Step 2." No "ten workstreams" phrasing remains anywhere in the plan.

### 4. MINOR (root aggregator citation) — CONFIRMED

Task 7 Step 9 specifies `` [`GebLean.lean`](../../GebLean.lean) ``
explicitly and warns against `../../GebLean/GebLean.lean` ("not a real
file and would fail the coverage check"), with the one-fewer-segment
rationale. The live script enumerates the root aggregator as
`./geb-lean/GebLean.lean`, matching the cited target.

### 5. MINOR (doctoc sentinel) — CONFIRMED

The `_TEMPLATE.md` body (line 105) uses the full sentinel
`<!-- START doctoc generated TOC please keep comment here to allow auto update -->`
paired with `<!-- END doctoc -->`. No bare `<!-- START doctoc -->`
remains.

### 6. MINOR (jj move phrasing) — CONFIRMED

Task 6 Step 2 now says "Relocate each into `geb-lean/docs/research/`
with a plain `mv`; jj records the move on its next snapshot (jj has no
`mv` subcommand …). Do not use `git mv` …." No `jj mv` or
"history-preserving move" phrasing remains.

### 7. MINOR (CI gate) — CONFIRMED

The coverage-check-script section (lines 145–152) now states the
script "lives at the repo root, outside the CI markdown-lint scope
(`geb-lean/**`), so it is a one-time authoring gate, not continuously
enforced; wiring it into CI … is a named follow-up (recorded in Task 9
/ `…-followups.md`)." This acknowledges the one-time-gate scope and
the CI follow-up.

## New-issue consistency scan

No genuinely new blocking inconsistency found. The two matrices remain
internally consistent (Lean 215, Idris 77; slug names match across
matrices, `_coverage.tsv` values, area-doc filenames, and the
filename-keyed check), the disjointness reassignments are unchanged,
and the STOP gates (Task 3, Task 6) are intact.
