# Adversarial review 1: Idris/Lean docs-sweep plan

## Verdict

The plan is substantially sound: the frozen Lean matrix is a genuine
total, disjoint partition of all 215 source files (verified by
reconstructing index-mentioned ∪ 70-assigned = 215, no double-homes
beyond the three the plan already calls out); the Idris matrix is a
total, disjoint partition of all 77 modules with correct per-area
counts in the matrix; and the coverage script's path-normalization and
regex logic are correct end-to-end once it runs. But it does not run:
the script's very first executable line has a brace-balancing bug in
the `${1:?...}` expansion that makes `lang` always pick up a trailing
`}`, so every invocation falls through to the `*) exit 2` arm. The
gate the whole plan leans on is therefore dead on arrival. There is
also a self-contradiction in the Idris per-area counts between the
authoritative matrix and Task 4's step text, and a stale "ten `##`
workstreams" instruction in Task 2 that does not match the index.

## Findings

### 1. BLOCKER — coverage script never runs: brace bug in `${1:?...}`

**Problem.** Line 157 of the plan (the verbatim script body) is:

```bash
lang="${1:?usage: $0 {idris|lean}}"
```

Bash parameter expansion `${var:?word}` ends at the *first* unescaped
`}`. The `{idris|lean}` inside `word` supplies that first `}`, so the
expansion consumed is `${1:?usage: $0 {idris|lean}` (error word
`usage: $0 {idris|lean`) and the trailing `}` is appended as a literal
to the result. `lang` becomes `lean}` (or `idris}`), which matches
neither `idris)` nor `lean)` in the `case`, so control always reaches
`*) echo "usage..."; exit 2`. The gate can never print `OK` and can
never enumerate sources — Tasks 0/5/8/10 all fail spuriously.

**Evidence.**

```text
$ bash -c 'set -- lean; lang="${1:?usage: $0 {idris|lean}}"; \
    echo "[$lang]"; case "$lang" in lean) echo MATCH;; *) echo NO;; esac'
[lean}]
NO
```

```text
$ grep -n 'usage: \$0' .../2026-05-30-idris-lean-docs-sweep-plan.md
157:lang="${1:?usage: $0 {idris|lean}}"
```

With the line replaced by a `}`-free assignment, the rest of the
script works: on a fixture it correctly reported totality and flagged
a cross-file `MULTI-HOME`, and within-file duplicate links were deduped
as designed.

**Fix.** Remove the brace from the error word, e.g.

```bash
lang="${1:?usage: $0 idris|lean}"
```

or split the check off the expansion:

```bash
lang="${1:-}"
[ -n "$lang" ] || { echo "usage: $0 {idris|lean}" >&2; exit 2; }
```

This is the only defect in the script; all other mechanics
(`mapfile`, associative arrays, `realpath -m`, the
`./geb-lean/...`-vs-`./geb-lean/...` path agreement, the regex) are
correct on this environment (`bash 5.2.21`, `realpath` at
`/usr/bin/realpath`).

### 2. MAJOR — Idris per-area counts contradict the authoritative matrix

**Problem.** The Idris matrix freezes I2 = 14 and I8 = 13 (and the
sum 4+14+24+7+3+4+0+13+8 = 77 is stated explicitly). But Task 4's
step text says "**`polynomial-functors.md`** (I2, 16 modules)" and
"**`foundational-cats.md`** (I8, 11 modules)". Both contradict the
matrix; an engineer following Task 4 will look for 16 I2 modules and
11 I8 modules and find 14 and 13. Since the spec calls the matrix
"authoritative" and the check verifies *the matrix*, the Task-4
numbers are simply wrong (note 16+11 = 27 = 14+13, so the two errors
cancel in the total, which is how the 77 sum still holds — masking
the bug).

**Evidence.**

```text
$ # matrix I2 list word count
14
$ # matrix I8 list word count
13
$ grep -nE 'I2, [0-9]+ modules|I8, [0-9]+ modules' plan.md
553:- ... **`polynomial-functors.md`** (I2, 16 modules). ...
569:- ... **`foundational-cats.md`** (I8, 11 modules incl. `MLQuiv*`). ...
```

The matrix itself is correct: reconstructing every module under
`geb-idris/src` (excluding `/Test/`) and matching against the matrix's
nine area lists gives an exact 1:1 partition of all 77, no omissions,
no duplicates.

**Fix.** Change Task 4 Step 2 to "I2, 14 modules" and Step 8 to
"I8, 13 modules" to match the frozen matrix.

### 3. MAJOR — Task 2 Step 1 overstates the index workstream count

**Problem.** Task 2 Step 1 says "For each of the **ten** `##`
workstreams in `geb-lean/docs/index.md`, extract its `Source-tree
paths` `.lean` entries" and then maps ten slugs (including
`nno-arithmetic-topos` and `utilities`). The index has only eight
topical `##` workstreams (plus `## Directory structure` and
`## CSLib integration`, neither a source-area). There is no
NNO/arithmetic/topos workstream and no Utilities workstream to "seed
from": areas A9 and A10 are built *entirely* from the 70-file
"unmentioned" list, not from any index section. An engineer trying to
"extract source paths" for those two slugs from the index will find
nothing and may conclude the matrix is broken.

**Evidence.**

```text
$ grep -E '^## ' geb-lean/docs/index.md | grep -viE 'Directory|CSLib'
## Quivers, semicategories, acyclic categories
## Category-judgment encodings
## Polynomial / W- / M-types and PFunctors
## Profunctors and end machinery
## Internal-presheaf Grothendieck equivalence
## PshRelEdge and edge-of-presheaf machinery
## Tree calculus Phase 2
## K_sim hierarchy and ER <-> K_sim_2 equivalence
   (8 workstreams)
$ for f in NatArith NatNNO PSO PLO PSTONat ParanaturalTopos PresheafPRA; \
    do echo "$f: $(grep -c $f geb-lean/docs/index.md)"; done
NatArith: 0   NatNNO: 0   PSO: 0   PLO: 0
PSTONat: 0   ParanaturalTopos: 0   PresheafPRA: 0
```

All A9 files are absent from the index; all are explicitly in the
70-file list, so coverage is *not* lost — only the Task-2 instruction
is wrong.

**Fix.** Reword Task 2 Step 1 to "the eight topical `##` workstreams"
and state that the `nno-arithmetic-topos` and `utilities` areas are
seeded wholly from the unmentioned-file list in Step 2 (the
`K_sim hierarchy` heading maps to the `lawvere-er-ksim` slug). Drop
the implication that ten index workstreams exist.

### 4. MINOR — matrix totality and disjointness confirmed (positive)

**Problem.** None; this records the verification the attack brief
requested.

**Evidence.** The Lean union check:

```text
$ # distinct GebLean...lean paths mentioned anywhere in index
145
$ # the 70 explicit assignments (root aggregator as GebLean.lean)
70
$ # union, deduped
215
$ comm -23 all_source_215  union_215   # uncovered source files
(empty)
$ comm -13 all_source_215  union_215   # union entries not real sources
(empty)
```

145 index-mentioned + 70 explicit = 215 with no overlap and no
non-source entries; every index-mentioned path is a real file. The
only files double-listed across index workstreams are exactly the
three the plan calls out — no others:

```text
$ # per-path count of distinct ## sections mentioning it, >1 only
2  GebLean/ParanatAlg.lean              -> Polynomial | Profunctors
2  GebLean/Paranatural.lean             -> Polynomial | Profunctors
2  GebLean/Utilities/PolyCombinators.lean -> Polynomial | Tree calculus
```

So the plan's `PolyCombinators → A3-only`, `Paranatural`/`ParanatAlg`
→ A4-only reassignments are exactly the set needed for disjointness.
The Idris matrix likewise partitions all 77 modules exactly, and the
contested reassignments (`RopeCat`, `FinCatPRA`, `MLQuiv*` → I8)
correspond to real files under `LanguageDef/`. No action; this finding
exists only to confirm the matrices are trustworthy.

### 5. MINOR — root aggregator citation must be `../../GebLean.lean`, not `../../GebLean/GebLean.lean`

**Problem.** The convention says "visible text is the repo-relative
path" and the worked example is `GebLean/Polynomial.lean`. The root
aggregator's repo-relative path is `GebLean.lean` (it lives at
`geb-lean/GebLean.lean`, *not* `geb-lean/GebLean/GebLean.lean`). If an
author mechanically prepends `GebLean/` (as the surrounding A10 bullets
all do), the link `../../GebLean/GebLean.lean` resolves to
`./geb-lean/GebLean/GebLean.lean`, which is not in the source set:
that single file would show as both an UNLINKED source (`GebLean.lean`)
and a LINKED non-source target — a spurious double failure of
Assertion 1.

**Evidence.**

```text
$ ls geb-lean/GebLean.lean         # the real root aggregator
geb-lean/GebLean.lean
$ # script enumerates it as:
./geb-lean/GebLean.lean
$ # correct link from areas/ resolves to the same:
../../GebLean.lean -> ./geb-lean/GebLean.lean   (matches)
$ # the wrong path resolves to a non-source target:
../../GebLean/GebLean.lean -> ./geb-lean/GebLean/GebLean.lean  (no such file)
```

**Fix.** In Task 7 Step 9 (utilities/A10), state explicitly that the
root aggregator is cited as `` [`GebLean.lean`](../../GebLean.lean) ``
(one fewer path segment than the topical `Utilities/*` files).

### 6. MINOR — `_TEMPLATE.md` uses a non-standard doctoc sentinel

**Problem.** The frozen template embeds `<!-- START doctoc -->` /
`<!-- END doctoc -->`, but doctoc's recognized sentinel (used by every
existing doc and re-inserted by `doctoc`) is
`<!-- START doctoc generated TOC please keep comment here to allow
auto update -->`. Task 10 Step 3 runs `doctoc --dryrun --update-only`,
which only updates blocks carrying the full sentinel. The bare comment
in the template is harmless because each area-doc authoring step runs
`doctoc` on the finished doc (replacing the bare comment with the full
sentinel + TOC), but the template as written would not be picked up by
`--update-only`, and a copied-but-not-yet-doctoc'd doc could slip
through the final verify.

**Evidence.**

```text
$ grep -h 'START doctoc' geb-lean/docs/index.md
<!-- START doctoc generated TOC please keep comment here to allow auto update -->
$ grep -n 'START doctoc' plan.md
28:<!-- START doctoc generated TOC please keep comment here to allow auto update -->
105:<!-- START doctoc -->     # the template — bare form
```

**Fix.** Use the full sentinel pair in the template body so the
placeholder is doctoc-recognized from the start.

### 7. MINOR — jj "history-preserving move" phrasing is slightly incoherent

**Problem.** Task 6 Step 2 says to relocate notes "with `jj`
(history-preserving move; do not use raw `git mv`)". jj has no `mv`
subcommand; it tracks files by snapshotting the working copy, so a
relocation is just a filesystem `mv` that jj records on the next
snapshot — there is no jj move command to invoke, and jj does not
preserve per-file rename history the way the phrasing implies (it is
content-snapshot based). The instruction is *interpretable* (the real
point is "don't stage a `git mv`; let jj snapshot the move"), but as
written it could send an engineer hunting for `jj mv`.

**Evidence.**

```text
$ jj --help | grep -iE '^\s+(mv|move|rename)'
(no such subcommand)
```

**Fix.** Reword to: "Relocate with a plain `mv`; jj will record the
move on the next snapshot. Do not use `git mv` (the repo is
jj-colocated and we do not run mutating git)."

### 8. MINOR — coverage gate is not wired into CI; future drift uncatchable

**Problem.** The script lives at repo-root `docs/tools/`, outside the
CI markdown-lint scope (`geb-lean/**/*.md`), and nothing adds it to any
workflow; it is invoked only manually in Tasks 0/5/8/10. This matches
the spec's "best-effort, run by the final SDD task" framing, so it is
not a defect against the spec — but it means the totality/disjointness
invariant is enforced once at authoring time and never again. Worth a
one-line follow-up note so a later source-file addition that breaks
coverage is at least flagged as a known gap.

**Evidence.** CI lints only:

```text
$ grep -A2 'paths:' .github/workflows/markdown-lint.yml
  paths:
    - 'geb-lean/**/*.md'
    - 'geb-lean/.markdownlint-cli2.jsonc'
```

`docs/tools/check-area-coverage.sh` is neither `.md` nor under
`geb-lean/`, so CI never runs it.

**Fix.** Add a follow-up item (in the existing follow-ups doc) to wire
the coverage check into CI, or accept the one-time-gate scope
explicitly in the plan text.

## Spec-compliance spot checks (all pass)

- Calibration-doc-first gate: Task 3 ends with an explicit STOP for
  user approval. Confirmed.
- Dead-note sign-off gate: Task 6 Step 3 STOPs for sign-off before any
  deletion. Confirmed.
- Index slimming preserves framing + `## Directory structure`: Task 8
  Step 1 states both. Confirmed.
- Prose-only Idris area 7 contributes no `.idr` link: the script
  tolerates an area doc with zero matching links (empty associative
  array iterates cleanly under `set -u`). Confirmed.
- Provenance time-boxing and category-1/2-only Idris adaptation: Task 4
  preamble and Conventions reproduce the spec's bounded-search rule.
  Confirmed.
- All Task 3 read-targets exist on disk (the 14 A2 modules plus
  `novelty-analysis.md`). Confirmed.
- 51 top-level Lean notes to relocate, and `geb-lean/docs/research/`
  already exists. Confirmed.
- Lean/Idris share the slug `polynomial-functors`, but the check runs
  per-language over disjoint `areas/` directories, so no
  cross-contamination. Confirmed.
