# Idris-2 and Lean documentation-sweep Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Author overview-level documentation for the Idris-2 and Lean
codebases — per-area documents under each `docs/areas/`, indexed by a
slimmed `docs/index.md` — so a reader starting at the root `README.md`
sees what is implemented, how it fits together, and each headline
result's provenance, with links down to source.

**Architecture:** One shared doc template; two parallel execution
tracks (Idris green-field, Lean audit-and-extend). Coverage is enforced
mechanically by a two-assertion link-check (totality + per-document
disjointness) over a frozen file→area matrix. No source code is edited;
only Markdown under the two `docs/` trees and one helper script.

**Tech Stack:** Markdown, `markdownlint-cli2`
(`geb-lean/.markdownlint-cli2.jsonc`), `doctoc`, `bash`, `jj`
(colocated). Online research (`WebSearch`/`WebFetch`,
`leansearch`/`loogle`) for provenance.

**Spec:** `docs/superpowers/specs/2026-05-30-idris-lean-docs-sweep-design.md`
(converged through five adversarial-review rounds).

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Conventions for every task](#conventions-for-every-task)
- [Frozen artifacts](#frozen-artifacts)
  - [The doc template](#the-doc-template)
  - [The coverage-check script](#the-coverage-check-script)
  - [Lean area matrix](#lean-area-matrix)
  - [Idris area matrix](#idris-area-matrix)
  - [Contested boundaries (for reviewer attention)](#contested-boundaries-for-reviewer-attention)
  - [Parallel-formulation seed clusters](#parallel-formulation-seed-clusters)
- [Task 0: Tooling and baseline](#task-0-tooling-and-baseline)
- [Task 1: Idris partition matrix and import-graph note](#task-1-idris-partition-matrix-and-import-graph-note)
- [Task 2: Lean partition matrix](#task-2-lean-partition-matrix)
- [Task 3: Template + calibration area doc (Lean L-Phi)](#task-3-template--calibration-area-doc-lean-l-phi)
- [Task 4: Idris area documents](#task-4-idris-area-documents)
- [Task 5: Idris index assembly + coverage gate](#task-5-idris-index-assembly--coverage-gate)
- [Task 6: Lean research-note relocation + dead-note sign-off](#task-6-lean-research-note-relocation--dead-note-sign-off)
- [Task 7: Lean area documents](#task-7-lean-area-documents)
- [Task 8: Lean index slim + coverage gate](#task-8-lean-index-slim--coverage-gate)
- [Task 9: Cross-cutting pass (README, clusters, provenance collation)](#task-9-cross-cutting-pass-readme-clusters-provenance-collation)
- [Task 10: Final gate and holistic review](#task-10-final-gate-and-holistic-review)
- [Self-review against the spec](#self-review-against-the-spec)

<!-- END doctoc -->

## Conventions for every task

These apply to all authoring tasks; they are not repeated per step.

- **Source is authoritative.** Open each module and read its top-level
  declarations (`def`/`theorem`/`structure`/`inductive`/`instance` and,
  for Idris, top-level definitions and `data`) before writing its
  bullet. Confirm any name carried from existing prose still exists.
- **Depth budget.** One to three sentences per module; name at most the
  one to three headline declarations (those another module imports, or
  that state the area's headline result); never list intermediate
  lemmas. Pure re-export/index modules get a one-line aggregator note
  and no declaration list.
- **Citation syntax (load-bearing for the check).** Cite every source
  file as a relative Markdown link whose visible text is the
  repo-relative path, from a doc in `docs/areas/`:
  `` [`GebLean/Polynomial.lean`](../../GebLean/Polynomial.lean) `` and
  `` [`LanguageDef/PolyCat.idr`](../../src/LanguageDef/PolyCat.idr) ``.
  Do not cite a coverage-counted source file in backticks-without-link.
- **Provenance.** For each headline declaration, add a one-line tag of
  the form `Provenance: <category> — <citation>; searched <YYYY-MM-DD>,
  scope <list>.` Time-box the search (the ordered targets in the spec,
  first decisive hit wins, otherwise a bounded handful of queries per
  axis); on exhaustion write `Provenance: unverified (searched ...,
  scope ...)`. Idris docs use categories 1–2 plus Lean cross-links
  only.
- **Markdown discipline.** Repo-relative internal links; ATX headers;
  prose wrapped to match the surrounding docs; fenced code with a
  language tag; a doctoc TOC on any doc with more than one `##`.
  Run the linter on touched files before each commit:
  `npx markdownlint-cli2 --config geb-lean/.markdownlint-cli2.jsonc <files>`.
- **Commits via `jj`.** This repo is jj-colocated; do not run mutating
  `git`. After staging conceptually, set the change description with
  `jj describe -m "<msg>"` and start the next with `jj new`. End commit
  messages with the `Co-Authored-By` trailer. One area document per
  commit.
- **No source edits.** If authoring reveals a code problem, note it in
  `docs/superpowers/plans/2026-05-30-idris-lean-docs-sweep-followups.md`
  (create on first need); do not edit `.lean`/`.idr`.

## Frozen artifacts

### The doc template

Task 3 writes this verbatim to **both**
`geb-idris/docs/areas/_TEMPLATE.md` and
`geb-lean/docs/areas/_TEMPLATE.md`. Every area document follows it.

````markdown
# <Area title>

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- END doctoc -->

## Purpose

<One or two sentences: what this area is and why it exists in Geb.>

## Mathematical context

<The known mathematics this area formalises/implements, with external
references where helpful.>

## Modules

- [`<repo/relative/path>`](<../../relative/path>) — <one-line role>.
  <Up to three sentences naming the 1–3 headline declarations.>
  Provenance: <category> — <citation>; searched <date>, scope <list>.

## Alternative formulations

<Present only when this area, or the codebase across areas, formulates
one concept more than once. Lead with the single shared concept; then
present the formulations as variations of that one concept (artifacts
of exploring for a preferred form), naming each formulation, its
module, and the respect in which it differs. Other area docs link here
rather than restating.>

## Dependencies

<Which other areas this one builds on, as links to their area docs.>

## Pointers

<Lean: relocated research notes and docs/superpowers/specs entries
relevant to the area. Idris: development status where it aids the
reader.>
````

`_TEMPLATE.md`, `_coverage.tsv`, and any `_`-prefixed file are skipped
by the coverage check (it scans non-`_` `*.md` only).

### The coverage-check script

Task 0 writes this verbatim to `docs/tools/check-area-coverage.sh` and
`chmod +x` it. It is run per language in Tasks 5, 8, and 10. It lives
at the repo root, outside the CI markdown-lint scope (`geb-lean/**`),
so it is a one-time authoring gate, not continuously enforced; wiring
it into CI so a later source-file addition cannot silently break
coverage is a named follow-up (recorded in Task 9 /
`…-followups.md`).

```bash
#!/usr/bin/env bash
# Usage: docs/tools/check-area-coverage.sh {idris|lean}
# Asserts (1) the set of source files linked from <lang>/docs/areas/*.md
# equals the language's source set, and (2) no source file is linked
# from more than one area document. Run from the repo root.
set -euo pipefail

lang="${1:-}"
[ -n "$lang" ] || { echo "usage: $0 {idris|lean}" >&2; exit 2; }
case "$lang" in
  idris)
    areas="geb-idris/docs/areas"; ext="idr"
    mapfile -t sources < <(
      find geb-idris/src -name '*.idr' | grep -v '/Test/' \
      | sed 's#^#./#' | sort -u)
    ;;
  lean)
    areas="geb-lean/docs/areas"; ext="lean"
    mapfile -t sources < <(
      { echo geb-lean/GebLean.lean; find geb-lean/GebLean -name '*.lean'; } \
      | grep -vE '(^|/)GebLeanTests(/|\.lean$)' \
      | sed 's#^#./#' | sort -u)
    ;;
  *) echo "usage: $0 {idris|lean}" >&2; exit 2 ;;
esac

declare -A docs_for   # normalised-source-path -> space-joined area docs
linked_tmp="$(mktemp)"
for md in "$areas"/*.md; do
  [ -e "$md" ] || continue
  case "$(basename "$md")" in _*) continue ;; esac
  # distinct link targets ending in .<ext>, deduped within this file
  while IFS= read -r tgt; do
    [ -n "$tgt" ] || continue
    abs="$(realpath -m "$(dirname "$md")/$tgt")"
    rel="./${abs#"$PWD"/}"
    echo "$rel" >> "$linked_tmp"
    if [ -n "${docs_for[$rel]:-}" ]; then
      docs_for[$rel]="${docs_for[$rel]} $(basename "$md")"
    else
      docs_for[$rel]="$(basename "$md")"
    fi
  done < <(grep -oE "\]\([^)]*\.${ext}\)" "$md" \
           | sed -E 's/^\]\((.*)\)$/\1/' | sort -u)
done

linked_sorted="$(sort -u "$linked_tmp")"; rm -f "$linked_tmp"
src_sorted="$(printf '%s\n' "${sources[@]}" | sort -u)"

status=0
echo "== Assertion 1: totality (linked set == source set) =="
missing="$(comm -23 <(printf '%s\n' "$src_sorted") <(printf '%s\n' "$linked_sorted"))"
extra="$(comm -13 <(printf '%s\n' "$src_sorted") <(printf '%s\n' "$linked_sorted"))"
if [ -n "$missing" ]; then echo "UNLINKED source files:"; echo "$missing"; status=1; fi
if [ -n "$extra" ]; then echo "LINKED non-source targets:"; echo "$extra"; status=1; fi

echo "== Assertion 2: disjointness (each file in <=1 area doc) =="
for f in "${!docs_for[@]}"; do
  n=$(wc -w <<<"${docs_for[$f]}")
  if [ "$n" -gt 1 ]; then echo "MULTI-HOME: $f -> ${docs_for[$f]}"; status=1; fi
done

[ "$status" -eq 0 ] && echo "OK: $lang coverage total and disjoint."
exit "$status"
```

### Lean area matrix

Source set: 215 files (`geb-lean/GebLean.lean` + 214 under `GebLean/`),
excluding `GebLeanTests/`. Each area = the `.lean` entries listed under
its workstream in the current `geb-lean/docs/index.md` (frozen by Task
2), **plus** the unmentioned files assigned below, **minus** the
disjointness reassignments. Ten areas; CSLib is a cross-cutting note,
not an area.

The 70 files mentioned nowhere in the current index are assigned:

- **A1 Quivers/semicategories/acyclic** (`quivers.md`):
  `CategoryPresentation.lean`.
- **A2 Category-judgment & `L ⊣ Φ`** (`category-judgments.md`):
  `PLang/CatJudgmentAdjunction.lean`, `CatValuedFunctor.lean`,
  `PLang.lean` (aggregator).
- **A3 Polynomial / W- / M-types & PFunctors** (`polynomial-functors.md`):
  `LawvereBTEq.lean`, `LawvereBTPrimrec.lean`, `TreePER.lean`,
  `TreePERLimits.lean`, `TreePERColimits.lean`,
  `TreePERLawvereBT.lean`, `TypePBTO.lean`, `FreeToposBT.lean`.
- **A4 Profunctors & end machinery** (`profunctors-ends.md`):
  `WedgeWeightComputation.lean`, `DinaturalNumbers.lean`.
- **A5 Internal-presheaf Grothendieck** (`internal-presheaf.md`): none.
- **A6 PshRelEdge / edge-of-presheaf** (`pshreledge.md`):
  `RelDouble.lean`, `RelInterpComposition.lean`, `RelSpanDiagram.lean`.
- **A7 Tree calculus Phase 2** (`tree-calculus.md`): none new.
- **A8 Lawvere ER / Gödel-T / K_sim** (`lawvere-er-ksim.md`):
  `LawvereERBool.lean`, `LawvereERDelta.lean`, `LawvereERLex.lean`,
  `LawvereERNatBTV2Equiv.lean`, `LawvereERTetration.lean`,
  `LawvereGodelT.lean`, `LawvereGodelTLemma16.lean`,
  `LawvereGodelTReduces.lean`, `LawvereGodelTTerm.lean`,
  `LawvereNatBT.lean`, `LawvereNatBT0.lean`,
  `LawvereNatBTBackTrans.lean`, `LawvereNatBTInterp.lean`,
  `LawvereNatBTQuot.lean`, `LawvereNatBTV2.lean`,
  `LawvereNatBTV20.lean`, `LawvereNatBTV2Interp.lean`,
  `LawvereNatBTV2Quot.lean`, `LawvereTreeERArith.lean`,
  `LawvereTreeERInterp.lean`, `LawvereTreeERQuot.lean`,
  `LayeredEquivalence.lean`, `TreeGoedel.lean`, `TreeEqGoedel.lean`,
  `TreeLogic.lean`.
- **A9 NNO / arithmetic / topos primitives** (`nno-arithmetic-topos.md`):
  `NatArith.lean`, `NatNNO.lean`, `PSO.lean`, `PLO.lean`,
  `PSTONat.lean`, `ParanaturalTopos.lean`, `PresheafPRA.lean`,
  `PresheafPRADiscrete.lean`, `PresheafPRAUMorph.lean`.
- **A10 Utilities (residual)** (`utilities.md`): `GebLean.lean` (root
  aggregator), `Utilities.lean` (aggregator), and these 17
  `Utilities/*.lean` files: `Utilities/Arrow.lean`,
  `Utilities/ArrowCospanAdjunction.lean`,
  `Utilities/ComputableLimits.lean`, `Utilities/DaggerCategory.lean`,
  `Utilities/DistributiveLaw.lean`, `Utilities/DoubleCategory.lean`,
  `Utilities/Equalities.lean`, `Utilities/Families.lean`,
  `Utilities/Fintype.lean`, `Utilities/Graph.lean`,
  `Utilities/Opposites.lean`, `Utilities/Presheaf.lean`,
  `Utilities/RepresentableDensity.lean`, `Utilities/SetoidCat.lean`,
  `Utilities/Sigma.lean`, `Utilities/Skeleton.lean`,
  `Utilities/Slice.lean`.

Disjointness reassignments (the index lists these under two
workstreams; the matrix keeps each once):

- `GebLean/Utilities/PolyCombinators.lean` — linked from **A3** only;
  A7 (`tree-calculus.md`) references it in prose without a coverage
  link.
- `GebLean/Paranatural.lean` and `GebLean/ParanatAlg.lean` — listed
  under both A3 and A4 in the index; linked from **A4** only (their
  paranatural/end home); A3 references in prose.

Area 10 = `Utilities/` files **not** claimed by a topical workstream.
The topical workstreams already enumerate the `Utilities/*` files they
document (e.g. `Utilities/Profunctors.lean` → A4,
`Utilities/KArith.lean` → A8, `Utilities/Grothendieck.lean` → A5); A10
takes only the residue listed above. The check enforces that the split
is exact.

### Idris area matrix

Source set: 77 non-test modules under `geb-idris/src/` (exclude any
path with a `Test/` segment, which covers `LanguageDef/Test/`,
`Library/Test/`, `Executable/Test/`, and top-level `Test/`). Nine
areas. Assignment by dominant import / namespace, except where a module
is named explicitly below (explicit naming overrides the import
tie-break).

- **I1 Library** (`library.md`) [4]: `Library/IdrisUtils`,
  `Library/IdrisCategories`, `Library/IdrisAlgebra`,
  `Library/CategoryTheory`.
- **I2 Polynomial functors** (`polynomial-functors.md`) [14]:
  `PolyCat`, `FinPoly`, `GenPolyFunc`, `HigherPolyCat`, `PolyIndTypes`,
  `SliceFuncCat`, `SlicePolyCat`, `SlicePolyUMorph`, `PolySliceCat`,
  `SlPolyImpred`, `DisliceCat`, `DislicePolyCat`, `SlicePolyDialg`,
  `SlicePolyDifunc`.
- **I3 Internal categories & profunctors** (`internal-cats-profunctors.md`)
  [24]: `InternalCat`, `InternalHigherCat`, `InternalProfunctor`,
  `Diprofunctor`, `IntArena`, `IntDepFamCat`, `IntDisheafCat`,
  `IntECofamCat`, `IntEFamCat`, `IntFactCat`, `IntFactCatFunc`,
  `IntParamCat`, `IntTwistedArrowCat`, `IntUCofamCat`, `IntUFamCat`,
  `MLBundleCat`, `MLDirichCat`, `MLTwistPair`, `SlPolyIntCat`,
  `DiPolyFunc`, `MLDiPolyFunc`, `PolyDifunc`, `PolyProfunctor`,
  `PolyProfEnd`.
- **I4 The Geb language** (`geb-language.md`) [7]: `Geb`, `GebTopos`,
  `Theories`, `ProgFinSet`, `Expression`, `Interpretation`, `ADTCat`.
- **I5 Recursion & compilation targets** (`recursion-targets.md`) [3]:
  `TreeCalculus`, `Nock`, `BinTree`.
- **I6 Metaprogramming & syntax** (`metaprogramming-syntax.md`) [4]:
  `Metaprogramming`, `Syntax`, `Figures`, `Telescope`.
- **I7 Circuit frontend** (`circuit-frontend.md`) [0 modules]: prose
  summary linking to `geb-idris/README.md`, left in place. No `.idr`
  link.
- **I8 Foundational & finite-category machinery** (`foundational-cats.md`)
  [13]: `Quiver`, `FinCat`, `FinCatPRA`, `Adjunctions`,
  `UniversalCategory`, `DiagramCat`, `SpanCospan`, `HelixCat`,
  `RopeCat`, `NatPrefixCat`, and the quiver-based multi-level family
  `MLQuivCat`, `MLQuivUniv`, `MLQuivPoly`.
- **I9 Logic, refinement, effects & language assembly**
  (`logic-refinement.md`) [8]: `Logic`, `QType`, `RQFin`,
  `RefinedADT`, `Atom`, `ComputationalEffects`, `Embedded`,
  `FullLanguageDef`.

Counts: 4 + 14 + 24 + 7 + 3 + 4 + 0 + 13 + 8 = 77. Task 1 freezes the
exact per-file assignment and the check verifies it.

### Contested boundaries (for reviewer attention)

Defensible either way; recorded so the adversarial reviewer and the
user can object before authoring. Each has a chosen home above.

- Lean `CategoryPresentation` (A1 chosen vs A2).
- Lean `CatValuedFunctor` (A2 chosen vs A4).
- Lean `PLang.lean` aggregator (A2 chosen vs A7; the dir spans both).
- Lean `FreeToposBT` (A3 chosen vs A9).
- Lean `DinaturalNumbers` (A4 chosen vs A9).
- Lean tree split: `TreePER*`/`TypePBTO` → A3 vs `TreeGoedel`/
  `TreeEqGoedel`/`TreeLogic` → A8 (Gödel-numbering side).
- Lean `GebLean.lean` root aggregator (A10 chosen).
- Idris `SlPolyIntCat` (I3 chosen vs I2).
- Idris `MLQuiv*` family (I8 chosen vs I2; `MLQuivPoly` touches poly).
- Idris `FullLanguageDef` (I9 chosen vs I4; it assembles the language
  atop the logic/effects substrate).
- Idris `Figures`/`Telescope` (I6 by explicit naming, overriding their
  dominant poly import).

### Parallel-formulation seed clusters

Maintained and extended during authoring; described once in a home
area's **Alternative formulations** section, cross-linked elsewhere.
Each cluster is written **concept-first**: state the single shared
mathematical concept, then present the repository's several
formulations as variations of that one concept (artifacts of exploring
for a preferred form), not as distinct constructions. See
`geb-lean/docs/areas/category-judgments.md` (the calibration doc) for
the worked exemplar.

- Lean Lawvere-NatBT versions: `LawvereNatBT*` vs `LawvereNatBTV2*`
  (and `*V20`) — home A8.
- Lean K_sim→ER routes: `LawvereKSimER.lean` vs
  `LawvereKSimERDirect.lean` — home A8.
- Lean `Cat` ↔ (co)presheaf adjunction over `CategoryJudgments`:
  the several `L ⊣ Φ` formulations — home A2.
- Lean relational double categories: `RelDouble` / `PshRelDouble` /
  `YonedaRelDouble` — home A6.

## Task 0: Tooling and baseline

**Files:**

- Create: `docs/tools/check-area-coverage.sh`
- Create (empty dirs via `.gitkeep`): `geb-idris/docs/areas/.gitkeep`,
  `geb-lean/docs/areas/.gitkeep`

- [ ] **Step 1: Write the check script** exactly as in
  [The coverage-check script](#the-coverage-check-script) to
  `docs/tools/check-area-coverage.sh`.

- [ ] **Step 2: Make it executable and create the area dirs**

```bash
chmod +x docs/tools/check-area-coverage.sh
mkdir -p geb-idris/docs/areas geb-lean/docs/areas
touch geb-idris/docs/areas/.gitkeep geb-lean/docs/areas/.gitkeep
```

- [ ] **Step 3: Baseline run (expect total failure, no docs yet)**

Run: `docs/tools/check-area-coverage.sh lean` then `... idris`
Expected: both exit non-zero, Assertion 1 lists every source file as
UNLINKED, Assertion 2 lists nothing. This confirms the enumerator sees
the right source sets (215 Lean, 77 Idris).

- [ ] **Step 4: Verify the source-set sizes**

Run:

```bash
{ echo geb-lean/GebLean.lean; find geb-lean/GebLean -name '*.lean'; } \
  | grep -vE '(^|/)GebLeanTests' | wc -l   # expect 215
find geb-idris/src -name '*.idr' | grep -v '/Test/' | wc -l  # expect 77
```

- [ ] **Step 5: Commit**

`jj describe -m "docs(tooling): add area-coverage check script"` then
`jj new`.

## Task 1: Idris partition matrix and import-graph note

**Files:**

- Create: `geb-idris/docs/areas/_coverage.tsv`
- Create: `geb-idris/docs/areas/_partition-notes.md`

- [ ] **Step 1: Generate the import graph** for confirmation:

```bash
for f in $(find geb-idris/src -name '*.idr' | grep -v /Test/ | sort); do
  printf '%s\t%s\n' "$f" \
    "$(grep -E '^import' "$f" | sed 's/import public //;s/import //' \
       | grep -E 'LanguageDef|Library' | tr '\n' ' ')"
done
```

- [ ] **Step 2: Write `_coverage.tsv`** — one `path<TAB>area-slug` line
  per the 77 modules, following the
  [Idris area matrix](#idris-area-matrix). Use the area slugs
  (`library`, `polynomial-functors`, `internal-cats-profunctors`,
  `geb-language`, `recursion-targets`, `metaprogramming-syntax`,
  `circuit-frontend`, `foundational-cats`, `logic-refinement`).

- [ ] **Step 3: Verify the matrix is total and disjoint over 77 files**

```bash
cut -f1 geb-idris/docs/areas/_coverage.tsv | sort -u | wc -l   # expect 77
cut -f1 geb-idris/docs/areas/_coverage.tsv | sort | uniq -d    # expect empty
comm -3 <(cut -f1 geb-idris/docs/areas/_coverage.tsv | sort -u) \
        <(find geb-idris/src -name '*.idr' | grep -v /Test/ | sort -u)  # empty
```

- [ ] **Step 4: Record contested calls** in `_partition-notes.md` (the
  Idris items from
  [Contested boundaries](#contested-boundaries-for-reviewer-attention)),
  one line each with the chosen home and the alternative.

- [ ] **Step 5: Lint and commit**

Run markdownlint on `_partition-notes.md`; then
`jj describe -m "docs(geb-idris): freeze area partition matrix"`;
`jj new`.

## Task 2: Lean partition matrix

**Files:**

- Create: `geb-lean/docs/areas/_coverage.tsv`
- Create: `geb-lean/docs/areas/_partition-notes.md`

- [ ] **Step 1: Seed from the index workstreams.** The index has
  **eight** topical `##` workstreams (plus `## Directory structure` and
  `## CSLib integration`, which are not source areas). Extract each
  workstream's `Source-tree paths` `.lean` entries:

```bash
awk '/^## /{s=$0} /GebLean(\/[A-Za-z0-9]+)*\.lean/{print s"\t"$0}' \
  geb-lean/docs/index.md | grep -oE '^## .*|GebLean[^`]*\.lean'
```

  Map each of the eight workstream headings to its area slug
  (`quivers`, `category-judgments`, `polynomial-functors`,
  `profunctors-ends`, `internal-presheaf`, `pshreledge`,
  `tree-calculus`, and the `K_sim hierarchy …` heading →
  `lawvere-er-ksim`). The remaining two areas, `nno-arithmetic-topos`
  (A9) and `utilities` (A10), have **no** index workstream; they are
  built entirely from the unmentioned-file list in Step 2.

- [ ] **Step 2: Add the 70 unmentioned files** per the
  [Lean area matrix](#lean-area-matrix), and apply the disjointness
  reassignments (`PolyCombinators` → A3 only; `Paranatural`,
  `ParanatAlg` → A4 only). Write all 215 `path<TAB>area-slug` rows to
  `_coverage.tsv`.

- [ ] **Step 3: Verify total and disjoint over 215 files**

```bash
cut -f1 geb-lean/docs/areas/_coverage.tsv | sort -u | wc -l   # expect 215
cut -f1 geb-lean/docs/areas/_coverage.tsv | sort | uniq -d    # expect empty
comm -3 <(cut -f1 geb-lean/docs/areas/_coverage.tsv | sed 's#^#geb-lean/#' | sort -u) \
        <( { echo geb-lean/GebLean.lean; find geb-lean/GebLean -name '*.lean'; } \
           | grep -vE 'GebLeanTests' | sort -u)   # expect empty
```

- [ ] **Step 4: Record contested calls + the Utilities split** in
  `_partition-notes.md` (the Lean items from
  [Contested boundaries](#contested-boundaries-for-reviewer-attention),
  plus the rule "A10 = `Utilities/` not claimed by a topical area").

- [ ] **Step 5: Lint and commit**

`jj describe -m "docs(geb-lean): freeze area partition matrix"`;
`jj new`.

## Task 3: Template + calibration area doc (Lean L-Phi)

This calibrates depth budget, citation syntax, and a worked provenance
tag of a high-stakes category. **STOP for user approval at the end.**

**Files:**

- Create: `geb-idris/docs/areas/_TEMPLATE.md`,
  `geb-lean/docs/areas/_TEMPLATE.md`
- Create: `geb-lean/docs/areas/category-judgments.md`

- [ ] **Step 1: Write `_TEMPLATE.md`** (both copies) exactly as in
  [The doc template](#the-doc-template).

- [ ] **Step 2: Read the A2 modules.** Read declarations of
  `CategoryJudgments.lean`, `DepCategoryJudgments.lean`,
  `CatJudgmentAdjunction.lean`, `PLang/CatJudgmentAdjunction.lean`,
  `DepCategoryAdjunction.lean`, `DepCategoryCat.lean`,
  `PLang/CatJudgment.lean`, `PLang/CatJudgGrothendieck.lean`,
  `PLang/CatJudgCoprAdjunction.lean`, `PLang/CatJudgGrAdjunction.lean`,
  `CatValuedFunctor.lean`, `PLang.lean`, `Utilities/Category.lean`,
  `Utilities/OverCategoryEquiv.lean`. Read
  `geb-lean/docs/novelty-analysis.md` as the provenance starting input.

- [ ] **Step 3: Author `category-judgments.md`** to the template:
  Purpose; Mathematical context (judgmental vs structural category
  presentations, the `L ⊣ Φ` reflective adjunction `Cat ⇆ [Cⱼᵒᵖ,Set]`,
  the nerve/realisation analogy); Modules (one bullet per file above,
  with headline declarations and a Provenance tag each — at least one
  category-1 or category-2 tag exists here per `novelty-analysis.md`);
  an **Alternative formulations** section for the several `L ⊣ Φ`
  formulations (the named seed cluster); Dependencies (→ A1);
  Pointers (`novelty-analysis.md`, relevant specs).

- [ ] **Step 4: Lint + run doctoc on the new doc**

Run: `npx markdownlint-cli2 --config geb-lean/.markdownlint-cli2.jsonc geb-lean/docs/areas/category-judgments.md`
then `doctoc geb-lean/docs/areas/category-judgments.md`.

- [ ] **Step 5: Commit, then STOP and request user review of the
  calibration doc** (depth, citation style, provenance phrasing) before
  authoring the remaining areas.

`jj describe -m "docs(geb-lean): calibration area doc — category judgments"`;
`jj new`.

## Task 4: Idris area documents

One commit per area. For each, read the modules in
`geb-idris/docs/areas/_coverage.tsv` for that slug, author the doc to
`_TEMPLATE.md`, link every assigned module exactly once, lint, doctoc.
Provenance uses Idris categories 1–2 + Lean cross-links only (per the
spec's Idris adaptation).

- [ ] **Step 1: `library.md`** (I1) — the Idris/category-theory
  substrate; modules `Library/IdrisUtils`, `IdrisCategories`,
  `IdrisAlgebra`, `CategoryTheory`. Commit.
- [ ] **Step 2: `polynomial-functors.md`** (I2, 14 modules). Cite the
  existing `geb-idris/docs/mldirichf-generalization.md` in Pointers.
  Commit.
- [ ] **Step 3: `internal-cats-profunctors.md`** (I3, 24 modules). Cite
  `geb-idris/docs/profunctor-end-characterization.md` and
  `twisted-arrow-copresheaf-analysis.md` in Pointers; note the
  difunctor family as a parallel-formulation candidate vs the Lean
  profunctor area. Commit.
- [ ] **Step 4: `geb-language.md`** (I4, 7 modules) — the assembled
  topos/expression/interpretation layer. Commit.
- [ ] **Step 5: `recursion-targets.md`** (I5, 3 modules) — tree
  calculus, Nock, binary trees; cross-link the Lean tree-calculus area.
  Commit.
- [ ] **Step 6: `metaprogramming-syntax.md`** (I6, 4 modules). Commit.
- [ ] **Step 7: `circuit-frontend.md`** (I7, prose-only) — summary
  linking to `geb-idris/README.md`; no `.idr` link. Commit.
- [ ] **Step 8: `foundational-cats.md`** (I8, 13 modules incl.
  `RopeCat`, `FinCatPRA`, and the `MLQuiv*` trio). Commit.
- [ ] **Step 9: `logic-refinement.md`** (I9, 8 modules incl.
  `FullLanguageDef`). Commit.

## Task 5: Idris index assembly + coverage gate

**Files:**

- Modify: `geb-idris/docs/index.md`

- [ ] **Step 1: Rewrite `index.md` as the spine** — short identity
  paragraph; one paragraph + link per area document (I1–I9); retain
  links to `geb-syllabus.md` and the three existing research notes; a
  coverage note stating the source set and test exclusion.

- [ ] **Step 2: doctoc + lint** `index.md`.

- [ ] **Step 3: Run the coverage gate**

Run: `docs/tools/check-area-coverage.sh idris`
Expected: `OK: idris coverage total and disjoint.` Fix any UNLINKED or
MULTI-HOME report (a missing module bullet, a wrong relative path, or a
file linked from two area docs) and rerun until clean.

- [ ] **Step 4: Commit**

`jj describe -m "docs(geb-idris): index spine + area coverage gate"`;
`jj new`.

## Task 6: Lean research-note relocation + dead-note sign-off

**Files:**

- Move: the 51 top-level `geb-lean/docs/*.md` notes (all except
  `index.md`) → `geb-lean/docs/research/`
- Create: `geb-lean/docs/areas/_dead-note-candidates.md`

- [ ] **Step 1: List the 51 notes**

```bash
find geb-lean/docs -maxdepth 1 -name '*.md' ! -name index.md | sort
```

- [ ] **Step 2: Relocate** each into `geb-lean/docs/research/` with a
  plain `mv`; jj records the move on its next snapshot (jj has no `mv`
  subcommand and tracks content by snapshot). Do not use `git mv` (the
  repo is jj-colocated and we do not run mutating git). Leave
  `index.md`, the `research/`, `plans/`, `superpowers/`, `.claude/`
  subdirectories, and the PDFs in place.

- [ ] **Step 3: Draft dead-note candidates** in
  `_dead-note-candidates.md`: any relocated note that is a superseded
  duplicate or an explicitly-abandoned approach (e.g.
  `plang-category-judgments-old.md`). For each give the reason and the
  superseding artifact. **STOP and request user sign-off; delete only
  what the user approves.**

- [ ] **Step 4: Fix inbound links.** Re-point any `docs/<note>.md`
  reference inside `index.md` to `docs/research/<note>.md`:

```bash
grep -rnE '\]\((\.\./)*docs/[A-Za-z0-9-]+\.md\)' geb-lean/docs/index.md
```

- [ ] **Step 5: Lint, then commit**

`jj describe -m "docs(geb-lean): relocate research notes to research/"`;
`jj new`.

## Task 7: Lean area documents

One commit per area; A2 (`category-judgments.md`) is already done
(Task 3). For each remaining area read the modules in
`geb-lean/docs/areas/_coverage.tsv`, author to `_TEMPLATE.md`, link
each assigned file once, add provenance tags (full four-category search
for Lean), cite relocated research notes / specs in Pointers, lint,
doctoc.

- [ ] **Step 1: `quivers.md`** (A1) incl. `CategoryPresentation`. Commit.
- [ ] **Step 2: `polynomial-functors.md`** (A3) incl. the
  `TreePER*`/`LawvereBT*` additions; link `Utilities/PolyCombinators`
  here (A3-only). Cite `coalgebra-copresheaf-math.md`. Commit.
- [ ] **Step 3: `profunctors-ends.md`** (A4) incl. `Paranatural`,
  `ParanatAlg`, `WedgeWeightComputation`, `DinaturalNumbers`. Commit.
- [ ] **Step 4: `internal-presheaf.md`** (A5). Commit.
- [ ] **Step 5: `pshreledge.md`** (A6) incl. the `Rel*` additions and
  the relational-double-category parallel-formulation note. Commit.
- [ ] **Step 6: `tree-calculus.md`** (A7); reference (do not re-link)
  `Utilities/PolyCombinators`; cite `docs/research/tree-calculus.md`.
  Commit.
- [ ] **Step 7: `lawvere-er-ksim.md`** (A8) — the largest area; incl.
  all `LawvereGodelT*`, `LawvereNatBT*`/`V2*`, `LawvereTreeER*`,
  `Tree{Goedel,EqGoedel,Logic}`, `LayeredEquivalence`, and the
  `LawvereERKSim/` subdir. Write the two A8 parallel-formulation
  clusters (NatBT vs V2; KSimER vs KSimERDirect). Cite the K_sim/ER
  specs and research notes. Commit.
- [ ] **Step 8: `nno-arithmetic-topos.md`** (A9) incl. `NatArith`,
  `NatNNO`, `PSO`, `PLO`, `PSTONat`, `ParanaturalTopos`,
  `PresheafPRA*`. Commit.
- [ ] **Step 9: `utilities.md`** (A10) — residual `Utilities/*` + the
  two aggregators + `GebLean.lean`; aggregators get one-line notes. The
  root aggregator is cited with one fewer path segment than the
  `Utilities/*` files: `` [`GebLean.lean`](../../GebLean.lean) `` (not
  `../../GebLean/GebLean.lean`, which is not a real file and would fail
  the coverage check). Commit.

## Task 8: Lean index slim + coverage gate

**Files:**

- Modify: `geb-lean/docs/index.md`

- [ ] **Step 1: Slim `index.md`.** Preserve the opening framing
  paragraph and the `## Directory structure` section. Compress each
  workstream section to a short paragraph + a link to its area doc
  under `areas/`; move per-module detail into the area docs. Demote
  CSLib to a short cross-cutting note (no longer a workstream with
  source paths). Keep the Dependencies prose that conveys build order.

- [ ] **Step 2: doctoc + lint** `index.md`.

- [ ] **Step 3: Run the coverage gate**

Run: `docs/tools/check-area-coverage.sh lean`
Expected: `OK: lean coverage total and disjoint.` Fix UNLINKED /
MULTI-HOME reports (most likely a `Utilities/*` file claimed by both a
topical area and A10, or a `Paranatural`/`PolyCombinators` double-link)
and rerun until clean.

- [ ] **Step 4: Commit**

`jj describe -m "docs(geb-lean): slim index to spine + area coverage gate"`;
`jj new`.

## Task 9: Cross-cutting pass (README, clusters, provenance collation)

**Files:**

- Modify (only if a target moved): `README.md`
- Create: `geb-lean/docs/areas/_provenance-claims.md`

- [ ] **Step 1: Root README link check.** Confirm the root `README.md`
  links still resolve (no Idris/Lean index path moved). The Idris and
  Lean `index.md` paths are unchanged, so this is expected to be a
  no-op; if any link is stale, fix it.

```bash
grep -nE '\]\([^)]*\.md\)' README.md
```

- [ ] **Step 2: Cross-link parallel-formulation clusters.** Verify each
  cluster from
  [Parallel-formulation seed clusters](#parallel-formulation-seed-clusters)
  is described in exactly one area doc and linked (not restated) from
  the others; add any cluster discovered during authoring.

- [ ] **Step 3: Collate category-1/2 provenance claims** into
  `_provenance-claims.md` — every "novel" or "first formalization
  anywhere" tag across all area docs, with its citation and search
  scope, for the user's review (these are the highest-stakes claims).

- [ ] **Step 4: Lint, then commit**

`jj describe -m "docs: cross-link clusters + collate novelty claims"`;
`jj new`.

## Task 10: Final gate and holistic review

- [ ] **Step 1: Both coverage gates green**

Run: `docs/tools/check-area-coverage.sh idris` and `... lean`
Expected: both print `OK: ... total and disjoint.`

- [ ] **Step 2: Markdownlint the whole sweep**

```bash
npx markdownlint-cli2 --config geb-lean/.markdownlint-cli2.jsonc \
  "geb-idris/docs/**/*.md" "geb-lean/docs/areas/*.md" \
  "geb-lean/docs/index.md" "README.md"
```

Expected: `0 error(s)`.

- [ ] **Step 3: doctoc verify**

Run: `doctoc --dryrun --update-only geb-idris/docs geb-lean/docs`
Expected: no file reported as needing an update.

- [ ] **Step 4: Holistic review.** Dispatch a fresh-context reviewer
  over the full doc diff for: depth-budget consistency across areas,
  accuracy of headline-declaration names against current source
  (spot-check ten modules), provenance tags that overclaim, broken
  relative links, and any area doc that reads as scaffolding rather
  than overview. Fix findings; rerun Steps 1–3.

- [ ] **Step 5: Final commit**

`jj describe -m "docs: finalize Idris/Lean overview-documentation sweep"`.

## Self-review against the spec

- **Spec coverage:** every spec section maps to a task — target layout
  (Tasks 3–9), area decomposition (Tasks 1–2 matrices), template
  (Task 3), parallel formulations (Tasks 7, 9 + seed list), provenance
  (Conventions + Tasks 3–9 + Task 9 collation), existing-material
  policy (Task 6), coverage discipline (Task 0 script + Tasks 5/8/10
  gates), accuracy discipline (Conventions), markdownlint/doctoc
  (Tasks 5/8/10), process order (Tasks 0–10).
- **Placeholder scan:** the check script, template, and both matrices
  are given verbatim; the 70 unmentioned-file assignments are explicit;
  no "TBD"/"similar to" remains.
- **Type/name consistency:** area slugs are identical between the
  matrices, the area-doc filenames, the `_coverage.tsv` values, and the
  check (which keys on filenames). The two language tracks share one
  `_TEMPLATE.md` and one check script.
