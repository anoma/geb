# Verso ramified-recurrence manual implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [File structure](#file-structure)
- [Phase 0: dependency resolution](#phase-0-dependency-resolution)
  - [Task 0.1: resolve Verso in a scratch clone](#task-01-resolve-verso-in-a-scratch-clone)
  - [Task 0.2: settle the diagnostic classes](#task-02-settle-the-diagnostic-classes)
- [Phase 1: build wiring](#phase-1-build-wiring)
  - [Task 1.1: lakefile and gitignore](#task-11-lakefile-and-gitignore)
  - [Task 1.2: the module hierarchy, stubbed](#task-12-the-module-hierarchy-stubbed)
  - [Task 1.3: nolints entries](#task-13-nolints-entries)
  - [Task 1.4: extend the lint-driver guard](#task-14-extend-the-lint-driver-guard)
  - [Task 1.5: the CI step](#task-15-the-ci-step)
- [Phase 2: source-side changes](#phase-2-source-side-changes)
  - [Task 2.1: name the faithfulness instances](#task-21-name-the-faithfulness-instances)
- [Phase 3: the covered set](#phase-3-the-covered-set)
  - [Task 3.1: enumerate Part II's covered declarations](#task-31-enumerate-part-iis-covered-declarations)
- [Phase 4: Part I, the tutorial](#phase-4-part-i-the-tutorial)
  - [Task 4.0: fix the deftech vocabulary](#task-40-fix-the-deftech-vocabulary)
  - [Task 4.1: chapter 1, free algebras and recurrence](#task-41-chapter-1-free-algebras-and-recurrence)
  - [Task 4.2: chapter 2, the need to restrict recurrence](#task-42-chapter-2-the-need-to-restrict-recurrence)
  - [Task 4.3: chapter 3, ramified types](#task-43-chapter-3-ramified-types)
  - [Task 4.4: chapter 4, the ramified schema](#task-44-chapter-4-the-ramified-schema)
  - [Task 4.5: chapter 5, the section 2.4 ladder](#task-45-chapter-5-the-section-24-ladder)
  - [Task 4.6: chapter 6, ramification and complexity](#task-46-chapter-6-ramification-and-complexity)
- [Phase 5: Part II, the reference](#phase-5-part-ii-the-reference)
  - [Task 5.1: chapter 1, correspondence](#task-51-chapter-1-correspondence)
  - [Task 5.2: chapter 2, signatures, free algebras, ramified types](#task-52-chapter-2-signatures-free-algebras-ramified-types)
  - [Task 5.3: chapter 3, the Lawvere-theory layer](#task-53-chapter-3-the-lawvere-theory-layer)
  - [Task 5.4: chapter 4, the higher-order system and its instantiations](#task-54-chapter-4-the-higher-order-system-and-its-instantiations)
  - [Task 5.5: chapter 5, the characterization](#task-55-chapter-5-the-characterization)
  - [Task 5.6: chapter 6, transcription map and scope](#task-56-chapter-6-transcription-map-and-scope)
- [Phase 6: documentation amendments](#phase-6-documentation-amendments)
  - [Task 6.1: amend the rule files and the documentation index](#task-61-amend-the-rule-files-and-the-documentation-index)
  - [Task 6.2: final verification](#task-62-final-verification)
- [Appendix A: Part I deftech vocabulary](#appendix-a-part-i-deftech-vocabulary)
- [Appendix B: Part II covered declarations](#appendix-b-part-ii-covered-declarations)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

**Goal:** Build a `VersoManual` document that serves as tutorial and
reference for ramified recurrence, with its Lean content sampled from
`GebLean/Ramified/` rather than transcribed.

**Architecture:** A new `GebLeanDocs` Lean library of seventeen
modules plus an executable root, declared in `geb-lean/lakefile.toml`
and built only in CI. Twelve chapter modules each carry one
`#doc (Manual)` command; two part-index modules and a root module
assemble them with `{include}`; the generator entry point passes the
root `Part` to `manualMain`. Content reaches the document through
Verso's `docstring`, `signature`, `name` and `lean` facilities, which
resolve against the real declarations at elaboration, and through
`deftech`/`tech`, which Verso checks at generation.

**Tech Stack:** Lean 4 `v4.29.0-rc6`, `leanprover/verso`
`v4.29.0-rc6` (with `subverso`, `MD4Lean`, `plausible`), Lake,
`batteries/runLinter`.

**Spec:**
[`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`](../specs/2026-07-22-verso-ramified-manual-design.md).
Section references below are to that document.

---

## Global constraints

Every task's requirements implicitly include this section. Values are
copied verbatim from the spec.

- **Verso pin:** `name = "verso"`, `scope = "leanprover"`,
  `rev = "v4.29.0-rc6"`. The `[[require]]` block goes **before** the
  existing `mathlib` require (§2.1, §3.1).
- **`plausible` invariant:** the `plausible` entry in
  `geb-lean/lake-manifest.json` is unchanged after `lake update`. This
  is a literal acceptance criterion, not a guideline (§9).
- **`warningAsError` is retained.** No per-library entry resets it. A
  specific linter may be silenced by a per-library
  `weak.linter.<name>` entry; an environment linter by a
  `scripts/nolints.json` entry; a Verso warning by its option where it
  has one (§3.2).
- **No `module` keyword** in any of the eighteen new files (§3.1).
- **Exactly one `#doc (Manual) "…" =>`** per module in the document
  hierarchy — the root, the two part indexes, the twelve chapters.
  `GebLeanDocs.lean`, `GebLeanDocs/Bibliography.lean` and
  `GebLeanDocsMain.lean` carry none (§3.1).
- **Fully qualified names inside every `signature` block.** The block
  resolves in an empty scope with `autoImplicit` in force. Generalized
  field notation on a local, such as `A.B`, needs no qualification
  (§7).
- **Outer binder names in a `signature` block must match the
  declaration.** Only names inside an argument's type may be chosen by
  the author. This is unenforced — the mismatch is logged and
  discarded — so it is a convention the author observes (§2.3, §7).
- **`docstring` is used in Part II only.** Part I refers to
  declarations through the `name` role and `signature` blocks (§5).
- **Each technical term is defined exactly once with `deftech`.** A
  duplicated term that some `tech` reference resolves against fails
  generation (§6).
- **No proofs.** The two proof routes are described by shape; every
  result is stated with a citation (Purpose, §12).
- **Style:** `.claude/rules/lean-coding.md` for `.lean`,
  `.claude/rules/markdown-writing.md` for `.md`; 100-column limit;
  formal, dry register; no emojis; generic user references.
- **Commit discipline:** `bash scripts/pre-commit.sh` before any
  commit touching a `.lean` file. Commit messages follow
  `<type>(<scope>): <subject>`, imperative present, lower-case
  initial, no trailing period.
- **Never run `lake clean`** (forces a full mathlib rebuild). In a
  fresh worktree run `lake exe cache get` before the first
  `lake build`.

---

## File structure

**Created — the library (seventeen modules):**

| Path | Responsibility |
| --- | --- |
| `GebLeanDocs.lean` | Library index. Imports `GebLeanDocs.Root`. No `#doc`. |
| `GebLeanDocs/Root.lean` | The single root `Part`. Imports the two part modules; includes them. |
| `GebLeanDocs/Tutorial.lean` | Part I index and `Part`. Imports and includes its six chapters. |
| `GebLeanDocs/Tutorial/Ch1.lean` … `Ch6.lean` | Part I chapters (§4.1). |
| `GebLeanDocs/Reference.lean` | Part II index and `Part`. Imports and includes its six chapters. |
| `GebLeanDocs/Reference/Ch1.lean` … `Ch6.lean` | Part II chapters (§4.2). |
| `GebLeanDocs/Bibliography.lean` | Six bibliography entries. Imports `VersoManual`. No `#doc`. |

**Created — outside the library:**

| Path | Responsibility |
| --- | --- |
| `GebLeanDocsMain.lean` | Generator entry point. Imports `GebLeanDocs.Root`. No `#doc`. |

**Modified:**

| Path | Change |
| --- | --- |
| `geb-lean/lakefile.toml` | Verso require before `mathlib`; library, its `leanOptions` subtable, and executable appended. |
| `geb-lean/lake-manifest.json` | Regenerated by `lake update`, `plausible` unchanged. |
| `geb-lean/.gitignore` | `_out`. |
| `geb-lean/scripts/nolints.json` | `docBlame` entries for the generated document objects. |
| `geb-lean/scripts/tests/test-lint-driver.sh` | Extended to `GebLeanDocs`. |
| `geb-lean/scripts/pre-commit.sh` | Comment amended to record the declined instruction. |
| `GebLean/Ramified/Soundness/Collapse.lean:652` | Anonymous instance named `collapseFunctor_faithful`. |
| `GebLean/Ramified/Characterization.lean:195` | Anonymous instance named `collapseKFunctor_faithful`. |
| `.claude/rules/ci-and-workflow.md` | Pre-commit/pre-push exception; `test-lint-driver.sh` description. |
| `.claude/rules/lean-coding.md` | Docstring mandate exception (two sections); `module`-keyword exemption. |
| `docs/index.md` | Entry for the manual. |
| `docs/areas/ramified-recurrence.md` | Entry for the manual. |
| `../.github/workflows/lean_action_ci.yml` | One step running the linter and the generator. |
| This plan file | Appendices A and B, filled by Tasks 3.1 and 4.0. |

---

## Phase 0: dependency resolution

This phase is a go/no-go. If Task 0.1 fails after its fallbacks, the
deliverable reduces to §9's Markdown fallback and Phases 1 to 6 do not
run.

### Task 0.1: resolve Verso in a scratch clone

**Files:**

- Create: `/tmp/verso-spike/` (scratch clone; not committed)
- Read: `geb-lean/lakefile.toml`, `geb-lean/lake-manifest.json`

**Interfaces:**

- Consumes: nothing.
- Produces: a verdict — either the Verso pin resolves with
  `plausible` unchanged, or the fallback is taken. Task 1.1 depends on
  the positive verdict.

- [ ] **Step 1: Record the current `plausible` revision**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
python3 -c "import json;m=json.load(open('lake-manifest.json'));print([p for p in m['packages'] if p['name']=='plausible'])"
```

Expected: one entry with `"rev": "e84e3e16aea6b72cc5d311ca1bb25caad417e162"`.
Record the exact revision string; it is the acceptance criterion.

- [ ] **Step 2: Make a scratch clone**

```bash
rm -rf /tmp/verso-spike
cp -r /home/terence/git-workspaces/geb/geb-lean /tmp/verso-spike
rm -rf /tmp/verso-spike/.lake/build
```

Expected: no output. The copy keeps `.lake/packages` so
`lake update` has a warm cache.

- [ ] **Step 3: Insert the require before `mathlib`**

In `/tmp/verso-spike/lakefile.toml`, immediately **before** the
existing `[[require]]` block whose `name = "mathlib"`, insert:

```toml
[[require]]
name = "verso"
scope = "leanprover"
rev = "v4.29.0-rc6"
```

- [ ] **Step 4: Resolve**

```bash
cd /tmp/verso-spike && lake update 2>&1 | tail -30
```

Expected: Lake fetches `verso`, `subverso` and `MD4Lean` and reports
no error. If it reports a version conflict, go to Step 7.

- [ ] **Step 5: Check the acceptance criterion**

```bash
cd /tmp/verso-spike
python3 -c "import json;m=json.load(open('lake-manifest.json'));print([p for p in m['packages'] if p['name']=='plausible'])"
```

Expected: the **same** revision recorded in Step 1. If it differs, the
ordering fix has not held; go to Step 7.

- [ ] **Step 6: Build Verso**

```bash
cd /tmp/verso-spike && lake build verso 2>&1 | tail -20
```

Expected: builds to completion. This is slow (Verso sets
`precompileModules := false`); allow it to run.

- [ ] **Step 7: Fallbacks, only if a previous step failed**

In order (§9):

1. Pin `plausible` explicitly at the Step 1 revision by adding a
   `[[require]]` for it ahead of the `verso` require, and repeat Steps
   4 to 6.
2. If Verso does not build against that `plausible`, stop. The
   deliverable reduces to Markdown plus a `GebLeanTests/` module
   holding one `example` per presented signature, ascribing the
   written type to the real declaration. Report this to the user and
   do not proceed to Phase 1.

- [ ] **Step 8: Record the verdict**

Append to this plan file, under Task 0.1, a two-line note giving the
resolved revisions of `verso`, `subverso` and `MD4Lean` from
`/tmp/verso-spike/lake-manifest.json`, and confirming the `plausible`
revision is unchanged. No commit yet; Task 1.1 commits the real
lakefile change.

### Task 0.2: settle the diagnostic classes

Settles open questions 2 and 3 (§13) before any chapter is written, so
that Phase 1's stubs build clean.

**Files:**

- Modify: `/tmp/verso-spike/lakefile.toml`
- Create: `/tmp/verso-spike/GebLeanDocs/Probe.lean` (scratch)

**Interfaces:**

- Consumes: Task 0.1's resolved scratch clone.
- Produces: the exact set of `[lean_lib.leanOptions]` entries and
  `scripts/nolints.json` entries that Tasks 1.1 and 1.3 apply.

- [ ] **Step 1: Add the library and a probe module**

Append to `/tmp/verso-spike/lakefile.toml`:

```toml
[[lean_lib]]
name = "GebLeanDocs"

[lean_lib.leanOptions]
weak.verso.code.warnLineLength = 100
```

Create `/tmp/verso-spike/GebLeanDocs.lean`:

```lean
import GebLeanDocs.Probe
```

Create `/tmp/verso-spike/GebLeanDocs/Probe.lean` with the content
below. The outer fence here is four backticks so that the inner
`signature` fence survives; the file itself uses three.

````lean
import VersoManual
import GebLean.Ramified.AlgSig

open Verso.Genre Manual

#doc (Manual) "Probe" =>

A paragraph naming {name}`GebLean.Ramified.FreeAlg.recurse`.

```signature
GebLean.Ramified.FreeAlg.recurse
    {A : GebLean.Ramified.AlgSig} {P C : Type}
    (g : (label : A.B) → (parameters : P) →
      (subterms : Fin (A.ar label) → GebLean.Ramified.FreeAlg A) →
      (results : Fin (A.ar label) → C) → C) :
    P → GebLean.Ramified.FreeAlg A → C
```

{docstring GebLean.Ramified.AlgSig}
````

The probe exercises all three sampling mechanisms at once, so a
failure in any of them surfaces here rather than in Phase 4.

- [ ] **Step 2: Build the probe**

```bash
cd /tmp/verso-spike && lake build GebLeanDocs 2>&1 | tail -40
```

Expected: builds. Record every warning promoted to an error. For each,
identify its class per §3.2 — frontend linter, environment linter, or
Verso warning — and its remedy. If a frontend linter objects, add a
`weak.linter.<name> = false` entry to the `[lean_lib.leanOptions]`
subtable and rebuild.

- [ ] **Step 3: Run the linter**

```bash
cd /tmp/verso-spike && lake lint -- GebLeanDocs 2>&1 | tail -40
```

Expected: one `docBlame` report against
`GebLeanDocs.Probe.«the canonical document object name»`, and possibly
others. Record every reported `(linter, declaration)` pair.

- [ ] **Step 4: Record the settled sets**

Append to this plan file, under Task 0.2, two lists: the
`[lean_lib.leanOptions]` entries required beyond the
`warnLineLength` raise, and the `(linter, declaration)` pairs
`scripts/nolints.json` will need per document module. Tasks 1.1 and
1.3 read these lists.

- [ ] **Step 5: Discard the scratch clone**

```bash
rm -rf /tmp/verso-spike
```

---

## Phase 1: build wiring

### Task 1.1: lakefile and gitignore

**Files:**

- Modify: `geb-lean/lakefile.toml`
- Modify: `geb-lean/.gitignore`
- Modify: `geb-lean/lake-manifest.json` (regenerated)

**Interfaces:**

- Consumes: Task 0.1's verdict and Task 0.2's `leanOptions` list.
- Produces: a `GebLeanDocs` lean_lib and a `geblean-docs` lean_exe
  with root `GebLeanDocsMain`, available to every later task.

- [ ] **Step 1: Insert the require before `mathlib`**

In `geb-lean/lakefile.toml`, immediately before the `[[require]]`
block whose `name = "mathlib"`:

```toml
[[require]]
name = "verso"
scope = "leanprover"
rev = "v4.29.0-rc6"
```

- [ ] **Step 2: Append the library and executable**

At the **end** of `geb-lean/lakefile.toml` — after the trailing
`[lean_lib.leanOptions]` subtable that binds to `GebLeanAxiomChecks`,
so that subtable is not rebound:

```toml
[[lean_lib]]
name = "GebLeanDocs"

[lean_lib.leanOptions]
weak.verso.code.warnLineLength = 100

[[lean_exe]]
name = "geblean-docs"
root = "GebLeanDocsMain"
supportInterpreter = true
```

Add any further `weak.linter.<name> = false` entries Task 0.2
recorded, inside the same `[lean_lib.leanOptions]` subtable.

- [ ] **Step 3: Add the output directory to `.gitignore`**

Append to `geb-lean/.gitignore`:

```text
/_out
```

- [ ] **Step 4: Resolve**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake update 2>&1 | tail -20
```

Expected: resolves without conflict.

- [ ] **Step 5: Verify the acceptance criterion**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
python3 -c "import json;m=json.load(open('lake-manifest.json'));print([p for p in m['packages'] if p['name']=='plausible'])"
```

Expected: the revision Task 0.1 Step 1 recorded, unchanged. If it
differs, revert and apply Task 0.1 Step 7 fallback 1.

- [ ] **Step 6: Confirm the existing build is undisturbed**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake build 2>&1 | tail -5
```

Expected: `GebLean` builds, from cache, in under a minute. A long
mathlib rebuild here means the `plausible` pin moved; stop and revert.

- [ ] **Step 7: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "build(verso): add the verso dependency and the GebLeanDocs targets

Declare the verso require ahead of mathlib so that mathlib's plausible
pin survives Lake's reverse-order root resolution, and append the
GebLeanDocs library, its line-length option and the geblean-docs
executable."
```

### Task 1.2: the module hierarchy, stubbed

Proves the `#doc` / `{include}` / `%doc` chain, the import graph and
the generator, with no chapter content. Phases 4 and 5 fill the
chapters.

**Files:**

- Create: `GebLeanDocs.lean`, `GebLeanDocs/Root.lean`,
  `GebLeanDocs/Tutorial.lean`, `GebLeanDocs/Reference.lean`,
  `GebLeanDocs/Bibliography.lean`, `GebLeanDocsMain.lean`
- Create: `GebLeanDocs/Tutorial/Ch1.lean` … `Ch6.lean`,
  `GebLeanDocs/Reference/Ch1.lean` … `Ch6.lean`

**Interfaces:**

- Consumes: Task 1.1's targets.
- Produces: `GebLeanDocs.Root`'s document object, consumed by
  `GebLeanDocsMain`; twelve chapter modules, each filled by one task
  in Phase 4 or 5; six bibliography entry names, cited by the chapters
  as `{citep}[leivant3]` and so on.

- [ ] **Step 1: Write the bibliography module**

Create `GebLeanDocs/Bibliography.lean`:

```lean
import VersoManual

open Verso.Genre.Manual

/-- Leivant III, the manual's primary source. -/
def leivant3 : Article := {
  authors := #["D. Leivant"],
  title := "Ramified recurrence and computational complexity III: Higher type recurrence and elementary complexity",
  journal := "Annals of Pure and Applied Logic",
  year := 1999,
  volume := "96",
  number := "1-3",
  month := "March",
  pages := some ("209", "229")
}
```

Add the remaining five entries — `leivant1`, `bellantoniCook`,
`clote`, `ritchie`, `dalLagoMartiniZorzi` — with the author lists,
titles, years, venues and DOIs from the spec's References section.
`leivant3`, `bellantoniCook` and `ritchie` take `Article`, which
requires `volume`, `number` and an explicit `month`, none defaulted
(§4.4); gather those three fields from the DOIs, which the spec's
References section carries for every published work. `leivant1`,
`clote` and `dalLagoMartiniZorzi` take `InProceedings`. Field names
above are indicative; read `VersoManual/Bibliography.lean` at the
pinned tag for the exact structure fields before writing the file.

- [ ] **Step 2: Write the twelve chapter stubs**

For each of `GebLeanDocs/Tutorial/Ch1.lean` … `Ch6.lean` and
`GebLeanDocs/Reference/Ch1.lean` … `Ch6.lean`, with the chapter title
from §4.1 or §4.2:

```lean
import VersoManual
import GebLeanDocs.Bibliography

open Verso.Genre Manual

#doc (Manual) "Free algebras and recurrence" =>

This chapter is not yet written.
```

- [ ] **Step 3: Write the two part indexes**

Create `GebLeanDocs/Tutorial.lean`:

```lean
import GebLeanDocs.Tutorial.Ch1
import GebLeanDocs.Tutorial.Ch2
import GebLeanDocs.Tutorial.Ch3
import GebLeanDocs.Tutorial.Ch4
import GebLeanDocs.Tutorial.Ch5
import GebLeanDocs.Tutorial.Ch6

open Verso.Genre Manual

#doc (Manual) "Part I: ramification from the ground up" =>

{include 1 GebLeanDocs.Tutorial.Ch1}

{include 1 GebLeanDocs.Tutorial.Ch2}

{include 1 GebLeanDocs.Tutorial.Ch3}

{include 1 GebLeanDocs.Tutorial.Ch4}

{include 1 GebLeanDocs.Tutorial.Ch5}

{include 1 GebLeanDocs.Tutorial.Ch6}
```

Create `GebLeanDocs/Reference.lean` on the same pattern, titled
"Part II: reference", including `GebLeanDocs.Reference.Ch1` …
`Ch6`.

- [ ] **Step 4: Write the root and the library index**

Create `GebLeanDocs/Root.lean`:

```lean
import GebLeanDocs.Tutorial
import GebLeanDocs.Reference

open Verso.Genre Manual

#doc (Manual) "Ramified recurrence" =>

{include 0 GebLeanDocs.Tutorial}

{include 0 GebLeanDocs.Reference}
```

Create `GebLeanDocs.lean`:

```lean
import GebLeanDocs.Root
```

- [ ] **Step 5: Write the generator entry point**

Create `GebLeanDocsMain.lean`:

```lean
import GebLeanDocs.Root

open Verso.Genre.Manual

/-- Generate the ramified-recurrence manual. -/
def main (args : List String) : IO UInt32 :=
  manualMain (%doc GebLeanDocs.Root)
    (options := args)
    (config := {
      sourceLink := some "https://github.com/anoma/geb",
      issueLink := some "https://github.com/anoma/geb/issues"
    })
```

- [ ] **Step 6: Build**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake build GebLeanDocs 2>&1 | tail -30
```

Expected: builds with no error. A `docBlame` report does not appear
here — that is `lake lint`, in Task 1.4.

- [ ] **Step 7: Generate**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake exe geblean-docs 2>&1 | tail -20
```

Expected: exit code 0, output under `_out/html-multi/`. Confirm:

```bash
test -d /home/terence/git-workspaces/geb/geb-lean/_out/html-multi && echo present
```

Expected: `present`.

- [ ] **Step 8: Run the pre-commit triad**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && bash scripts/pre-commit.sh 2>&1 | tail -20
```

Expected: passes. It does not reach `GebLeanDocs`; this confirms the
new library has not disturbed the existing gates.

- [ ] **Step 9: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "docs(verso): add the GebLeanDocs module hierarchy

Add the root, the two part indexes, twelve chapter stubs, the
bibliography entries and the generator entry point. Each module of the
document hierarchy carries one #doc command; the indexes include their
children with {include}."
```

### Task 1.3: nolints entries

**Files:**

- Modify: `geb-lean/scripts/nolints.json`

**Interfaces:**

- Consumes: Task 0.2's recorded `(linter, declaration)` pairs and
  Task 1.2's fifteen document modules.
- Produces: a `lake lint -- GebLeanDocs` that reports nothing, which
  Task 1.4's guard and Task 1.5's CI step depend on.

- [ ] **Step 1: Observe the reports**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake lint -- GebLeanDocs 2>&1 | tail -40
```

Expected: one `docBlame` report per document module — fifteen, being
the root, the two part indexes and the twelve chapters — each naming
`<Module>.«the canonical document object name»`.

- [ ] **Step 2: Append the entries manually**

Add one two-element array per reported pair to
`geb-lean/scripts/nolints.json`, preserving the existing entries:

```json
["docBlame", "GebLeanDocs.Root.«the canonical document object name»"],
["docBlame", "GebLeanDocs.Tutorial.«the canonical document object name»"],
["docBlame", "GebLeanDocs.Tutorial.Ch1.«the canonical document object name»"]
```

and so on for all fifteen. Do **not** run `runLinter --update`: it
rewrites the file wholesale from the current run and would discard
every existing entry (§3.3).

- [ ] **Step 3: Verify the file is still valid JSON**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && python3 -c "import json;d=json.load(open('scripts/nolints.json'));print(len(d))"
```

Expected: an integer at least fifteen greater than the count before
the edit.

- [ ] **Step 4: Re-run the linter**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake lint -- GebLeanDocs 2>&1 | tail -20
```

Expected: no reports.

- [ ] **Step 5: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "chore(lint): exempt Verso's generated document objects from docBlame

Verso's #doc emits one def per module with no doc comment, to which no
docstring can be attached. Append one nolints entry per document
module rather than regenerating the file, which would discard the
existing entries."
```

### Task 1.4: extend the lint-driver guard

**Files:**

- Modify: `geb-lean/scripts/tests/test-lint-driver.sh`

**Interfaces:**

- Consumes: Task 1.2's import graph.
- Produces: a guard that fails if a `GebLeanDocs.*` module is not
  transitively imported by `GebLeanDocs.lean`.

- [ ] **Step 1: Read the existing guard**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && cat scripts/tests/test-lint-driver.sh
```

Note its two invariants: that the workflow keeps the root-module
invocation form, and that no module is orphaned from the umbrella —
the second computed as a transitive `import` closure from the root,
compared against all modules with `comm -23`.

- [ ] **Step 2: Generalise the orphan check over both libraries**

Extend the script so the orphan check runs for `Geb` over
`vendor/geb-mathlib/Geb/` and for `GebLeanDocs` over `GebLeanDocs/`,
and so the invocation-form check accepts both `lake lint -- Geb` and
`lake lint -- GebLeanDocs`. Follow the script's existing structure
rather than rewriting it.

- [ ] **Step 3: Run the guard**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && bash scripts/tests/test-lint-driver.sh
```

Expected: passes for both libraries.

- [ ] **Step 4: Verify it catches an orphan**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
printf 'import VersoManual\n' > GebLeanDocs/Orphan.lean
bash scripts/tests/test-lint-driver.sh; echo "exit=$?"
rm GebLeanDocs/Orphan.lean
```

Expected: non-zero exit naming `GebLeanDocs.Orphan`. This is the
guard's whole purpose; if it passes, the check is not wired.

- [ ] **Step 5: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "test(lint): extend the lint-driver guard to GebLeanDocs

The guard's orphan invariant applies to any library linted by its root
module, so generalise it over both Geb and GebLeanDocs rather than
leaving the second unguarded."
```

### Task 1.5: the CI step

**Files:**

- Modify: `/home/terence/git-workspaces/geb/.github/workflows/lean_action_ci.yml`

**Interfaces:**

- Consumes: Tasks 1.1 to 1.4.
- Produces: CI coverage for the elaboration-time and generation-time
  checks of §2.3.

- [ ] **Step 1: Add the step**

After the existing `Axiom-linter smoke test` step, add:

```yaml
      - name: Build and generate the ramified-recurrence manual
        run: |
          lake lint -- GebLeanDocs
          lake exe geblean-docs
```

The job already sets `working-directory: geb-lean`, so both commands
resolve, and `runLinter` finds `scripts/nolints.json` at its relative
path.

- [ ] **Step 2: Verify the YAML parses**

```bash
python3 -c "import yaml,sys;yaml.safe_load(open('/home/terence/git-workspaces/geb/.github/workflows/lean_action_ci.yml'));print('ok')"
```

Expected: `ok`.

- [ ] **Step 3: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "ci(verso): lint and generate the ramified-recurrence manual

Run the generator rather than only building the library, so that both
the elaboration-time and the generation-time checks fire. The local
pre-commit and pre-push scripts are deliberately unchanged."
```

---

## Phase 2: source-side changes

### Task 2.1: name the faithfulness instances

**Files:**

- Modify: `GebLean/Ramified/Soundness/Collapse.lean:652`
- Modify: `GebLean/Ramified/Characterization.lean:195`

**Interfaces:**

- Consumes: nothing.
- Produces: `collapseFunctor_faithful` and `collapseKFunctor_faithful`,
  addressable by `{docstring}` in Part II chapter 5.

- [ ] **Step 1: Name the first instance**

In `GebLean/Ramified/Soundness/Collapse.lean`, change

```lean
instance : collapseFunctor.Faithful where
```

to

```lean
instance collapseFunctor_faithful : collapseFunctor.Faithful where
```

The existing declaration docstring above it is unchanged.

- [ ] **Step 2: Name the second instance**

In `GebLean/Ramified/Characterization.lean`, change

```lean
instance : collapseKFunctor.Faithful :=
```

to

```lean
instance collapseKFunctor_faithful : collapseKFunctor.Faithful :=
```

- [ ] **Step 3: Confirm both resolve**

Append two `#check` lines temporarily to
`GebLeanTests/Ramified/Characterization.lean`:

```lean
#check @GebLean.Ramified.collapseFunctor_faithful
#check @GebLean.Ramified.collapseKFunctor_faithful
```

then build the test library and remove them again:

```bash
cd /home/terence/git-workspaces/geb/geb-lean
lake build GebLeanTests 2>&1 | tail -20
```

Expected: builds, with the two `#check` outputs and no
`unknown identifier`. Remove the two lines before committing.
(`lake env lean` is not used: `CLAUDE.md` § Lake / build workflow
bans it, since it does not pick up `lakefile.toml`'s options.)

- [ ] **Step 4: Run the pre-commit triad**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && bash scripts/pre-commit.sh 2>&1 | tail -20
```

Expected: passes. Naming an instance is additive; no resolution
changes.

- [ ] **Step 5: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "refactor(ramified): name the two faithfulness instances

Verso's docstring block addresses a declaration by identifier, so the
anonymous instances the manual's characterization chapter renders need
names. Naming an instance is additive and leaves resolution
unchanged."
```

---

## Phase 3: the covered set

### Task 3.1: enumerate Part II's covered declarations

**Files:**

- Modify: this plan file, Appendix B

**Interfaces:**

- Consumes: §4.3's selection rule.
- Produces: the exact declaration list each Phase 5 task renders.

- [ ] **Step 1: List the candidates per module**

```bash
cd /home/terence/git-workspaces/geb/geb-lean/GebLean/Ramified
for f in AlgSig Algebras SortedSig RType Term Interp SynCat HigherOrder OmegaShift Examples; do
  echo "== $f"
  grep -nE '^(@\[[^]]*\] *)?(private |protected |partial |unsafe |scoped |nonrec )*(structure|inductive|def|abbrev|class|instance|theorem)\b' $f.lean
done
```

Expected: 309 declarations across the ten modules.

- [ ] **Step 2: Apply the selection rule**

For each declaration decide covered or excluded by §4.3:

Covered when it is a type former or a field of one; an operation the
paper names or the prose discusses; an interpretation or denotation
function, or an interpretation lemma stating such a function's value;
a predicate classifying sorts or identifiers; or one of the seven
endpoint declarations of Part II chapter 5.

Excluded when its only role is to assemble a covered declaration or to
support a proof — `simp` lemmas that are not interpretation lemmas,
transport, cast and congruence lemmas, renaming and substitution
fusion lemmas, arity and index bookkeeping, per-clause step-function
and hole-index helpers, environment constructions, and file-local
auxiliaries.

Where both reach a declaration the exclusion governs, with two
exceptions: the constructor and eliminator of a covered type former
are covered (so `FreeAlg.mk` is), and a schema's reduction rule is
covered (so `FreeAlg.recurse_mk` is). Decidability instances of
covered predicates and of covered types are excluded; the predicates
and types themselves are covered.

- [ ] **Step 3: Write Appendix B**

Fill Appendix B of this plan with one subsection per Part II chapter,
each listing its covered declarations by fully qualified name. Expect
on the order of sixty to a hundred in total (§4.3); if the count falls
far outside that band, re-read the rule before proceeding.

- [ ] **Step 4: Confirm every name resolves**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
# For each name N in Appendix B:
#   grep -rn "\b${N##*.}\b" GebLean/Ramified/ | head -1
```

Expected: every name found. A name that does not resolve is a
transcription error in the appendix, not a missing declaration.

- [ ] **Step 5: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "docs(verso): enumerate Part II's covered declarations

Apply the selection rule to the ten documented modules and record the
resulting set per chapter, so the chapter sizes are fixed before
writing begins."
```

---

## Phase 4: Part I, the tutorial

Each task fills one chapter module created in Task 1.2. Every task
follows the same five steps, so they are given once here and referred
to by each task:

- **Step A:** write the chapter's `#doc` body, with the imports its
  `name` roles and `signature` blocks require.
- **Step B:** `lake build GebLeanDocs` — expected to pass. A `name`
  role or `signature` block naming an unresolvable declaration fails
  here; that is the elaboration-time check of §2.3.
- **Step C:** `lake exe geblean-docs` — expected exit 0. A `tech`
  reference with no `deftech`, or a duplicated `deftech` that some
  `tech` resolves against, fails here; that is the generation-time
  check.
- **Step D:** `bash scripts/pre-commit.sh` — expected to pass.
- **Step E:** commit, `docs(verso): write Part I chapter N, <title>`.

### Task 4.0: fix the deftech vocabulary

- [ ] Fill Appendix A of this plan with the full `deftech` term list,
  from §6 plus a decision on each of the further Part I terms — monadic
  and polyadic word algebra, tree algebra, Kalmar elementary, tier
  erasure, clone — as `deftech`-defined or plain prose (§13, open
  question 4). Commit.

### Task 4.1: chapter 1, free algebras and recurrence

**Files:** modify `GebLeanDocs/Tutorial/Ch1.lean`.

**Imports:** `GebLeanDocs.Bibliography`, `GebLean.Ramified.AlgSig`,
`GebLean.Ramified.Algebras`.

**Content (§4.1 item 1):** `AlgSig`, `FreeAlg`, `FreeAlg.recurse` by
`name` role; Leivant III §2.1 eq. (1); the standing convention that the
algebra is infinite; word algebras, monadic and polyadic, against tree
algebras. Carries the §7 `signature` presentation of
`FreeAlg.recurse`, fully qualified, with `margin` notes naming each
position's role. Carries the sole `deftech` definitions for the eq. (1)
vocabulary — constructor label, recurrence parameters, recurrence
argument, subterms, recursive results, step functions — and for the
fragment names monotonic, closed and flat.

The `signature` block is the one in §7, verbatim.

- [ ] Steps A–E.

### Task 4.2: chapter 2, the need to restrict recurrence

**Files:** modify `GebLeanDocs/Tutorial/Ch2.lean`.

**Imports:** `GebLeanDocs.Bibliography`, `GebLean.Ramified.Examples`.

**Content (§4.1 item 2):** unrestricted nesting reaches the `2_m`
ladder, cited to Leivant III §2.4(4), with a forward `name` reference
to `GebLean.Ramified.ramTwoPow`. No `deftech` definitions.

- [ ] Steps A–E.

### Task 4.3: chapter 3, ramified types

**Files:** modify `GebLeanDocs/Tutorial/Ch3.lean`.

**Imports:** `GebLeanDocs.Bibliography`, `GebLean.Ramified.RType`.

**Content (§4.1 item 3):** `RType` as `FreeAlg rTypeSig`; `RType.o`,
`RType.arrow`, `RType.omega`; `RType.IsObj`, `RType.IsTower`,
`RType.tower`; `RType.interp`, and Leivant III §2.7's identification of
every object type's denotation with the same carrier. Carries the
`deftech` definitions for r-type, object type, `Omega`-type and tier.
The first-order tier reading appears as an aside, illustrated with a
`lean` block — keep every line at or under 100 columns, the limit
Task 1.1's `leanOptions` entry sets.

- [ ] Steps A–E.

### Task 4.4: chapter 4, the ramified schema

**Files:** modify `GebLeanDocs/Tutorial/Ch4.lean`.

**Imports:** `GebLeanDocs.Bibliography`,
`GebLean.Ramified.HigherOrder`.

**Content (§4.1 item 4):** Leivant III §2.3, eq. (4) for monotonic
ramified recurrence and eq. (5) for flat recurrence; `RIdent` and its
three shapes `DefnShape`, `MrecShape`, `FrecShape`; the indexing that
places the recurrence argument at `RType.omega τ` against an output at
`τ`, so ill-tiered recurrence is inexpressible rather than rejected;
`RIdent.interp` as tier erasure. Carries `signature` presentations of
`GebLean.Ramified.RIdent.mrec` and `GebLean.Ramified.RIdent.frec`,
fully qualified. Both already name every outer binder, so no renaming
arises; the presentations exhibit the tier indexing and supply the
retype check `docstring` does not. Every eq. (1) and type term is a
`tech` reference, not a second `deftech`.

- [ ] Steps A–E.

### Task 4.5: chapter 5, the section 2.4 ladder

**Files:** modify `GebLeanDocs/Tutorial/Ch5.lean`.

**Imports:** `GebLeanDocs.Bibliography`, `GebLean.Ramified.Examples`.

**Content (§4.1 item 5):** `ramKappa`, `ramDeltaIdent`, `ramAdd`,
`ramMul`, `ramSize`, the second-order `ramExp`, and `ramTwoPow`, each
paired with its interpretation lemma — `ramKappa_interp`,
`ramDeltaIdent_interp`, `ramAdd_interp`, `ramMul_interp`,
`ramSize_interp`, `ramExp_interp`, `ramTwoPow_interp` — stated to
exhibit the semantics and not proved. All by `name` role;
`docstring` is Part II only.

- [ ] Steps A–E.

### Task 4.6: chapter 6, ramification and complexity

**Files:** modify `GebLeanDocs/Tutorial/Ch6.lean`.

**Imports:** `GebLeanDocs.Bibliography`.

**Content (§4.1 item 6):** the three cells, stated and cited, with no
proof. Monadic word algebras and linear space, `E^2`, citing
`{citep}[ritchie]` and `{citep}[clote]`. Polyadic word algebras and
polynomial time, citing `{citep}[leivant1]` and
`{citep}[bellantoniCook]`, with the tree-algebra cost-model caveat
citing `{citep}[dalLagoMartiniZorzi]`. Higher-type ramification and the
Kalmar elementary functions, citing `{citep}[leivant3]` at §6.1,
Theorem 14. Provenance follows the design spec §2.2.

- [ ] Steps A–E.

---

## Phase 5: Part II, the reference

Each task fills one chapter module created in Task 1.2, rendering the
declarations Appendix B assigns it with `{docstring}` blocks and
connecting prose. Steps A–E are as in Phase 4, with the commit message
`docs(verso): write Part II chapter N, <title>`.

A `{docstring}` on a declaration lacking a doc comment fails
elaboration (§2.3). Appendix B's set is expected to contain no such
declaration; if one appears, add the docstring to the source module
under `GebLean/Ramified/` and note it in the commit (§8).

### Task 5.1: chapter 1, correspondence

**Files:** modify `GebLeanDocs/Reference/Ch1.lean`.
**Imports:** `GebLeanDocs.Bibliography`.
**Content (§4.2 item 1):** the paper-to-code table, as a `:::table`
directive, from §6's terminology table extended with the Lean names;
and a pointer to the generated terminology index.

- [ ] Steps A–E.

### Task 5.2: chapter 2, signatures, free algebras, ramified types

**Files:** modify `GebLeanDocs/Reference/Ch2.lean`.
**Imports:** `GebLeanDocs.Bibliography`, `GebLean.Ramified.AlgSig`,
`GebLean.Ramified.Algebras`, `GebLean.Ramified.SortedSig`,
`GebLean.Ramified.RType`.
**Content (§4.2 item 2):** the Appendix B declarations from those four
modules.

- [ ] Steps A–E.

### Task 5.3: chapter 3, the Lawvere-theory layer

**Files:** modify `GebLeanDocs/Reference/Ch3.lean`.
**Imports:** `GebLeanDocs.Bibliography`, `GebLean.Ramified.Term`,
`GebLean.Ramified.Interp`, `GebLean.Ramified.SynCat`.
**Content (§4.2 item 3):** `Tm` with its clone laws, `SortedModel` /
`Presentation` / `interpQuotRel`, and `SynCat` with its finite
products. `SortedSig`, rendered in Part II chapter 2, is referred to
here through the `name` role, not a second `docstring`.

- [ ] Steps A–E.

### Task 5.4: chapter 4, the higher-order system and its instantiations

**Files:** modify `GebLeanDocs/Reference/Ch4.lean`.
**Imports:** `GebLeanDocs.Bibliography`,
`GebLean.Ramified.HigherOrder`, `GebLean.Ramified.OmegaShift`,
`GebLean.Ramified.Examples`.
**Content (§4.2 item 4):** `appSig`, `RIdent`, `higherOrder`,
`RMRecCat`, `identHom`; `RType.omegaShift`, `kappaHat`, `kappaIdent`,
`deltaIdent`; and the §2.4 ladder whose narrative reading is Part I
chapter 5.

- [ ] Steps A–E.

### Task 5.5: chapter 5, the characterization

**Files:** modify `GebLeanDocs/Reference/Ch5.lean`.
**Imports:** `GebLeanDocs.Bibliography`,
`GebLean.Ramified.Soundness.Collapse`,
`GebLean.Ramified.Characterization`.
**Content (§4.2 item 5):** the seven endpoint declarations —
`SynCatFO`, `collapseFunctor`, `collapseFunctor_faithful`,
`ramified_definability`, `collapseKFunctor`,
`collapseKFunctor_faithful`, `ramified_definability_kSim` — as
statements, plus one paragraph each on the shape of the machine route
and the normalization route. No proofs.

- [ ] Steps A–E.

### Task 5.6: chapter 6, transcription map and scope

**Files:** modify `GebLeanDocs/Reference/Ch6.lean`.
**Imports:** `GebLeanDocs.Bibliography`.
**Content (§4.2 item 6):** paper section and equation from the design
spec §2.1's table, Lean modules from the area document's Modules
section, as a `:::table` directive; then the modules §4.3 names as
absent — the `Definability/` and `Polynomial/` directories and their
index modules, the remainder of `Soundness/` and its index module,
`SigEquiv.lean`, `PresentationEquiv.lean`, and
`GebLean/Ramified.lean`.

- [ ] Steps A–E.

---

## Phase 6: documentation amendments

### Task 6.1: amend the rule files and the documentation index

**Files:**

- Modify: `geb-lean/scripts/pre-commit.sh` (comment only)
- Modify: `.claude/rules/ci-and-workflow.md`
- Modify: `.claude/rules/lean-coding.md`
- Modify: `docs/index.md`
- Modify: `docs/areas/ramified-recurrence.md`

**Interfaces:**

- Consumes: Phases 1 to 5.
- Produces: rule files that no longer contradict the delivered
  configuration.

- [ ] **Step 1: Amend `scripts/pre-commit.sh`'s comment**

The comment instructs that a target outside the test driver's
dependency graph be added there and to `pre-push.sh` in lockstep.
Record that `GebLeanDocs` is such a target and that this design
declines the instruction, gating the manual in CI instead, so that no
contributor builds Verso on every push (§10).

- [ ] **Step 2: Amend `.claude/rules/ci-and-workflow.md`**

Record the same exception in the pre-commit and pre-push checklists,
and rewrite the description of `test-lint-driver.sh`, currently
written in `geb-mathlib` terms, to cover both libraries (§3.3).

- [ ] **Step 3: Amend `.claude/rules/lean-coding.md`**

In § Documentation and § Comment and docstring rules, which state the
same declaration-docstring mandate, record that Verso's generated
document objects carry no docstring, so neither section contradicts
the `nolints.json` entries. In § Lean 4 module system, record the
`module`-keyword exemption for `GebLeanDocs` and `GebLeanDocsMain`,
with §3.1's ground: Verso's `#doc` emits a non-`public` `def` that
`%doc` could not reach under `module`.

- [ ] **Step 4: Index the manual**

Add an entry to `docs/index.md` and to
`docs/areas/ramified-recurrence.md` § Pointers, naming the manual, its
library target and the command that generates it.

- [ ] **Step 5: Lint the markdown**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
npx doctoc --update-only docs/index.md docs/areas/ramified-recurrence.md
npx markdownlint-cli2 'docs/**/*.md' '.claude/rules/*.md' 2>&1 | tail -3
```

Expected: `0 issues`.

- [ ] **Step 6: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "docs(rules): record the GebLeanDocs exceptions and index the manual

Amend the pre-commit comment and the CI rule file to record that the
manual is gated in CI rather than locally, the lean-coding rule file
to record the docstring and module-keyword exemptions Verso's
generated definitions require, and the documentation indexes to name
the manual."
```

### Task 6.2: final verification

- [ ] **Step 1: Full local gate**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
bash scripts/pre-push.sh 2>&1 | tail -30
```

Expected: passes.

- [ ] **Step 2: The manual's own gate**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
lake lint -- GebLeanDocs && lake exe geblean-docs && echo "manual ok"
```

Expected: `manual ok`.

- [ ] **Step 3: Read the rendered output**

Open `_out/html-multi/index.html` in a browser. Confirm both parts
appear with their six chapters, the terminology index is populated,
and the bibliography renders.

- [ ] **Step 4: Report to the user**

Summarise what was built, what the gates report, and any open question
the execution settled differently from the spec's expectation.

---

## Appendix A: Part I deftech vocabulary

Filled by Task 4.0.

## Appendix B: Part II covered declarations

Filled by Task 3.1.
