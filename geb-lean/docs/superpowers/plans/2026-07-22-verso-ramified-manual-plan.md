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
  - [Task 0.1: resolve Verso against this repository](#task-01-resolve-verso-against-this-repository)
  - [Task 0.2: settle the diagnostic classes](#task-02-settle-the-diagnostic-classes)
- [Phase 1: build wiring](#phase-1-build-wiring)
  - [Task 1.1: lakefile and gitignore](#task-11-lakefile-and-gitignore)
  - [Task 1.2: the module hierarchy, stubbed](#task-12-the-module-hierarchy-stubbed)
  - [Task 1.3: nolints entries](#task-13-nolints-entries)
  - [Task 1.4: the CI step](#task-14-the-ci-step)
  - [Task 1.5: extend the lint-driver guard](#task-15-extend-the-lint-driver-guard)
- [Phase 2: source-side changes](#phase-2-source-side-changes)
  - [Task 2.1: name the faithfulness instances](#task-21-name-the-faithfulness-instances)
- [Phase 3: the covered set](#phase-3-the-covered-set)
  - [Task 3.1: enumerate Part II's covered declarations](#task-31-enumerate-part-iis-covered-declarations)
- [Phase 4: Part I, the tutorial](#phase-4-part-i-the-tutorial)
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
  - [Task 5.4a: chapter 4, the higher-order system](#task-54a-chapter-4-the-higher-order-system)
  - [Task 5.4b: chapter 4, the instantiations](#task-54b-chapter-4-the-instantiations)
  - [Task 5.5: chapter 5, the characterization](#task-55-chapter-5-the-characterization)
  - [Task 5.6: chapter 6, transcription map and scope](#task-56-chapter-6-transcription-map-and-scope)
- [Phase 6: documentation amendments](#phase-6-documentation-amendments)
  - [Task 6.1: amend the rule files and the documentation index](#task-61-amend-the-rule-files-and-the-documentation-index)
  - [Task 6.2: final verification](#task-62-final-verification)
- [Appendix A: Part I deftech vocabulary](#appendix-a-part-i-deftech-vocabulary)
- [Appendix B: Part II covered declarations](#appendix-b-part-ii-covered-declarations)
  - [Part II chapter 2: signatures, free algebras, ramified types](#part-ii-chapter-2-signatures-free-algebras-ramified-types)
  - [Part II chapter 3: the Lawvere-theory layer](#part-ii-chapter-3-the-lawvere-theory-layer)
  - [Part II chapter 4: the higher-order system and its instantiations](#part-ii-chapter-4-the-higher-order-system-and-its-instantiations)
  - [Part II chapter 5: the characterization](#part-ii-chapter-5-the-characterization)
- [References](#references)

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

**Branch:** `docs/verso-ramified-manual`, which carries the spec, its
eight review artefacts and this plan. Decision 10 fixes one plan on
one branch.

---

## Global constraints

Every task's requirements implicitly include this section. Values are
copied verbatim from the spec.

- **Verso pin:** `name = "verso"`, `scope = "leanprover"`,
  `rev = "v4.29.0-rc6"`. The `[[require]]` block goes before the
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
- **A chapter module opens two namespaces.** `open Verso.Genre
  Manual` reaches `docstring`, `deftech`, `tech`, `margin`, `table`,
  `citep` and `citet`, but `name`, `signature`, `lean` and `leanTerm`
  are declared in `Verso.Genre.Manual.InlineLean`, which is not
  re-exported, so a chapter using any of those four also writes `open
  Verso.Genre.Manual.InlineLean`. Established empirically by Task 0.2:
  without it the three constructs fail with `Unknown constant`.
- **A module docstring precedes every `#doc`.**
  `.claude/rules/lean-coding.md` states twice that a `/-! … -/`
  module docstring is mandatory after imports, and §3.1 confirms it
  as an authored obligation for this library, no linter reaching it.
  `#doc` replaces the command parser for the rest of the module, so
  the docstring can only appear before the `#doc` line; it cannot
  be retrofitted afterwards.
- **Style:** `.claude/rules/lean-coding.md` for `.lean` (100-column
  limit, enforced by `linter.style.longLine`, which
  `mathlibStandardSet` enables and `warningAsError` promotes — this
  binds prose lines inside a `#doc` body as well as Lean code);
  `.claude/rules/markdown-writing.md` for `.md` (80-column limit,
  `MD013`, tables and code blocks exempt). Formal, dry register; no
  emojis; generic user references.
- **Commit discipline:** `bash scripts/pre-commit.sh` before any
  commit touching a `.lean` file. Commit messages follow
  `<type>(<scope>): <subject>`, imperative present, lower-case
  initial, no trailing period. The type comes from the documented
  list — `feat | fix | doc | style | refactor | test | chore | perf |
  ci`. Note `doc`, singular: `.claude/rules/ci-and-workflow.md`
  records that the plural `docs` is the topic-branch prefix and not a
  commit type, and that the two forms are deliberately distinct.
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
| `geb-lean/.gitignore` | `/_out`. |
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
| This plan file | Appendix B, filled by Task 3.1. |

---

## Phase 0: dependency resolution

This phase decides whether the rest proceeds. If Task 0.1 fails after its
fallbacks, the
deliverable reduces to §9's Markdown fallback and Phases 1 to 6 do not
run.

### Task 0.1: resolve Verso against this repository

Runs in the working copy, not a copy of it. `/tmp` on this machine is
a tmpfs smaller than the repository, and
`.claude/rules/lean-coding.md` § Lake / build workflow directs
experiments into the codebase rather than `/tmp`. Nothing is committed
until Task 1.1, so a failed trial is undone with `jj restore`.

**Files:**

- Modify, provisionally: `geb-lean/lakefile.toml`,
  `geb-lean/lake-manifest.json`

**Interfaces:**

- Consumes: nothing.
- Produces: a verdict — either the Verso pin resolves with the
  manifest disturbed only by additions, or the fallback is taken.
  Task 0.2 and Task 1.1 depend on the positive verdict.

- [ ] **Step 1: Snapshot the manifest**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
cp lake-manifest.json /home/terence/git-workspaces/geb/geb-lean/manifest-before.json
python3 -c "import json;m=json.load(open('lake-manifest.json'));print([p['rev'] for p in m['packages'] if p['name']=='plausible'])"
```

Expected: `['e84e3e16aea6b72cc5d311ca1bb25caad417e162']`. The snapshot
file is scratch; Step 7 deletes it and it is never committed.

- [ ] **Step 2: Insert the require before `mathlib`**

In `geb-lean/lakefile.toml`, immediately before the `[[require]]`
block whose `name = "mathlib"`, insert:

```toml
[[require]]
name = "verso"
scope = "leanprover"
rev = "v4.29.0-rc6"
```

- [ ] **Step 3: Resolve**

```bash
lake update 2>&1 | tail -30
```

Expected: Lake fetches `verso`, `subverso` and `MD4Lean`, reporting no
error. On a version conflict, go to Step 6.

- [ ] **Step 4: Check the acceptance criterion**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
python3 - <<'EOF'
import json
before = {p['name']: p['rev'] for p in json.load(open('manifest-before.json'))['packages']}
after = {p['name']: p['rev'] for p in json.load(open('lake-manifest.json'))['packages']}
changed = {k: (before[k], after[k]) for k in before if k in after and before[k] != after[k]}
print('removed:', sorted(set(before) - set(after)))
print('added:', sorted(set(after) - set(before)))
print('changed:', changed)
EOF
```

Expected:

```text
removed: []
added: ['MD4Lean', 'subverso', 'verso']
changed: {}
```

Further names under `added` are acceptable: Verso's or SubVerso's
manifest may contribute packages this repository does not yet carry,
and the criterion is additions only. Any entry under `changed` —
`plausible` above all, but equally
`batteries`, `aesop`, `Qq`, `proofwidgets` or `Cli`, each of which
Verso's manifest may also pin — means a package already in mathlib's
closure has moved, which is the mathlib-rebuild outcome §9 declares
unacceptable. Go to Step 6.

- [ ] **Step 5: Build Verso's manual genre**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake build VersoManual 2>&1 | tail -20
```

Expected: builds to completion. `VersoManual` rather than `verso`,
which resolves to Verso's own CLI executable and builds more than this
design uses. This is slow — Verso sets `precompileModules := false` —
so allow it to run.

- [ ] **Step 6: Fallbacks, only if a previous step failed**

In order (§9):

1. Pin the moved package explicitly at its Step 1 revision, by adding
   a `[[require]]` for it ahead of the `verso` require, and repeat
   Steps 3 to 5.
2. If Verso does not build against it, undo and stop:

```bash
cd /home/terence/git-workspaces/geb && jj restore geb-lean/lakefile.toml geb-lean/lake-manifest.json
```

   Remove `manifest-before.json` as well.
   The deliverable then reduces to Markdown plus a `GebLeanTests/`
   module holding one `example` per presented signature, ascribing the
   written type to the real declaration. Report to the user and do not
   proceed to Phase 1.

- [ ] **Step 7: Record the verdict and clear the snapshot**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
python3 -c "import json;m=json.load(open('lake-manifest.json'));print({p['name']:p['rev'] for p in m['packages'] if p['name'] in ('verso','subverso','MD4Lean')})"
rm manifest-before.json
```

Append the three resolved revisions to this plan under Task 0.1, with
a line confirming the manifest diff was additions only. Task 0.2
reverts the lakefile at its own Step 7; Task 1.1 rewrites it in full
and commits.

### Task 0.2: settle the diagnostic classes

Settles open questions 2 and 3 (§13) before any chapter is written.
The probe exercises every facility §2.2 lists that a chapter uses, not
only the sampling mechanisms, because §3.2's option-less warnings bind
every role and directive argument the chapters write.

**Files:**

- Modify: `geb-lean/.gitignore` (kept)
- Modify, provisionally: `geb-lean/lakefile.toml`
- Create, provisionally: `GebLeanDocs.lean`, `GebLeanDocs/Probe.lean`,
  `GebLeanDocsMain.lean`

**Interfaces:**

- Consumes: Task 0.1's resolved working copy.
- Produces: the exact `[lean_lib.leanOptions]` entries and
  `scripts/nolints.json` entries Tasks 1.1 and 1.3 apply.

- [ ] **Step 1: Ignore the generator's output, then add the targets**

The probe runs the generator, and `jj` here sets
`snapshot.auto-track = "all()"`, so an unignored `_out` would be
snapshotted into the working copy — and `snapshot.max-new-file-size`
would make `jj` itself fail on a larger asset. Append `/_out` to
`geb-lean/.gitignore` now rather than in Task 1.1, which then has
nothing to add there.

Append to `geb-lean/lakefile.toml`:

```toml
[[lean_lib]]
name = "GebLeanDocs"

[lean_lib.leanOptions]
weak.verso.code.warnLineLength = 100
weak.linter.hashCommand = false

[[lean_exe]]
name = "geblean-docs"
root = "GebLeanDocsMain"
supportInterpreter = true
```

`weak.linter.hashCommand = false` is included from the start rather
than discovered: `linter.hashCommand` belongs to
`mathlibStandardSet`, which the package enables, and every `#doc` is a
`#`-command. The lakefile already disables it for `GebLeanTests` and
`GebLeanAxiomChecks` for the same reason.

- [ ] **Step 2: Write the probe**

Create `GebLeanDocs.lean`:

```lean
import GebLeanDocs.Probe

/-! # GebLeanDocs (probe stage)

Provisional library index; Task 1.2 replaces it.
-/
```

Create `GebLeanDocsMain.lean`:

```lean
import GebLeanDocs.Probe

open Verso.Genre.Manual

/-! # Probe generator entry point

Provisional; Task 1.2 replaces it.
-/

/-- Generate the probe document. -/
def main (args : List String) : IO UInt32 :=
  manualMain (%doc GebLeanDocs.Probe) (options := args)
```

Create `GebLeanDocs/Probe.lean` with the content below. The outer
fence here is four backticks so the inner fences survive; the file
itself uses three.

````lean
import VersoManual
import GebLean.Ramified.AlgSig

open Verso.Genre Manual

/-! # Probe

A throwaway module exercising every Verso facility a chapter uses, so
that each one's diagnostics surface before any chapter is written.
-/

def probeRef : Article := {
  title := inlines!"Classes of predictably computable functions",
  authors := #[inlines!"R. W. Ritchie"],
  journal := inlines!"Transactions of the American Mathematical Society",
  year := 1963,
  month := none,
  volume := inlines!"106",
  number := inlines!"1",
  pages := some (139, 173),
  url := some "https://doi.org/10.1090/S0002-9947-1963-0158822-2"
}

#doc (Manual) "Probe" =>

A paragraph defining {deftech}[probe term] and naming
{name}`GebLean.Ramified.FreeAlg.recurse`, then referring to the
{tech}[probe term] again, and citing {citep probeRef}[].

{margin}[A margin note.]

```signature
GebLean.Ramified.FreeAlg.recurse
    {A : GebLean.Ramified.AlgSig} {P C : Type}
    (g : (label : A.B) → (parameters : P) →
      (subterms : Fin (A.ar label) → GebLean.Ramified.FreeAlg A) →
      (results : Fin (A.ar label) → C) → C) :
    P → GebLean.Ramified.FreeAlg A → C
```

```lean
def probeHelper (n : Nat) : Nat := n + 1
```

:::table +header
* - Column
  - Column
* - Cell
  - Cell
:::

{docstring GebLean.Ramified.AlgSig}
````

The `lean` block is present because `verso.code.warnLineLength` is
checked by that block alone — §3.2 records that `leanTerm` and
`signature` do not check it — and because such a block keeps its
environment by default, so `probeHelper` becomes a real declaration
that `docBlame` will report. Both are what open questions 2 and 3 ask
about.

- [ ] **Step 3: Build**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake build GebLeanDocs 2>&1 | tail -40
```

Expected: builds. Record every warning promoted to an error. For each,
identify its class per §3.2 — frontend linter, environment linter, or
Verso warning — and its remedy. A frontend linter gets a
`weak.linter.<name> = false` entry in the `[lean_lib.leanOptions]`
subtable; retry until the build is clean.

- [ ] **Step 4: Generate**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake exe geblean-docs 2>&1 | tail -20; echo "exit=$?"
```

Expected: `exit=0`. This is where generation-time diagnostics appear —
an undefined `tech`, an unused link or footnote definition, a
deprecated role or directive argument form. Record each and its
remedy.

- [ ] **Step 5: Lint**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake lint -- GebLeanDocs 2>&1 | tail -40
```

Expected: at least two `docBlame` reports — one against
`GebLeanDocs.Probe.«the canonical document object name»` and one
against `GebLeanDocs.Probe.probeHelper`, the declaration the `lean`
block introduced. Record every `(linter, declaration)` pair.

- [ ] **Step 6: Record the settled sets**

Append to this plan under Task 0.2 two lists: the
`[lean_lib.leanOptions]` entries needed beyond the two of Step 1, and
the `(linter, declaration)` shapes `scripts/nolints.json` will need —
one per document module, plus one per declaration a `lean` block
introduces. Tasks 1.1 and 1.3 read these lists.

**Settled by this task, 2026-07-22.**

*`[lean_lib.leanOptions]` entries needed beyond Step 1's two:* none.
The probe built clean with `weak.verso.code.warnLineLength = 100` and
`weak.linter.hashCommand = false` alone.

*`(linter, declaration)` pairs for `scripts/nolints.json`:* `docBlame`
is the only linter that fires, in three shapes —

| Shape | One per | Example |
| --- | --- | --- |
| Generated document object | document module | `GebLeanDocs.Probe.«the canonical document object name»` |
| Declaration a `lean` block introduces | such declaration | `GebLeanDocs.Probe.probeHelper` |
| Undocumented top-level `def` | such declaration | `GebLeanDocs.Probe.probeRef` |

The third shape was not predicted. It does not arise where the plan is
followed, every bibliography entry carrying a declaration docstring
(Task 1.2 Step 1), but it is the reason that instruction matters.

*Not exercised:* the generation-time diagnostics §3.2 names — an
undefined `tech`, an unused link or footnote definition, a deprecated
role or directive argument — did not fire, the probe being internally
consistent. They remain unverified rather than disproved; Step C2 of
the Phase 4 and 5 cycle is where they would first appear.

- [ ] **Step 7: Undo the probe**

```bash
cd /home/terence/git-workspaces/geb
jj restore geb-lean/lakefile.toml
rm -f geb-lean/GebLeanDocs.lean geb-lean/GebLeanDocsMain.lean
rm -rf geb-lean/GebLeanDocs geb-lean/_out
```

Expected: `jj status` shows `geb-lean/lake-manifest.json` modified,
from Task 0.1, and `geb-lean/.gitignore` modified, from Step 1. The lakefile
is rewritten properly in Task
1.1; keep `.lake/` as built, so Verso is not rebuilt from source.

---

## Phase 1: build wiring

### Task 1.1: lakefile and gitignore

**Files:**

- Modify: `geb-lean/lakefile.toml`
- Modify: `geb-lean/lake-manifest.json` (regenerated)

`geb-lean/.gitignore` already carries `/_out`, added at Task 0.2
Step 1. Whether that line arrives in its own commit or in this task's
depends on whether anything was committed between the two; run
`jj status` before committing and describe what is actually there.

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

At the end of `geb-lean/lakefile.toml` — after the trailing
`[lean_lib.leanOptions]` subtable that binds to `GebLeanAxiomChecks`,
so that subtable is not rebound:

```toml
[[lean_lib]]
name = "GebLeanDocs"

[lean_lib.leanOptions]
weak.verso.code.warnLineLength = 100
weak.linter.hashCommand = false

[[lean_exe]]
name = "geblean-docs"
root = "GebLeanDocsMain"
supportInterpreter = true
```

Task 0.2 settled that no further `[lean_lib.leanOptions]` entries are
needed: the probe built clean with these two alone.

- [ ] **Step 3: Resolve**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake update 2>&1 | tail -20
```

Expected: resolves without conflict.

- [ ] **Step 4: Verify the acceptance criterion**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
python3 -c "import json;m=json.load(open('lake-manifest.json'));print([p for p in m['packages'] if p['name']=='plausible'])"
```

Expected: the revision Task 0.1 Step 1 recorded, unchanged. If it
differs, revert and apply Task 0.1 Step 7 fallback 1.

- [ ] **Step 5: Confirm the existing build is undisturbed**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake build 2>&1 | tail -5
```

Expected: `GebLean` builds, from cache, in under a minute. A long
mathlib rebuild here means the `plausible` pin moved; stop and revert.

- [ ] **Step 6: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "chore(deps): add the verso dependency and the GebLeanDocs targets

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
  as `{citep leivant3}[]` and so on.

- [ ] **Step 1: Write the bibliography module**

Create `GebLeanDocs/Bibliography.lean`. Every field of Verso's
`Article` and `InProceedings` that takes a `Doc.Inline Manual` is
written `inlines!"…"`: Verso defines no `Coe String
(Doc.Inline Manual)`, so a bare string does not elaborate. `pages`, on
`Article` only, is `Option (Nat × Nat)`; `InProceedings`
has no `pages` field, so the References table's page ranges are
transcribed for the three `Article` entries alone. Neither structure
has a DOI field, so the DOI
goes in `url`. `month` is `Option`, so `none` is a legal value, but
the field carries no default and must be written. `InProceedings`
requires `booktitle` and takes an optional `series`, which `clote`
sets as `some inlines!"…"`; `Article` requires `journal`, `volume`
and `number`. Field values are transcribed from the References section at
the end of this plan, which records them with their DOIs.

```lean
import VersoManual

open Verso.Genre.Manual

/-! # Bibliography

The six published works the manual cites, as Verso bibliography
entries. Part I chapter 6 cites all six; Leivant III is additionally
cited throughout.
-/

/-- Leivant III, the manual's primary source. -/
def leivant3 : Article := {
  title := inlines!"Ramified recurrence and computational complexity \
    III: Higher type recurrence and elementary complexity",
  authors := #[inlines!"D. Leivant"],
  journal := inlines!"Annals of Pure and Applied Logic",
  year := 1999,
  month := some inlines!"March",
  volume := inlines!"96",
  number := inlines!"1-3",
  pages := some (209, 229),
  url := some "https://doi.org/10.1016/S0168-0072(98)00040-2"
}
```

Write the remaining five on the same pattern, from the References
section: `leivant1` and `clote` as `InProceedings`,
`dalLagoMartiniZorzi` as `InProceedings`, `bellantoniCook` and
`ritchie` as `Article`. Every entry carries a declaration docstring —
all six are `def`s in a linted library, so `docBlame` reports any that
does not. Keep every line at or under 100 columns.

- [ ] **Step 2: Write the twelve chapter stubs**

For each of `GebLeanDocs/Tutorial/Ch1.lean` … `Ch6.lean` and
`GebLeanDocs/Reference/Ch1.lean` … `Ch6.lean`, with the chapter title
from §4.1 or §4.2:

```lean
import VersoManual
import GebLeanDocs.Bibliography

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # Free algebras and recurrence

Part I chapter 1 of the ramified-recurrence manual. See
`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`
section 4.1.
-/

#doc (Manual) "Free algebras and recurrence" =>

Written by Task 4.1.
```

The `/-! … -/` block must precede the `#doc` line: `#doc` replaces the
command parser for the remainder of the module, so nothing can be
added above it afterwards without editing around the `#doc`.

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

/-! # Part I index

Assembles the tutorial half's six chapters.
-/

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

/-! # Manual root

The single root `Part`, with the two parts as children.
-/

#doc (Manual) "Ramified recurrence" =>

{include 0 GebLeanDocs.Tutorial}

{include 0 GebLeanDocs.Reference}
```

Create `GebLeanDocs.lean`:

```lean
import GebLeanDocs.Root

/-! # GebLeanDocs

Library index for the ramified-recurrence manual.
-/
```

- [ ] **Step 5: Write the generator entry point**

Create `GebLeanDocsMain.lean`:

```lean
import GebLeanDocs.Root

open Verso.Genre.Manual

/-! # Generator entry point

Passes the root `Part` to `manualMain`. Outside the library.
-/

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
here — that is `lake lint`, in Task 1.3.

- [ ] **Step 7: Generate**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake exe geblean-docs 2>&1 | tail -20
```

Expected: exit code 0, with output under `_out`. Confirm:

```bash
cd /home/terence/git-workspaces/geb/geb-lean
find _out -name '*.html' | head -3
```

Expected: at least one path. The spec fixes only the output directory
`_out`, not the genre's subdirectory name, so nothing below `_out` is
asserted.

- [ ] **Step 8: Run the pre-commit triad**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && bash scripts/pre-commit.sh 2>&1 | tail -20
```

Expected: passes. It does not reach `GebLeanDocs`; this confirms the
new library has not disturbed the existing gates.

- [ ] **Step 9: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "doc(verso): add the GebLeanDocs module hierarchy

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
  Task 1.4's CI step and Task 1.5's guard depend on.

- [ ] **Step 1: Observe the reports**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake lint -- GebLeanDocs 2>&1 | tail -40
```

Expected: one `docBlame` report per document module — fifteen, being
the root, the two part indexes and the twelve chapters — each naming
`<Module>.«the canonical document object name»`.

Task 0.2 established two further shapes this stage does not yet
exhibit but later phases will: one report per declaration a `lean`
block introduces, and one per undocumented top-level `def`. No `lean`
block exists until Task 4.3, and every bibliography entry carries a
docstring, so fifteen is the expected count here. Step C2 of the
Phase 4 and 5 cycle collects the rest as they arise.

- [ ] **Step 2: Append the entries manually**

Add one two-element array per reported pair to
`geb-lean/scripts/nolints.json`, preserving the existing entries:

```json
["docBlame", "GebLeanDocs.Root.«the canonical document object name»"],
["docBlame", "GebLeanDocs.Tutorial.«the canonical document object name»"],
["docBlame", "GebLeanDocs.Tutorial.Ch1.«the canonical document object name»"]
```

and so on for all fifteen. Do not run `runLinter --update`: it
rewrites the file wholesale from the current run and would discard
every existing entry (§3.3).

- [ ] **Step 3: Verify the file is still valid JSON**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && python3 -c "import json;d=json.load(open('scripts/nolints.json'));print(len(d))"
```

Expected: at least 940. The file carries 925 entries before the
edit, and the fifteen document modules add fifteen.

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

### Task 1.4: the CI step

**Files:**

- Modify:
`/home/terence/git-workspaces/geb/.github/workflows/lean_action_ci.yml`

**Interfaces:**

- Consumes: Tasks 1.1 to 1.3.
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

### Task 1.5: extend the lint-driver guard

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

- [ ] **Step 2: Generalise both checks over a per-library table**

Extend the script so each check iterates a table of triples — library
name, source root, workflow file:

| Library | Source root | Workflow |
| --- | --- | --- |
| `Geb` | `vendor/geb-mathlib` | `../.github/workflows/geb-mathlib-refresh.yml` |
| `GebLeanDocs` | `.` | `../.github/workflows/lean_action_ci.yml` |

The invocation-form check must require `lake lint -- <library>` in
that library's own workflow: a single check over one file would be
satisfied by the wrong workflow and would silently stop guarding the
refresh job. The orphan check's module-to-file mapping is currently
hard-coded to the vendored source root, so it needs the per-library
root; `GebLeanDocs`'s root module is `./GebLeanDocs.lean`. Follow the
script's existing structure rather than rewriting it.

Task 1.4 has already added the `lake lint -- GebLeanDocs` line to
`lean_action_ci.yml`, so both rows are satisfiable when this step
runs.

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

Expected: non-zero exit naming `GebLeanDocs.Orphan`. A passing run
means the check is not reaching the new library.

- [ ] **Step 5: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "test(lint): extend the lint-driver guard to GebLeanDocs

The guard's orphan invariant applies to any library linted by its root
module, so generalise it over both Geb and GebLeanDocs rather than
leaving the second unguarded."
```

## Phase 2: source-side changes

### Task 2.1: name the faithfulness instances

**Files:**

- Modify: `GebLean/Ramified/Soundness/Collapse.lean:652`
- Modify: `GebLean/Ramified/Characterization.lean:195`
- Modify transiently, restored in Step 3:
  `GebLeanTests/Ramified/Characterization.lean`

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
(`lake env lean` is not used: `.claude/rules/lean-coding.md`
§ Lake / build workflow bans it, since it does not pick up
`lakefile.toml`'s options.)

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
- Modify transiently, restored in Step 4:
  `GebLeanTests/Ramified/Characterization.lean`

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

Expected: 312 matches. Three of them are wrapped docstring lines
beginning at column zero with a declaration keyword —
`OmegaShift.lean:315`, `OmegaShift.lean:579` and `Examples.lean:144` —
which is why §4.3's figure, taken after stripping comments, is 309.
Discount those three by inspection.

- [ ] **Step 2: Apply the selection rule, one module per step**

Work module by module, recording each module's list in Appendix B
before starting the next, so a reviewer can see the rule applied
incrementally: `AlgSig`, `Algebras`, `SortedSig`, `RType`, `Term`,
`Interp`, `SynCat`, `HigherOrder`, `OmegaShift`, `Examples`. Then a
final pass over `Soundness/Collapse.lean` and `Characterization.lean`
for the seven endpoint declarations, which §4.3 places outside the
309 and which clause 5 of the rule covers.

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
outside that band by more than a factor of two, re-read the rule
before proceeding.

- [ ] **Step 4: Confirm every name resolves**

Write Appendix B's fully qualified names, one per line, to a scratch
file, then emit a `#check` per name into a temporary test module and
build it — the same idiom Task 2.1 Step 3 uses, and the only form that
proves a name resolves as a declaration rather than merely occurring
in some docstring.

```bash
cd /home/terence/git-workspaces/geb/geb-lean
# appendix-b.txt: one fully qualified name per line, from Appendix B.
while read -r n; do echo "#check @$n"; done < appendix-b.txt \
  >> GebLeanTests/Ramified/Characterization.lean
lake build GebLeanTests 2>&1 | grep -E "unknown identifier|error" | head -20
cd /home/terence/git-workspaces/geb
jj restore geb-lean/GebLeanTests/Ramified/Characterization.lean
rm -f geb-lean/appendix-b.txt
```

The restore uses `jj`, as Tasks 0.1 and 0.2 do, rather than a copy
under `/tmp`. Remove `appendix-b.txt` on every exit path: it is
untracked in a repository whose `snapshot.auto-track` is `all()`, so
any intervening `jj` command would track it.

Expected: no output from the `grep`. Any `unknown identifier` names a
transcription error in the appendix.

The `#check` lines are appended to an existing test module rather
than written to a new one. `lakefile.toml` declares `GebLeanTests`
with `roots = ["GebLeanTests"]` and no `globs`, so Lake builds only
the root module's import closure; a new file nothing imports would
never be elaborated and the check would pass whatever Appendix B
contained. `GebLeanTests/Ramified/Characterization.lean` is reachable
from that root, and the library already sets
`linter.hashCommand = false`, so the `#check` commands do not trip the
linter. Restore the file before committing.

- [ ] **Step 5: Regenerate this plan's own table of contents**

Appendix B gains one `###` heading per Part II chapter, which stales
the plan's doctoc block. `scripts/pre-push.sh` runs
`doctoc --dryrun --update-only .` and exits non-zero if any TOC would
change, so leaving it stale fails the push gate.

```bash
cd /home/terence/git-workspaces/geb/geb-lean
doctoc --update-only docs/superpowers/plans/2026-07-22-verso-ramified-manual-plan.md
markdownlint-cli2 --config .markdownlint-cli2.jsonc --no-globs \
  'docs/superpowers/plans/2026-07-22-verso-ramified-manual-plan.md' 2>&1 | tail -2
```

Expected: `Everything is OK.` and `Summary: 0 issues in 0 files`.
Write the declaration lists as tables or fenced blocks, which `MD013`
exempts from its 80-column limit.

- [ ] **Step 6: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "doc(verso): enumerate Part II's covered declarations

Apply the selection rule to the ten documented modules and record the
resulting set per chapter, so the chapter sizes are fixed before
writing begins."
```

---

## Phase 4: Part I, the tutorial

Each task fills one chapter module created in Task 1.2. Every task
follows the same six steps, so they are given once here and referred
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
- **Step C2:** `lake lint -- GebLeanDocs` — expected to report
  nothing. A `lean` block keeps its environment by default, so a
  declaration it introduces is a real declaration of the chapter
  module and `docBlame` reports it. Append any reported
  `(linter, declaration)` pair to `scripts/nolints.json` manually,
  never with `runLinter --update`, which rewrites the file wholesale
  (§3.3, Task 1.3). `scripts/pre-commit.sh` runs a bare `lake lint`,
  which does not reach this library, so without this step the entries
  §3.3 requires would first surface in CI.
- **Step D:** `bash scripts/pre-commit.sh` — expected to pass. It does
  not reach `GebLeanDocs`; it confirms the rest of the repository is
  undisturbed.
- **Step E:** commit, `doc(verso): write Part I chapter N, <title>`.

### Task 4.1: chapter 1, free algebras and recurrence

**Files:** modify `GebLeanDocs/Tutorial/Ch1.lean`.

**Imports:** `GebLeanDocs.Bibliography`, `GebLean.Ramified.AlgSig`,
`GebLean.Ramified.Algebras`.

**Content (§4.1 item 1):** `AlgSig`, `FreeAlg`, `FreeAlg.recurse` by
`name` role; Leivant III §2.1 eq. (1); the standing convention that the
algebra is infinite; word algebras, monadic and polyadic, against tree
algebras. Carries the §7 `signature` presentation of
`FreeAlg.recurse`, fully qualified, with `margin` notes naming each
position's role. Carries the twelve chapter-1 `deftech` definitions
of Appendix A: the eq. (1) vocabulary — constructor label, recurrence parameters,
recurrence argument, subterms, recursive results, step functions — the
fragment names monotonic, closed and flat, and the algebra
classifications monadic word algebra, polyadic word algebra and tree
algebra.

**Depends on:** Appendix A, which fixes the term set.

The `signature` block is the one in §7, verbatim.

- [ ] Steps A–E, C2 included.

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
every object type's denotation with the same carrier. Carries the four
chapter-3 `deftech` definitions of Appendix A:
r-type, object type, `Omega`-type and tier.

**Depends on:** Appendix A, which fixes the term set.
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
`{citep ritchie}[]` and `{citep clote}[]`. Polyadic word algebras and
polynomial time, citing `{citep leivant1}[]` and
`{citep bellantoniCook}[]`, with the tree-algebra cost-model caveat
citing `{citep dalLagoMartiniZorzi}[]`. Higher-type ramification and the
Kalmar elementary functions, citing `{citep leivant3}[]` at §6.1,
Theorem 14. Provenance follows the design spec §2.2.

- [ ] Steps A–E.

---

## Phase 5: Part II, the reference

Each task fills one chapter module created in Task 1.2, rendering the
declarations Appendix B assigns it with `{docstring}` blocks and
connecting prose. Steps A–E are as in Phase 4, with the commit message
`doc(verso): write Part II chapter N, <title>`.

A `{docstring}` on a declaration lacking a doc comment fails
elaboration (§2.3). Appendix B's set is expected to contain no such
declaration; if one appears, add the docstring to the source module
under `GebLean/Ramified/` and note it in the commit (§8).

### Task 5.1: chapter 1, correspondence

**Files:** modify `GebLeanDocs/Reference/Ch1.lean`.
**Imports:** `GebLeanDocs.Bibliography`.
**Content (§4.2 item 1):** the paper-to-code table, as a `:::table +header`
directive, with one row per `deftech` term in
Appendix A, whose two tables fix the set — not §6's six rows, which
cover the eq. (1) positions alone, whereas §4.2 item 1 calls for the
correspondence across the whole vocabulary. Columns: term here, Leivant III's symbol,
Leivant III's name, and where the term lands in the Lean code — a
declaration name where one corresponds, a position within a
declaration's type where the term names one, an em dash where
neither. The paper's symbols and names for the eq. (1) rows come from §6's
table. For the fragment names and the type vocabulary, §6 gives the
paper's names in prose — the fragments at Leivant III section 2.1, the
type terms in the chapter-3 paragraph — and the algebra
classifications take theirs from §4.1 chapter 1. Any cell with no
counterpart in the paper carries an em dash, which is most of the
symbol column outside the eq. (1) rows.

Then a paragraph naming the generated terminology index and saying
that every `tech` reference links into it. Verso generates that index
from the `deftech` domain; the chapter states this in prose rather
than linking, no cross-page addressing role appearing in §2.2's
facility table. If execution finds one, use it and record the finding.

**Depends on:** Appendix A, which fixes the row set.

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

### Task 5.4a: chapter 4, the higher-order system

Appendix B gives chapter 4 roughly twice as many declarations as any
sibling chapter, so it is written in two reviewed passes over the same
module. This pass covers the system proper. Take the exact set from
Appendix B; no count is restated here.

**Files:** modify `GebLeanDocs/Reference/Ch4.lean`.
**Imports:** `GebLeanDocs.Bibliography`,
`GebLean.Ramified.HigherOrder`, `GebLean.Ramified.OmegaShift`.
**Content (§4.2 item 4, first half):** `appSig`, `RIdent`,
`higherOrder`, `RMRecCat`, `identHom`; `RType.omegaShift`,
`kappaHat`, `kappaIdent`, `deltaIdent` — Appendix B's declarations
from `HigherOrder.lean` and `OmegaShift.lean`.

- [ ] Steps A–E, C2 included.

### Task 5.4b: chapter 4, the instantiations

**Files:** modify `GebLeanDocs/Reference/Ch4.lean`, appending to what
Task 5.4a wrote.
**Imports:** add `GebLean.Ramified.Examples`.
**Content (§4.2 item 4, second half):** the section 2.4 ladder whose
narrative reading is Part I chapter 5 — Appendix B's declarations from
`Examples.lean`.

- [ ] Steps A–E, C2 included.

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
doctoc --update-only .
markdownlint-cli2 --config .markdownlint-cli2.jsonc --no-globs '**/*.md' 2>&1 | tail -3
```

Expected: `Summary: 0 issues in 0 files`.

- [ ] **Step 6: Commit**

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "doc(rules): record the GebLeanDocs exceptions and index the manual

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

- [ ] **Step 3: Check the rendered output**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
out=$(find _out -name '*.html' | head -1); test -n "$out" || echo "NO HTML"
for t in "Free algebras and recurrence" "The need to restrict recurrence" \
         "Ramified types" "The ramified schema" "The section 2.4 ladder" \
         "Ramification and complexity" "Correspondence" "The characterization"; do
  grep -rqF "$t" _out/ || echo "MISSING TITLE: $t"
done
grep -rqF "recurrence argument" _out/ || echo "MISSING deftech term"
grep -rqF "Ritchie" _out/ || echo "MISSING bibliography entry"
echo "checked"
```

Expected: `checked` with no `MISSING` line. The generator's default
output directory is `_out`; the `find` avoids asserting a subdirectory
name the spec does not fix.

- [ ] **Step 4: Report to the user**

Summarise what was built, what the gates report, and any open question
the execution settled differently from the spec's expectation.

---

## Appendix A: Part I deftech vocabulary

The complete `deftech` set, with its defining chapter. A term earns a
`deftech` when a chapter other than the one introducing it refers to
it; a term used only where it is introduced stays plain prose, since
`deftech` exists to carry cross-references. This rule settles §13 open
question 4.

Part I chapter 1, from Leivant III eq. (1) (§6):

| Term | Referred to from |
| --- | --- |
| constructor label | Part I ch. 4, Part II ch. 1 |
| recurrence parameters | Part I ch. 4, Part II ch. 1 |
| recurrence argument | Part I ch. 4, Part II ch. 1 |
| subterms | Part I ch. 4, Part II ch. 1 |
| recursive results | Part I ch. 4, Part II ch. 1 |
| step functions | Part I ch. 4, Part II ch. 1 |
| monotonic | Part I ch. 4 |
| closed | none; see the exception below |
| flat | Part I ch. 4, Part II ch. 4 |
| monadic word algebra | Part I ch. 6, Part II ch. 1 |
| polyadic word algebra | Part I ch. 6, Part II ch. 1 |
| tree algebra | Part I ch. 6, Part II ch. 1 |

Part I chapter 3, which cannot be defined before `RType` exists (§6):

| Term | Referred to from |
| --- | --- |
| r-type | Part I ch. 4, ch. 5, Part II ch. 2, ch. 4 |
| object type | Part I ch. 4, Part II ch. 2 |
| `Omega`-type | Part I ch. 4, Part II ch. 4 |
| tier | Part I ch. 4, ch. 6 |

Left as plain prose, each being used only where it is introduced:
Kalmar elementary (Part I ch. 6), tier erasure (Part I ch. 4), and
clone (Part II ch. 3, where `Tm`'s clone laws are the only occurrence
in either part).

One exception to the rule: `closed` has no referrer outside Part I
chapter 1, but it is defined there with `monotonic` and `flat`, which
do. Leivant III section 2.1 names the three fragments as one
taxonomy, and splitting it so that two members are defined terms and
the third is prose would read as an oversight.

## Appendix B: Part II covered declarations

The set §4.3's rule selects, one subsection per Part II chapter, by
fully qualified name. Task 3.1's steps give the selection rule, the
per-module procedure and the verification; every name below resolves
under `#check @…` against the `GebLeanTests` import closure.

Part II chapters 1 and 6 render no `{docstring}` block: chapter 1 is
the paper-to-code table and chapter 6 the transcription map, both
prose and tables, both referring to declarations through the `name`
role. Chapters 2 to 5 carry the whole set.

The `Clause` column cites §4.3: `1` type former or field of one, `2`
operation the paper names or the prose discusses, `3` interpretation
or denotation function, or interpretation lemma stating such a
function's value, `4` predicate classifying sorts or identifiers, `5`
endpoint declaration; `C` the constructor-and-eliminator exception,
`R` the schema-reduction-rule exception.

Two readings of the rule are fixed here and applied uniformly, since
§4.3 states them only by example:

- A structure's fields are not listed. §4.3 renders them through the
  structure's own `{docstring}` block, so `AlgSig.B`, `SortedSig.Op`,
  `Presentation.std` and their kind carry no entry of their own.
- A theorem is covered when it states the value of an interpretation
  or denotation function and its module's `## Main statements` lists
  it, or when it is a schema reduction rule (`FreeAlg.recurse_mk`,
  `RIdent.interp_defn`, `RIdent.mrec_interp`), or when it is an
  endpoint. A `_interp` lemma whose subject declaration is excluded
  is itself excluded.

Counts: chapter 2, 41; chapter 3, 29; chapter 4, 67; chapter 5, 7;
144 in total, against 309 candidate declarations in the ten
documented modules plus the two endpoint modules. §4.3 estimates
sixty to a hundred; the rule as written selects half again as many,
driven by `HigherOrder.lean`, where 28 of 38 declarations are
signatures, schema shapes, or interpretation functions.

Two structural consequences of the rule are worth recording for the
chapter writers, neither a misapplication of it:

- `RIdent.frec` is covered, but its reduction rule
  `RIdent.interp_frec` lives in
  `GebLean/Ramified/Polynomial/IdentEquiv.lean`, a module §4.3
  partitions as absent from Part II. Chapter 4 therefore renders two
  of the three schema reduction rules (`RIdent.interp_defn`,
  `RIdent.mrec_interp`), not three.
- `Algebras.lean` imports `HigherOrder.lean`: chapter 2's
  `binLength`, `binTail`, `treeSize` and `treeLeftChild` are typed
  over `RIdent`, the schema-identifier type chapter 4 introduces
  (`binLength` and `treeSize` also over `RType.omega`, covered later
  within chapter 2 itself, in the `RType.lean` subsection). Task
  5.2's writer meets a forward reference to chapter 4 immediately.

### Part II chapter 2: signatures, free algebras, ramified types

`GebLean/Ramified/AlgSig.lean`, 10 of 10 candidates:

| Declaration | Clause |
| --- | --- |
| `GebLean.Ramified.AlgSig` | 1 |
| `GebLean.Ramified.AlgSig.polyEndo` | 1 |
| `GebLean.Ramified.FreeAlg` | 1 |
| `GebLean.Ramified.FreeAlg.mk` | C |
| `GebLean.Ramified.FreeAlg.recurse` | 2 |
| `GebLean.Ramified.FreeAlg.recurse_mk` | R |
| `GebLean.Ramified.natAlgSig` | 2 |
| `GebLean.Ramified.natToFreeAlg` | 3 |
| `GebLean.Ramified.freeAlgToNat` | 3 |
| `GebLean.Ramified.freeAlgToNat_natToFreeAlg` | 3 |

`GebLean/Ramified/Algebras.lean`, 16 of 34 candidates:

| Declaration | Clause |
| --- | --- |
| `GebLean.Ramified.binWordAlgSig` | 2 |
| `GebLean.Ramified.treeAlgSig` | 2 |
| `GebLean.Ramified.binEmpty` | C |
| `GebLean.Ramified.binCons` | C |
| `GebLean.Ramified.treeLeaf` | C |
| `GebLean.Ramified.treeNode` | C |
| `GebLean.Ramified.binLength` | 2 |
| `GebLean.Ramified.binTail` | 2 |
| `GebLean.Ramified.treeSize` | 2 |
| `GebLean.Ramified.treeLeftChild` | 2 |
| `GebLean.Ramified.natToFreeAlg_freeAlgToNat` | 3 |
| `GebLean.Ramified.natFreeAlgEquiv` | 3 |
| `GebLean.Ramified.natFreeAlgEquiv_apply` | 3 |
| `GebLean.Ramified.natFreeAlgEquiv_symm_apply` | 3 |
| `GebLean.Ramified.AlgSigHom` | 1 |
| `GebLean.Ramified.freeAlgMap` | 2 |

Excluded: the per-clause step functions and clause tables of the four
smoke recurrences (`binLengthZero`, `binLengthSucc`, `binLengthSteps`,
`binTailKeep`, `binTailClauses`, `treeSizeLeaf`, `treeSizeNode`,
`treeSizeSteps`, `treeLeftKeep`, `treeLeftClauses`), the term-level
constructor abbreviations (`binTmEmpty`, `binTmCons0`, `treeTmLeaf`,
`treeTmNode`), the transports `AlgSigHom.pullSteps` and
`interpMapObj`, and the transport lemmas `freeAlgMap_mk` and
`recurse_freeAlgMap`.

`GebLean/Ramified/SortedSig.lean`, 3 of 3 candidates:

| Declaration | Clause |
| --- | --- |
| `GebLean.Ramified.SortedSig` | 1 |
| `GebLean.Ramified.SortedSig.sum` | 2 |
| `GebLean.Ramified.constructorSig` | 2 |

`GebLean/Ramified/RType.lean`, 12 of 32 candidates:

| Declaration | Clause |
| --- | --- |
| `GebLean.Ramified.RTypeShape` | 1 |
| `GebLean.Ramified.rTypeSig` | 2 |
| `GebLean.Ramified.RType` | 1 |
| `GebLean.Ramified.RType.o` | C |
| `GebLean.Ramified.RType.arrow` | C |
| `GebLean.Ramified.RType.omega` | C |
| `GebLean.Ramified.RType.IsObj` | 4 |
| `GebLean.Ramified.RType.tower` | 2 |
| `GebLean.Ramified.RType.IsTower` | 4 |
| `GebLean.Ramified.RType.IsSimple` | 4 |
| `GebLean.Ramified.RType.interp` | 3 |
| `GebLean.Ramified.RType.interp_isObj` | 3 |

Excluded: the three `DecidablePred` instances and the `DecidableEq`
instance (§4.3 excludes decidability instances by name);
`RType.interpCongr` with `RType.interpCongr_isObj`,
`interpCongr_cast` and `interpCongr_arrow`, as the denotation's
transport along a carrier equivalence; `RType.shape` with its three
`simp` lemmas, used nowhere outside the module and only to discharge
injectivity and decidable equality; the injectivity lemmas
`RType.mk_children_inj`, `RType.arrow_eq_arrow`,
`RType.omega_eq_omega`; the predicate facts `RType.tower_isObj`,
`RType.tower_isTower`, `RType.o_isSimple`,
`RType.arrow_isSimple_iff`; and `oObj`, the base sort paired with its
`IsObj` witness for use as an argument.

### Part II chapter 3: the Lawvere-theory layer

`GebLean/Ramified/Term.lean`, 11 of 18 candidates:

| Declaration | Clause |
| --- | --- |
| `GebLean.Ramified.Ctx` | 1 |
| `GebLean.Ramified.SortedSig.polyEndo` | 1 |
| `GebLean.Ramified.Tm` | 1 |
| `GebLean.Ramified.Tm.var` | C |
| `GebLean.Ramified.Tm.op` | C |
| `GebLean.Ramified.Tm.subst` | 2 |
| `GebLean.Ramified.Tm.subst_id` | 2 |
| `GebLean.Ramified.Tm.subst_subst` | 2 |
| `GebLean.Ramified.Tm.var_subst` | 2 |
| `GebLean.Ramified.Tm.weaken` | 2 |
| `GebLean.Ramified.QuotRel` | 1 |

The three clone laws enter under clause 2, not clause 3: §4.2 item 3
makes "`Tm` with its clone laws" the chapter's subject matter, so the
prose discusses them. §4.3's "substitution fusion lemmas" exclusion
reaches the remainder — `Tm.subst_reind` and `QuotRel.rel_reind` —
along with the reindexing transport `Tm.reind` and its three lemmas
and the one-line variable family `varOver`.

`GebLean/Ramified/Interp.lean`, 8 of 10 candidates:

| Declaration | Clause |
| --- | --- |
| `GebLean.Ramified.SortedModel` | 1 |
| `GebLean.Ramified.SortedModel.Env` | 1 |
| `GebLean.Ramified.Tm.eval` | 3 |
| `GebLean.Ramified.Tm.eval_subst` | 3 |
| `GebLean.Ramified.Presentation` | 1 |
| `GebLean.Ramified.standardModel` | 1 |
| `GebLean.Ramified.interpSetoid` | 3 |
| `GebLean.Ramified.interpQuotRel` | 3 |

`SortedModel.Env` is the environment type former, not one of §4.3's
excluded "environment constructions", which are the particular
environments built per recurrence clause. Excluded:
`Tm.eval_transport`, which the module's implementation notes call
local to `Tm.eval`, and `Tm.eval_model_morphism`, a transport of
evaluation along a model morphism.

`GebLean/Ramified/SynCat.lean`, 10 of 45 candidates:

| Declaration | Clause |
| --- | --- |
| `GebLean.Ramified.HomTuple` | 1 |
| `GebLean.Ramified.Hom` | 1 |
| `GebLean.Ramified.SynCat` | 1 |
| `GebLean.Ramified.SynCat.instCategory` | 1 |
| `GebLean.Ramified.SynCat.instCartesianMonoidalCategory` | 1 |
| `GebLean.Ramified.HomTuple.eval` | 3 |
| `GebLean.Ramified.Hom.eval` | 3 |
| `GebLean.Ramified.Hom.eval_mk` | 3 |
| `GebLean.Ramified.HomTuple.eval_comp` | 3 |
| `GebLean.Ramified.Hom.eval_comp` | 3 |

The two instances carry the category structure and the chosen finite
products, so §4.2 item 3's "`SynCat` with its finite products" is
rendered by them; the components they are assembled from —
`homSetoid`, `HomTuple.id`, `HomTuple.comp`, `Hom.id`, `Hom.comp`,
the category laws, `finAppL`, `finAppR` and the `List.get`-of-append
lemmas, `joinTuple`, `fstTuple`, `sndTuple`, `terminalTuple`,
`SynProd.fst`, `SynProd.snd`, `SynProd.lift` with their three laws,
`Hom.terminal`, `synTerminalCone`, `synProdCone` — are excluded as
assembly and index bookkeeping.

### Part II chapter 4: the higher-order system and its instantiations

`GebLean/Ramified/HigherOrder.lean`, 28 of 38 candidates:

| Declaration | Clause |
| --- | --- |
| `GebLean.Ramified.appSig` | 2 |
| `GebLean.Ramified.stdConstructorInterp` | 3 |
| `GebLean.Ramified.stdAppInterp` | 3 |
| `GebLean.Ramified.RType.curried` | 2 |
| `GebLean.Ramified.curryInterp` | 3 |
| `GebLean.Ramified.holeSig` | 2 |
| `GebLean.Ramified.holeConstSig` | 2 |
| `GebLean.Ramified.defnSig` | 2 |
| `GebLean.Ramified.DefnShape` | 1 |
| `GebLean.Ramified.MrecShape` | 1 |
| `GebLean.Ramified.FrecShape` | 1 |
| `GebLean.Ramified.IdentShape` | 1 |
| `GebLean.Ramified.identEndo` | 1 |
| `GebLean.Ramified.RIdent` | 1 |
| `GebLean.Ramified.RIdent.defn` | C |
| `GebLean.Ramified.RIdent.mrec` | C |
| `GebLean.Ramified.RIdent.frec` | C |
| `GebLean.Ramified.RIdent.interp` | 3 |
| `GebLean.Ramified.appChain` | 2 |
| `GebLean.Ramified.appChain_curryInterp` | 3 |
| `GebLean.Ramified.appChain_stdConstructorInterp` | 3 |
| `GebLean.Ramified.RIdent.interp_eq_appChain_curryInterp` | 3 |
| `GebLean.Ramified.identSig` | 2 |
| `GebLean.Ramified.identConstSig` | 2 |
| `GebLean.Ramified.higherOrder` | 2 |
| `GebLean.Ramified.RMRecCat` | 1 |
| `GebLean.Ramified.identHom` | 2 |
| `GebLean.Ramified.identHom_eval` | 3 |

Excluded: `RType.curried_nil` and `RType.curried_cons`, `simp`
lemmas; `IdentDir` and `identTarget`, the direction and index data of
`identEndo`; `RIdent.interpStep`, the per-clause step of
`RIdent.interp`; `defnModel`, `childEnv`, `envHead` and `envLast`,
model and environment constructions; and `higherOrderModel`, whose
only role is to be `higherOrder`'s standard-model field, which
`standardModel` reads off.

`GebLean/Ramified/OmegaShift.lean`, 21 of 66 candidates:

| Declaration | Clause |
| --- | --- |
| `GebLean.Ramified.RType.omegaShift` | 2 |
| `GebLean.Ramified.kappaHatIdent` | 2 |
| `GebLean.Ramified.kappaHatIdent_interp` | 3 |
| `GebLean.Ramified.kappaHat` | 2 |
| `GebLean.Ramified.kappaHat_interp` | 3 |
| `GebLean.Ramified.RType.objTarget` | 2 |
| `GebLean.Ramified.RType.domains` | 2 |
| `GebLean.Ramified.cLiftArrow` | 2 |
| `GebLean.Ramified.cLiftArrow_interp` | 3 |
| `GebLean.Ramified.cLift` | 2 |
| `GebLean.Ramified.kappaHatFull` | 2 |
| `GebLean.Ramified.kappaHatFull_interp` | 3 |
| `GebLean.Ramified.canonIdent` | 2 |
| `GebLean.Ramified.applyCanon` | 2 |
| `GebLean.Ramified.applyCanon_interp` | 3 |
| `GebLean.Ramified.kappaIdent` | 2 |
| `GebLean.Ramified.kappaIdent_interp` | 3 |
| `GebLean.Ramified.deltaIdent` | 2 |
| `GebLean.Ramified.deltaIdent_interp` | 3 |
| `GebLean.Ramified.RIdent.interp_defn` | R |
| `GebLean.Ramified.RIdent.mrec_interp` | R |

`RIdent.interp_defn` and `RIdent.mrec_interp` are the reduction rules
of the explicit-definition and monotonic-recurrence schemas, so the
`R` exception covers them where they are declared. Excluded:
`kappaHatStep` and `kappaHatTuple`, a step function and the tuple
assembling `kappaHat`, with `kappaHatStep_interp` and
`kappaHat_recurse_id`; the `*Aux` auxiliaries `cLiftAux` and
`deltaAux` with their lemmas; the term-level application helpers
`defnApp`, `appPrefixVars` and `appArgs` with their evaluation
lemmas; the environment constructions `snocEnv` and its heterogeneous
lemmas; the cast lemmas `RIdent.mrec_cast`,
`RIdent.interp_omega_cast`, `RIdent.interp_single_cast`,
`cast_arrow_apply`, `cast_curryInterp_snoc`; the `RType` structural
lemmas `mk_arrow_eq`, `mk_omega_eq`, `mk_o_eq`, `curried_domains`,
`curried_append`, `objTarget_isObj`, `objTarget_of_isObj`,
`domains_of_isObj`; `get_replicate`; the proof-support lemma
`Tm.eval_var`, which restates `Tm.eval` at a variable for use inside
this module; and `kappaHatFull_eq_kappaHatIdent`, which states an
equality between two identifiers rather than the value of a
denotation function, so fails the first conjunct of the theorem
reading above regardless of its module's `## Main statements` entry.

`GebLean/Ramified/Examples.lean`, 18 of 53 candidates:

| Declaration | Clause |
| --- | --- |
| `GebLean.Ramified.objToNat` | 3 |
| `GebLean.Ramified.ramKappa` | 2 |
| `GebLean.Ramified.ramKappa_interp` | 3 |
| `GebLean.Ramified.ramDeltaIdent` | 2 |
| `GebLean.Ramified.ramDeltaIdent_interp` | 3 |
| `GebLean.Ramified.ramAdd` | 2 |
| `GebLean.Ramified.ramAdd_interp` | 3 |
| `GebLean.Ramified.ramMul` | 2 |
| `GebLean.Ramified.ramMul_interp` | 3 |
| `GebLean.Ramified.ramSize` | 2 |
| `GebLean.Ramified.ramSize_interp` | 3 |
| `GebLean.Ramified.ramFun` | 1 |
| `GebLean.Ramified.ramComp` | 2 |
| `GebLean.Ramified.ramSucc` | 2 |
| `GebLean.Ramified.ramExp` | 2 |
| `GebLean.Ramified.ramExp_interp` | 3 |
| `GebLean.Ramified.ramTwoPow` | 2 |
| `GebLean.Ramified.ramTwoPow_interp` | 3 |

The ten operations and their seven interpretation lemmas are §4.1
item 5's ladder; `ramFun` enters as the named sort `o → o` at which
`ramComp` and `ramExp` are stated, so that their rendered types carry
no unrendered name. Excluded: every per-clause step
identifier and hole-index table (`addZeroStep`, `addSuccStep`,
`ramAddSteps`, `mulZeroStep`, `mulSuccStep`, `mulSteps`, `mulStep`,
`mulHoleIdx`, `sizeZeroStep`, `sizeSuccStep`, `sizeSteps`,
`ramExpBase`, `ramExpStep`, `ramExpSteps`, `ramExpBaseHoleIdx`,
`ramExpStepHoleIdx`, `ramTwoPowStep`, `deltaHoleIdx`), the
environments `addEnv`, `mulEnv` and `sizeEnv`, the term
abbreviations `tmZero` and `tmSucc`, the transport lemmas
`objToNat_cast` and `objToNat_heq`, and the carrier-level and
recurrence-level stages of the interpretation proofs
(`freeAlgToNat_ramAdd_recurse`, `ramAdd_interp_env`,
`ramAdd_interp_carrier` and their `ramMul`, `ramSize`, `ramExp` and
`ramTwoPow` counterparts, and `kappaHatIdent_objToNat`).

### Part II chapter 5: the characterization

`GebLean/Ramified/Soundness/Collapse.lean` and
`GebLean/Ramified/Characterization.lean`, endpoint declarations only,
7 in total, all under clause 5:

| Declaration | Module |
| --- | --- |
| `GebLean.Ramified.SynCatFO` | `Soundness/Collapse.lean` |
| `GebLean.Ramified.collapseFunctor` | `Soundness/Collapse.lean` |
| `GebLean.Ramified.collapseFunctor_faithful` | `Soundness/Collapse.lean` |
| `GebLean.Ramified.ramified_definability` | `Characterization.lean` |
| `GebLean.Ramified.collapseKFunctor` | `Characterization.lean` |
| `GebLean.Ramified.collapseKFunctor_faithful` | `Characterization.lean` |
| `GebLean.Ramified.ramified_definability_kSim` | `Characterization.lean` |

No other declaration of either module is covered; §4.3 places their
internals outside Part II.

## References

Bibliographic data for `GebLeanDocs/Bibliography.lean` (Task 1.2
Step 1), verified against Crossref by DOI. `month` is `Option`, so
`none` is legal where Crossref records no month.

| Key | Type | Journal or book | Volume | Number | Pages | Year, month | DOI |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `leivant3` | `Article` | Annals of Pure and Applied Logic | 96 | 1-3 | 209-229 | 1999, March | `10.1016/S0168-0072(98)00040-2` |
| `leivant1` | `InProceedings` | Feasible Mathematics II | — | — | n/a | 1995 | `10.1007/978-1-4612-2566-9_11` |
| `bellantoniCook` | `Article` | Computational Complexity | 2 | 2 | 97-110 | 1992, June | `10.1007/BF01201998` |
| `clote` | `InProceedings` | Handbook of Computability Theory | — | — | n/a | 1999 | `10.1016/S0049-237X(99)80033-0` |
| `ritchie` | `Article` | Transactions of the American Mathematical Society | 106 | 1 | 139-173 | 1963, none | `10.1090/S0002-9947-1963-0158822-2` |
| `dalLagoMartiniZorzi` | `InProceedings` | Proceedings DICE 2010 (EPTCS 23) | — | — | n/a | 2010 | `10.4204/EPTCS.23.4` |

Author lists and titles are in the spec's References section. The
`booktitle` for the three `InProceedings` entries is the "Journal or
book" column above; `clote`'s `series` is "Studies in Logic and the
Foundations of Mathematics", which Crossref records alongside the
handbook title. `InProceedings` carries no `pages` field, hence "n/a";
the page ranges remain in the spec's References section, which is
prose. `url` takes `https://doi.org/<DOI>`.
