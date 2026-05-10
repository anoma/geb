# geb-lean process bootstrap (monorepo-aware)

> **Supersedes**:
> [`2026-05-07-process-bootstrap-design.md`](2026-05-07-process-bootstrap-design.md).
> The 2026-05-07 spec assumed geb-lean was a standalone git repo;
> this revision incorporates the monorepo-subdirectory reality.

**Date drafted**: 2026-05-09.
**Authoring**: drafted by Claude through brainstorming with the
user; subject to fresh-context adversarial review before approval
(per the discipline being instituted in this very document).

## Repository structure

The geb-lean codebase lives in a subdirectory of the larger
geb/ monorepo. On the developer's local checkout:
`/home/terence/git-workspaces/geb`. On `origin`: the GitHub
repository under `<owner>/geb`. The monorepo also contains:
`geb-agda/`, `geb-idris/`, `src/` (Common Lisp), `test/`
(Common Lisp), `docs/`, plus parent-level files (`Makefile`,
`geb.asd`, `README.md`, `LICENSE`, `.github/workflows/ci.yml`,
`.github/workflows/docs.yml`, `.gitignore`).

Throughout this spec, "the parent repo" means the geb/ git
repository. "geb-lean" means the `geb-lean/` subdirectory of it.

The refactor's content changes are scoped to `geb-lean/` only:

- `geb-lean/CLAUDE.md`
- `geb-lean/.claude/{settings.json, rules/*.md}`
- `geb-lean/scripts/{check-axioms.sh, check-jj-setup.sh,`
  `pre-push.sh, hooks/{block-mutating-git.sh,`
  `check-signing-key.sh}}`
- `geb-lean/lakefile.toml` additions (`lintDriver`)
- `geb-lean/scripts/nolints.json` (lake-lint baseline)
- `geb-lean/{TODO.md, README.md (new)}`
- `geb-lean/docs/{process.md, index.md, lean-resources.md}`
- `geb-lean/docs/superpowers/specs/*` (this spec lives here)
- `geb-lean/plans/*` (the implementation plan lives here)
- `geb-lean/.markdownlint-cli2.jsonc`

The refactor's cross-cutting infrastructure operates on the
parent `geb/`:

- `geb/.github/workflows/markdown-lint.yml` (new;
  path-filtered to `geb-lean/**`)
- `geb/.github/workflows/lean_action_ci.yml` (promoted from
  `geb-lean/`; path-filtered)
- `geb/.gitignore` (modified to permit
  `geb-lean/.claude/{settings.json, rules/}`)
- `geb/.jj/` (created by `jj git init --colocate` at parent)
- Per-repo jj config on parent (`git.private-commits`,
  `remotes.origin.fetch-tags`)
- Parent's `main`: cutover commit + signed `cutover-YYYY-MM-DD`
  tag
- Parent's GitHub Rulesets: branch protection on `main` +
  tag protection on `cutover-*`
- Parent's `geb/README.md`: brief addition near the top pointing
  at `geb-lean/README.md`

The refactor leaves the following unchanged:

- `geb-agda/`, `geb-idris/`, `src/`, `test/`, `geb.asd`,
  `Makefile` (other subprojects)
- Parent's existing `geb/LICENSE` (GNU General Public License
  version 3; geb-lean inherits it)
- Parent's existing `geb/.github/workflows/{ci.yml, docs.yml}`
  (Common Lisp workflows)
- Inert `geb-lean/.github/workflows/{update.yml,`
  `create-release.yml}` (forward-prep for eventual split-out;
  out of scope for this refactor)

Append-only-main-from-cutover-forward applies to the parent's
`main`, not to a `geb-lean/`-only path subset. This is a
project-wide policy commitment binding all subprojects, not a
geb-lean-internal one. Other subprojects' contributors operate
under the same rule.

A potential split-out (treating geb-lean as its own git repo) is
out of scope.

## Context

`geb-lean` is the Lean 4 + mathlib subdirectory of the geb
monorepo where the user's ongoing experimental and exploratory
formalisation of Geb takes place. Over its lifetime it has
accumulated:

- Substantial implemented mathematical content (quivers,
  semicategories, category-judgment encodings, polynomial /
  W- / M-types, profunctors, endofunctor CCC,
  internal-presheaf Grothendieck construction, tree calculus
  Phase 2, the K^sim hierarchy, the ER ↔ K^sim_2 equivalence
  programme, the KArith library, CSLib integration).
- A 704-line `CLAUDE.md` mixing always-on hard rules,
  Lean-coding conventions, project-specific mathematical
  disciplines, and a long list of mathlib / category-theory
  reference links.
- A `.session/workstreams/` directory holding approximately 78
  markdown files of varying age and currency, plus a Claude-
  harness task list of approximately 533 numbered entries (most
  completed, several stale).
- A `README.md` whose contents reflect an early-scaffolding
  state of the repository and no longer accurately describe
  what the repository is or contains.

Concurrently, the user has designed a sibling repository at
`geb-mathlib` (specification at
`docs/superpowers/specs/2026-05-04-geb-mathlib-bootstrap-design.md`
within that repository; plan at
`docs/superpowers/plans/2026-05-04-geb-mathlib-bootstrap-plan.md`),
intended as the curated, mathlib-upstreamable home for content
that proves itself out in this repository.

This document specifies a process refactor of `geb-lean` that
adopts the parts of the `geb-mathlib` design that do not depend
on upstream-eligibility infrastructure — the layered
`CLAUDE.md` + `.claude/rules/*.md` + `docs/process.md`
architecture, the single `TODO.md` index, the jj-based workflow
with `main`-append-only / `integration`-regenerated /
topic-branch model, the adversarial-review discipline for specs
and plans, and the `docs/index.md` topological narrative —
adapted to this repository's identity as an active
experimentation hub with substantial existing content. It does
**not** adopt the `geb-mathlib` design's upstream-eligibility
infrastructure (`Geb/Mathlib/` vs `Geb/Internal/` split,
floodgate-CI lint, PR-extraction script, test-repo simulation,
`downstream-reports` registration, `upstreaming-dashboard-action`).

## Goals

The refactor delivers a repository whose process infrastructure
matches the layered, jj-based, adversarial-review-disciplined
pattern designed for `geb-mathlib`, adapted to this
repository's character. Concretely:

1. Replace the monolithic 704-line `CLAUDE.md` with a layered
   system: slim `CLAUDE.md` (≤ 200 lines), path-scoped
   `.claude/rules/*.md` files, and a `docs/process.md`
   rationale layer.
2. Stand up a single `TODO.md` at repository root as the only
   authoritative index of in-flight workstreams, with two
   top-level sections: *Active in geb-lean* and *To be done
   in geb-mathlib (not pending here)*.
3. Define a workstream-triage method for the existing
   `.session/workstreams/` content, executed during the
   implementation plan, that classifies every entry and
   dispatches it to the appropriate destination.
4. Adopt jj in colocated mode (`jj git init --colocate`) at the
   parent `geb/` repo root, preserving the existing GitHub
   remote and the existing git history unchanged; wire the
   `block-mutating-git` PreToolUse hook and the
   `check-signing-key` SessionStart hook in
   `geb-lean/.claude/settings.json`.
5. Adopt the `main`-append-only / `integration`-regenerated /
   topic-branch model, forward-only — no retroactive history
   rewriting.
6. Encode the adversarial-review process for specs and plans as
   a hard rule, with the procedure documented in
   `docs/process.md`.
7. Backfill `docs/index.md` with topological narrative entries
   for the major existing implemented material; subsequent
   workstreams append entries on completion.
8. Author a new `geb-lean/README.md` that accurately describes
   the subdirectory and its place in the monorepo; add a brief
   pointer near the top of the parent `geb/README.md` pointing
   at `geb-lean/README.md`.
9. No `geb-lean/LICENSE` is created: geb-lean falls under the
   parent `geb/LICENSE` (GNU General Public License version 3)
   by inheritance. Spec/CLAUDE.md/README references to licence
   point at `../LICENSE`. The in-flight A5 commit's
   `geb-lean/LICENSE` (Apache 2.0) is removed in the cleanup
   task that opens the new plan.
10. Add a vendored `scripts/check-axioms.sh` (derivative of the
    `lean4-skills` plugin's `check_axioms_inline.sh` with
    `Classical.choice` excluded from the allowlist), wired into
    CI and the pre-push checklist.
11. Add a `markdown-lint.yml` GitHub Actions workflow (at the
    parent level, path-filtered to `geb-lean/**`) plus a shared
    `geb-lean/.markdownlint-cli2.jsonc` configuration.
12. Lift the mathlib / category-theory / CSLib resource link list
    out of `CLAUDE.md` into a public-facing
    `docs/lean-resources.md`.
13. Retire `.session/` once every workstream entry has been
    triaged and dispatched.

## Non-goals

The refactor deliberately excludes:

- **Upstream-eligibility infrastructure**: no `GebLean/Mathlib/`
  vs `GebLean/Internal/` directory split, no floodgate-CI lint,
  no `extract-pr.sh` script, no `upstreaming-dashboard-action`,
  no `downstream-reports` registration. These are part of the
  `geb-mathlib` repository's value proposition and do not apply
  to this repository's experimental focus.
- **Test-repo simulation**: the `geb-mathlib` design uses
  throwaway numbered test repositories to discover process bugs
  before the real repository exists. This repository already
  exists; the discipline for catching process bugs here is the
  adversarial-review cycle on the spec and plan plus the
  verification checklist on execution.
- **Namespace rename**: the `GebLean` namespace is preserved.
  Renaming to `Geb` (which `geb-mathlib` uses) would touch
  every source file and is not part of the refactor.
- **Retroactive history rewriting**: `main`'s past commits are
  not rebased, squashed, or otherwise restructured. The
  `main`-append-only rule applies forward-only.
- **Migration of code from this repository to `geb-mathlib`**:
  such migration is a separate workstream, outside this
  refactor.
- **Mass docstring rewrite**: the new `.claude/rules/lean-coding.md`
  rules bind subsequent edits; existing files are not rewritten as
  part of this refactor unless directly touched.
- **Standalone git repo split-out**: geb-lean will remain a
  subdirectory of the geb/ monorepo for the duration of this
  refactor. An eventual split-out is deferred.

## Scope boundary

This refactor changes process and infrastructure files only. It
does not modify any `.lean` source under `GebLean/` or `test/`
except as incidental to lakefile-option changes (which propagate
via the build, not via source edits). Content changes are
scoped to `geb-lean/`; cross-cutting infrastructure changes are
scoped to the parent `geb/` as enumerated in § Repository
structure above.

## New file and directory layout

Items marked `+` are new, `~` are modified, `-` are removed.
Items prefixed `[parent]` live outside `geb-lean/`.

```text
[parent] geb/
├── .github/
│   └── workflows/
│       ├── ci.yml               (existing; unchanged)
│       ├── docs.yml             (existing; unchanged)
│       ├── lean_action_ci.yml   (+ promoted from geb-lean/)
│       └── markdown-lint.yml    (+ new; path-filtered)
├── .gitignore                   (~ permit geb-lean/.claude/{…})
├── .jj/                         (+ created by jj; git-ignored)
├── README.md                    (~ brief pointer near top)
└── LICENSE                      (existing; unchanged)

geb-lean/
├── .claude/
│   ├── docs/                    (existing; unchanged)
│   ├── memory/                  (existing; unchanged)
│   ├── settings.json            (+ committed; wires hooks)
│   ├── settings.local.json      (existing; unchanged)
│   ├── tools/                   (existing; unchanged)
│   └── rules/                   (+ new directory)
│       ├── lean-disciplines.md  (+ no paths; unconditional)
│       ├── lean-coding.md       (+ paths: ["**/*.lean"])
│       ├── markdown-writing.md  (+ paths: ["**/*.md"])
│       └── ci-and-workflow.md   (+ paths: …)
├── .gitignore                   (existing; all .claude-related
│                                   patterns removed by cleanup
│                                   task C-gitignore-revert;
│                                   otherwise unchanged)
├── .markdownlint-cli2.jsonc     (existing; rewritten by
│                                   cleanup task
│                                   C-markdownlint-config-rewrite
│                                   per § .markdownlint-cli2.jsonc)
├── .github/
│   └── workflows/
│       ├── lean_action_ci.yml   (- moved to parent)
│       ├── markdown-lint.yml    (- removed; superseded by
│       │                           parent geb/.github/
│       │                           workflows/markdown-lint.yml)
│       ├── update.yml           (existing; inert; unchanged)
│       └── create-release.yml   (existing; inert; unchanged)
├── CLAUDE.md                    (~ rewritten, ≤ 200 lines)
├── README.md                    (+ new; geb-lean identity)
├── TODO.md                      (+ active workstreams index)
├── lakefile.toml                (~ minor adjustments)
├── lean-toolchain               (existing; unchanged)
├── lake-manifest.json           (existing; unchanged)
├── GebLean.lean                 (existing; unchanged)
├── GebLean/                     (existing; unchanged)
├── test/                        (existing; unchanged)
├── docs/
│   ├── index.md                 (+ topological narrative)
│   ├── process.md               (+ rationale layer)
│   ├── lean-resources.md        (+ link list lifted)
│   ├── research/                (existing; unchanged)
│   └── superpowers/
│       ├── specs/               (existing; new entries)
│       └── plans/               (existing; new entries)
├── plans/                       (existing; carries the 2026-05-07
│   │                               plan and will carry the
│   │                               2026-05-09 monorepo-aware plan)
├── scripts/                     (existing; created by
│   │                               in-flight A2-prep mkdir;
│   │                               carried forward)
│   ├── check-axioms.sh          (+ vendored)
│   ├── check-jj-setup.sh        (+ on-boarding verifier)
│   ├── nolints.json             (existing; lake-lint baseline
│   │                               ratchet; ~919 entries;
│   │                               updated by
│   │                               lake lint -- --update
│   │                               when the baseline shrinks)
│   ├── pre-push.sh              (+ manual checklist runner)
│   └── hooks/
│       ├── block-mutating-git.sh  (+ PreToolUse)
│       └── check-signing-key.sh   (+ SessionStart)
└── .session/                    (- retired post-triage)
```

`jj git init --colocate` runs at the parent `geb/` root.
It creates `geb/.jj/` with a self-contained
`geb/.jj/.gitignore` (containing `/*`), which excludes `.jj/`
from git's view without modifying any `.gitignore` files.
Verified empirically against jj 0.40 (initial) and 0.41
(re-verified) and against the jj documentation at
<https://docs.jj-vcs.dev/latest/git-compatibility/>.

## CLAUDE.md content

`CLAUDE.md` is the slim always-on layer. Target: under 200
lines per Anthropic's recommendation
(<https://code.claude.com/docs/en/memory>: "longer files consume
more context and reduce adherence"). This is a target, not a
documented cliff; if a draft exceeds it, the spec specifies a
priority order for cuts (see "Priority order for cuts" below).
Every section either ports content from the `geb-mathlib`
skeleton, adapts it to this repository's identity, or is fresh
(no analogue in the new repository's design).

**Nested `CLAUDE.md` are forbidden.** Anthropic auto-discovers
`CLAUDE.md` and `CLAUDE.local.md` files in subdirectories,
which would silently bypass the rule-priority structure of
`.claude/rules/`. Per-area instructions go in
`.claude/rules/<name>.md` with `paths:` frontmatter, not in
nested `CLAUDE.md` files. The single root `CLAUDE.md` is the
only `CLAUDE.md` in the repository. This rule is replicated in
`.claude/rules/markdown-writing.md`.

### Repository structure note in CLAUDE.md

The slim `CLAUDE.md` opens with a brief "Repository structure"
line near the top, after the title, before the existing
sections: "geb-lean/ is a subdirectory of the geb/ monorepo
(parent repo at `..`); cross-cutting infrastructure (CI
workflows, `.gitignore`, jj colocated init, GitHub Rulesets,
signed cutover tag) lives at the parent level; code and
per-project content are scoped to geb-lean/." This goes near
the top, after the title, before the existing CLAUDE.md
sections.

### Per-section line budget (target ~180 lines, with margin)

| Section | Lines |
| --- | --- |
| Header + identity | 5 |
| Repository structure note | 6 |
| Project status | 5 |
| Hard rules (~10 bullets) | 22 |
| Phase-driven workflow table | 18 |
| Style guidelines (with banned-word pointer) | 8 |
| Repo structure | 8 |
| Constructive-only Lean code | 6 |
| Specs and plans on the feature branch | 7 |
| GebLean-specific disciplines (three items) | 18 |
| Cross-reference for spec/plan authorship | 4 |
| Tooling | 18 |
| Skill-creation pointer | 4 |
| Pointers | 8 |
| Section spacing and markdown overhead | ~50 |
| **Total** | **~187** |

### Priority order for cuts (if budget is exceeded)

1. Move the banned-word example list out of CLAUDE.md (it lives
   canonically in `.claude/rules/markdown-writing.md` already).
2. Compress the phase-driven workflow table to one line per
   phase.
3. Move tooling-detail bullets to `docs/process.md`.

Sections in order:

1. **Project header and one-paragraph identity** (fresh): one
   paragraph describing the repository as an experimental
   Lean 4 + mathlib formalisation hub for Geb, the active
   experimentation counterpart to the curated `geb-mathlib`
   repository. Pointer to `README.md` for full identity and
   `docs/process.md` for the rationale behind each rule.
2. **Repository structure note** (new): geb-lean/ is a
   subdirectory of the geb/ monorepo; cross-cutting
   infrastructure lives at the parent level.
3. **Project status** (fresh): five lines describing the
   repository's role, the relationship to `geb-mathlib`, and
   pointers to `TODO.md` and `docs/index.md`.
4. **Hard rules — must not violate** (adapted): the bullets
   that bind every session.
   - No `git push` without user line-by-line review. The same
     human-gate rule applies symmetrically to `gh` write
     operations (`gh pr create`, `gh pr merge`, `gh release
     create`, `gh issue create`, `gh issue close`, etc.) since
     these bypass local git and the PreToolUse hook does not
     see them.
   - No raw mutating `git` subcommands; the PreToolUse hook
     enforces a closed-allowlist default-deny policy; use `jj`.
   - No LLM-drafted text in user-facing channels (PR
     descriptions, GitHub comments, issue threads).
   - Generic user references in committed text.
   - No `noncomputable`, no `axiom`, minimise `Classical` (see
     Constructive-only Lean code below).
   - Specs and plans are adversarially reviewed before user
     review (see Adversarial review of specs and plans below,
     and the full procedure in `docs/process.md`).
   - No `admit` anywhere — ever.
   - No `sorry` in any commit. (`sorry` is a permitted transient
     working tool between commits, including with skill-driven
     `sorry`-filling tools, but committed code must build
     cleanly under our warnings-as-errors policy, which fails
     on `sorry`.)
   - Use `_` (underscore) — not `sorry` — when you want to
     surface a hole's type as a goal-display error.
5. **Phase-driven workflow** (ported): table of phases
   (brainstorming / writing-plan / executing-plan / Lean code
   work / mathlib search / pre-commit / receiving review)
   mapped to always-on skills and helpers. Same structure as
   `geb-mathlib`'s, including the `lean4` sub-skill table.
6. **Style guidelines** (adapted): formal, mathematical, dry,
   unopinionated register. The canonical list of value-laden
   adjectives to avoid lives in
   `.claude/rules/markdown-writing.md`; CLAUDE.md gives a few
   examples (`key`, `important`, `core`, `complex`)
   with a pointer to the full list. Detailed prose-tone rules
   live in `.claude/rules/markdown-writing.md` and
   `.claude/rules/lean-coding.md`. The rule binds repository
   content; conversational chat is unrestricted.
7. **Repo structure** (fresh): one-line per fact. `GebLean/`
   namespace; `GebLean/Utilities/` for shared helpers;
   `GebLean.lean` as index module. `main` append-only;
   `integration` regenerated fan-in view; topic branches per
   workstream (`feat/`, `fix/`, `refactor/`, `chore/`, `docs/`,
   `bump/`). `TODO.md` at repository root with two top-level
   sections.
8. **Constructive-only Lean code** (ported): no
   `noncomputable`, no `axiom`; minimise `Classical`.
   `scripts/check-axioms.sh` flags non-allowlisted axioms in
   CI and pre-push.
9. **Specs and plans live on the feature branch** (ported):
   each workstream's spec, plan, and code co-evolve on the
   same topic branch. Spec at
   `docs/superpowers/specs/<date>-<topic>-design.md`; plan at
   `plans/<date>-<topic>-plan.md`.
   Adversarial-review iterations and self-review fixes are
   commits on the same branch.
10. **GebLean-specific disciplines** (fresh): one paragraph
    each. The rule text lives in
    `.claude/rules/lean-disciplines.md`, which is loaded
    unconditionally (no `paths:` frontmatter), so the rules
    apply during spec / plan authorship as well as during
    `.lean` editing. CLAUDE.md item 10 is the human-readable
    index.
    - Literature-citation discipline (transcription
      workstreams).
    - Bottom-up named-composite discipline for categorical
      equivalences.
    - Non-negotiable interfaces for categories formalising
      pre-existing mathematical objects.
11. **Cross-reference to file-edit-only Lean rules**: build
    discipline, mathlib comment / docstring rules, Lean idioms,
    and other rules that apply only when editing `.lean` source
    live in `.claude/rules/lean-coding.md`
    (`paths: ["**/*.lean"]`). That file loads automatically
    when Claude reads a `.lean` file. No manual cross-reference
    is required for the disciplines (those are in the
    unconditionally-loaded `lean-disciplines.md`); this item
    exists in CLAUDE.md only as a navigation pointer for human
    readers.
12. **Tooling** (adapted): the entries below name
    **phase-default skills** (skills invoked at specific phases
    of work; they load on demand, not at session start) and
    **always-loaded layers** (`CLAUDE.md` and
    `.claude/rules/*.md` files without `paths:` frontmatter,
    present in context from session start). The two are not
    the same; do not conflate "always-on by phase expectation"
    with "always-loaded into context." VCS (`jj` v0.41+ in
    colocated mode at the parent `geb/` root;
    lease-protected pushes; `.jj/` is git-ignored
    automatically by jj; do NOT run `git clean -xdf`, which
    deletes `.jj/`); build (`lake`); CI
    (`lean_action_ci.yml` and `markdown-lint.yml` at the
    parent level; `update.yml` and `create-release.yml`
    inert at `geb-lean/.github/workflows/`); linters
    (`markdownlint-cli2`, `lake lint`,
    `scripts/check-axioms.sh`); skills (`superpowers:*`,
    `lean4:*`, `claude-md-management:*`, `code-review:*`,
    `pr-review-toolkit:*`, `commit-commands:*`,
    `security-review`, plus `dispatching-parallel-agents`,
    `systematic-debugging`, `test-driven-development`,
    `remember`, `session-report`, `fewer-permission-prompts`).
13. **When to consider creating a project-specific skill**
    (ported): three lines describing the friction-driven
    default-to-wait posture, with reference to
    `skill-creator:skill-creator`.
14. **Pointers** (adapted): navigation links to
    `docs/process.md`, `.claude/rules/`, `docs/index.md`,
    `docs/lean-resources.md`, and the refactor's own spec and
    plan paths.

Length verification is part of the refactor's success criteria
(item 5 of the checklist).

## .claude/rules/lean-disciplines.md

**No `paths:` frontmatter** — this file is loaded
unconditionally, on every Claude Code session, regardless of
which files are read. The rules in this file apply to spec /
plan authorship as well as to `.lean` file editing, so they
cannot be path-scoped to `.lean` files alone.

The unconditional-load mechanism for `.claude/rules/*.md` files
without `paths:` is verified against
<https://code.claude.com/docs/en/memory>: rules without
path-scoping load at session start with the same priority as
`CLAUDE.md`.

Content sections:

1. **Hole-marking discipline**: `_` for unsolved goals
   (surfaces the type as an error); `sorry` permitted as a
   transient working tool only — committed code must build
   under warnings-as-errors and therefore cannot contain
   `sorry`; `admit` forbidden everywhere, always. The
   warnings-as-errors mechanism is
   `moreLeanArgs = ["-DwarningAsError=true"]` in
   `lakefile.toml`, which promotes `declaration uses 'sorry'`
   (and every other warning-class diagnostic) into a build
   error at the Lean kernel level.
2. **Constructive-only Lean code**: no `noncomputable`, no
   `axiom`; minimise `Classical`. `Quotient` / `Quot`
   constructive API only; `Quot.out` / `Quotient.out` (which
   require `Classical.choice`) are avoided.
   `scripts/check-axioms.sh` is the mechanical check.
3. **Literature-citation discipline**. In transcription
   workstreams (e.g. the ER ↔ K^sim_2 equivalence, which
   transcribes Tourlakis 2018 / Wagner-Wong /
   Grzegorczyk-hierarchy literature), every planned function,
   definition, or theorem in a plan document carries a
   reference to the literature proposition or in-codebase
   lemma it corresponds to; every implemented function,
   definition, or theorem includes the literature reference in
   its docstring. Citations are specific (e.g.
   "Tourlakis 2018 §0.1.0.27 (3)") and reference the
   project's research documents in `docs/research/` for the
   cross-reference network.
4. **Bottom-up named-composite discipline** for categorical
   equivalences. When building a new categorical structure
   that is to be proven equivalent to an existing one, never
   add a constructor or morphism to the new category before
   its image in the target category has been built and named
   as a `def` (with a `@[simp]` interp lemma). Workflow:
   identify the image; if not present, build it bottom-up as a
   composition of atomic constructors of the target category;
   give it a name and prove its interp lemma in `Utilities/`;
   only then add the corresponding constructor (or helper) to
   the new category, with its translation function pointing
   directly at the named composite. If a proposed construct
   cannot be built ultimately out of compositions of the
   target's atomic generators, that is a signal not to add
   it — not to build a workaround.
5. **Non-negotiable interfaces** for categories formalising
   pre-existing mathematical objects. The interface (objects,
   primitive constructors, generators) is fixed by the
   external mathematical source and is not a design choice
   open to the implementation. Implementation design (proof
   strategies, auxiliary inductives, choice of named
   composites) may change freely; interface changes are not a
   valid response to implementation difficulty. If
   implementation gets stuck, the correct moves are: re-examine
   the implementation strategy; strengthen `Utilities/`
   infrastructure; surface the obstruction for discussion.
   Weakening or redefining the interface so the implementation
   becomes easier is not a valid move.

## .claude/rules/lean-coding.md

YAML frontmatter:

```yaml
paths:
  - "**/*.lean"
```

Loaded automatically when Claude reads a `.lean` file (per
<https://code.claude.com/docs/en/memory>: path-scoped rules
trigger on file reads matching the pattern). Content
sections:

1. **Build discipline**: `lake build` and `lake test` after
   every change; never `lake env lean` (which fails to pick
   up project options); never `lake clean` (would force
   mathlib rebuild). Fix first errors first. Write modules
   one definition at a time. Work both forwards and
   backwards. Try one proof step at a time. Use `Write` (not
   shell heredocs) for experiments. Test within the codebase,
   not in `/tmp`.
2. **Comment and docstring rules**: module `/-! ... -/`
   mandatory after imports; declaration `/-- ... -/` mandatory
   for every `def`, `structure`, `class`, `instance`, and
   major theorem; markdown and LaTeX (`$...$`, `$$...$$`)
   inside docstrings; no development-history references; no
   post-hoc axiom-free celebration. **This project is stricter
   than mathlib on `instance` docstrings**: mathlib's
   <https://leanprover-community.github.io/contribute/doc.html>
   treats `instance` docstrings as encouraged, not required;
   this project requires them, on the rationale that
   searchable docstrings on every typeclass instance pay off
   in navigability of a heavily category-theoretic codebase.
3. **Lean idioms**: `@[ext]` on structures (when it compiles);
   derive `Inhabited` / `DecidableEq` / `Repr`; `extends` is
   composition (per *Functional Programming in Lean:
   Structures and Inheritance*); use `eqToHom` / `eqToIso`
   for object equalities in categories; the
   sigma-of-dependent-fields pattern; the
   typeclass-via-interface-structure pattern; `_root_`
   namespacing for mathlib functor-vs-control-functor
   collisions; the factoring-out-lemmas technique; `grind`
   and `aesop` automation; `Plausible` for property-based
   tests.
4. **`lean4` skill mapping**: drafting from informal math
   (`lean4:draft`, `lean4:formalize`, `lean4:autoformalize`);
   proving a stated lemma (`lean4:prove`, `lean4:autoprove`);
   polishing (`lean4:golf` — phase-default post-process for
   any new proof); porting (`lean4:refactor` — phase-default
   during porting); pre-commit Lean review (`lean4:review` —
   phase-default for any Lean commit); exploration
   (`lean4:learn`); diagnosis (`lean4:doctor`); save progress
   (`lean4:checkpoint`). All `lean4` skills produce ordinary
   commits and are subject to the same warnings-as-errors gate
   as any commit; `lean4:checkpoint` cannot commit code that
   contains `sorry`. Note that "phase-default" here refers to
   *when to invoke a skill at a given phase*, not to whether
   the skill loads at session start. The always-loaded layers
   are `CLAUDE.md` and `.claude/rules/lean-disciplines.md`
   (no `paths:`), nothing else.
5. **Universe and variable hygiene**: keep universes
   polymorphic (as polymorphic as compiles); after editing a
   file with `universe` or `variable` declarations, prune any
   that are unused.
6. **No copyright or author headers in source files** —
   preserved from the existing project rule. This
   intentionally diverges from mathlib's per-file `Authors:`
   template. Licence coverage for the project lives at the
   repository-level `../LICENSE` file (GNU General Public
   License version 3, at the parent `geb/` root); per-file
   copyright headers are not required by GPLv3 for original
   GebLean code. Vendored upstream content (e.g. files copied
   verbatim from mathlib or `lean4-skills`, which carry
   Apache 2.0 notices — mathlib is Apache 2.0, a dependency
   of this GPLv3 project) preserves any per-file notices it
   carries verbatim per those upstream licences' requirements.
7. **Reminder of unconditionally-loaded disciplines**: the
   project-specific Lean disciplines (literature citations,
   bottom-up named composites, non-negotiable interfaces,
   hole marking, constructive-only) live in
   `.claude/rules/lean-disciplines.md`, which is always in
   context. They are not duplicated here; cite them by name
   from this file's docstrings as needed.

## .claude/rules/markdown-writing.md

YAML frontmatter:

```yaml
paths:
  - "**/*.md"
```

Content:

1. **Markdownlint cleanliness**: every `.md` file must pass
   `markdownlint-cli2` against `.markdownlint-cli2.jsonc`. CI
   enforces this; pre-push runs the check locally.
2. **Prose register**: formal, mathematical, dry,
   unopinionated; mathematical-paper register; refer to "the
   X-Y theorem" not "the seminal X-Y theorem"; avoid
   value-laden adjectives. Short example list (rebroadcast
   from `CLAUDE.md` § Style guidelines for ease of reference
   here).
3. **No development-history references** in any committed prose
   (specs, plans, README, docs, comments). History belongs in
   commit messages and review threads. Comments in code do not
   refer to prior states of the code or to in-progress /
   planned work.
4. **Generic user references**: "the user" / "they" / "them";
   no first names, email addresses, or autobiographical
   details in committed text. (Per-developer local state,
   e.g. user-level `jj config` for `user.name` / `user.email`
   / `signing.*`, is stored outside the repository per jj
   0.38+'s config-location model and is exempt.)
5. **No LLM-drafted user-facing text**: PR descriptions,
   GitHub issue and comment threads, and any external-facing
   message must be authored by the user. Claude may produce a
   draft clearly marked "for paraphrasing"; the final posted
   text is the user's.
6. **Line length**: ≤ 80 characters (stricter than mathlib's
   100). Enforced by `markdownlint-cli2`'s MD013 rule against
   `.markdownlint-cli2.jsonc`'s configured limit; tables and
   code blocks are exempt (long lines in those contexts are
   legitimate; the exemption is recorded in
   `.markdownlint-cli2.jsonc`).
7. **No emojis**: preserves the dry register.
8. **Link conventions**: internal links by relative path;
   external links inline.

## .claude/rules/ci-and-workflow.md

YAML frontmatter:

```yaml
paths:
  - ".github/workflows/**"
  - "scripts/**"
```

> Note: This rule applies to CI and workflow files inside the
> geb-lean subdirectory. Parent-level workflow files at
> `geb/.github/workflows/` are outside the geb-lean project's
> `paths:` scope; when editing those files, load
> `geb-lean/docs/process.md` § CI as the reference.

Content:

1. **Workflow conventions**: the `lean_action_ci.yml` and
   `markdown-lint.yml` workflows live at the parent
   `geb/.github/workflows/` level and are path-filtered to
   `geb-lean/**`; `update.yml` and `create-release.yml`
   remain inert at `geb-lean/.github/workflows/` as forward
   prep. Third-party action references are SHA-pinned where
   the security gain warrants the maintenance cost;
   major-version pinning is acceptable for actions whose
   maintainers have a release-discipline track record.
2. **Pre-push checklist**: `scripts/pre-push.sh` runs
   `lake build`, `lake test`, `lake lint`,
   `markdownlint-cli2 --config .markdownlint-cli2.jsonc
   --no-globs '**/*.md'`,
   `bash scripts/check-axioms.sh GebLean/ test/`. Note: the
   single-quotes around `'**/*.md'` are load-bearing — without
   them, the shell would expand the glob before
   `markdownlint-cli2` sees it, defeating `--no-globs`. The
   same applies wherever a glob is passed: always quote the
   glob argument. The script additionally surfaces user-driven
   gates as reminders:
   - `lean4:golf` and `lean4:review` ran on changed Lean
     code;
   - line-by-line user diff review of every change about to
     be pushed.
3. **Hook-script conventions**: `scripts/hooks/*.sh` exit 0
   by default; explicit blocks exit 2 with a stderr message.
   `block-mutating-git.sh` blocks raw mutating `git` and
   translates blocked commands to their `jj` equivalents in
   stderr. `check-signing-key.sh` warms the gpg-agent or
   ssh-agent at session start.
4. **Commit-message convention**: adopt mathlib's
   `<type>(<optional-scope>): <subject>` form (`feat | fix |
   doc | style | refactor | test | chore | perf | ci`),
   imperative present, no capital, no period. Note: the
   commit-message type is `doc:` (singular, mathlib-mandated)
   while the topic-branch prefix for documentation work is
   `docs/<topic>` (plural, project-local convention adopted
   from `geb-mathlib`). The two forms are deliberately
   distinct and used in distinct contexts
   (`git commit -m "doc: ..."` vs branch name `docs/<topic>`).
   Consistency with `geb-mathlib` and mathlib motivates the
   convention even though this repository does not currently
   target mathlib upstream. Applies forward from the cutover
   commit (see § Branch model); pre-cutover commits remain in
   their original forms (mixed style, per `git log`).

## docs/process.md

Index-shaped at first. Sections, each a short paragraph
(~ 5–10 lines) referring to the spec and the path-scoped rule
files for full text:

1. **Repository structure.** geb-lean is a subdirectory of the
   geb/ monorepo. jj is colocated at the parent. Hooks live
   at `geb-lean/scripts/hooks/`. CI workflows that touch
   geb-lean live at the parent `geb/.github/workflows/`.
   Pre-push is geb-lean-scoped (builds and tests only
   geb-lean artefacts).
2. Phase-driven workflow.
3. Adversarial review of specs and plans.
4. Order of artefact production: brainstorm → spec →
   spec self-review → spec adversarial review (loop) →
   user spec review → plan → plan self-review →
   plan adversarial review (loop) → user plan review →
   execute. (See § Adversarial review of specs and plans
   below.)
5. Verify agent claims against authoritative sources.
6. Constructive-only Lean code.
7. `main` / `integration` / topic-branch model.
8. `jj` colocated mode (at the parent `geb/` root; with the
   `git clean -xdf` warning and the `.jj/.gitignore`
   self-exclusion fact).
9. Comment and docstring style.
10. Markdownlint discipline.
11. No LLM-drafted user-facing text.
12. Generic user references.
13. Process self-update mechanism.
14. **GebLean-specific: literature-citation discipline.**
15. **GebLean-specific: bottom-up named-composite
    discipline.**
16. **GebLean-specific: non-negotiable interfaces.**
17. **GebLean-specific: relationship to geb-mathlib.** What
    "to be done in geb-mathlib" means in `TODO.md`; how
    content migrates from this repository to the new one;
    why no `Mathlib/` vs `Internal/` split here.
18. **GebLean-specific: no per-file copyright or author
    headers.** Project rule preserved from the existing
    `CLAUDE.md`. The repository-level `../LICENSE` (GNU
    General Public License version 3, at the parent `geb/`
    root) covers all original GebLean code; per-file headers
    are not required by GPLv3 for original work. Vendored
    upstream content (e.g. files copied from mathlib or
    `lean4-skills`, which carry Apache 2.0 notices) preserves
    any per-file notices it carries verbatim per those
    upstream licences' requirements. Rationale for diverging
    from mathlib's per-file `Authors:` template:
    project-author preference, recorded as a deliberate
    stylistic choice rather than an oversight.

## docs/index.md

Topological narrative of implemented content. Each entry:
workstream or content area name; source-tree paths; central
concepts; dependencies on other entries; pointers to
`docs/research/` and `docs/superpowers/` artefacts where
applicable. Backfilled at refactor time with entries for the
major existing implemented material:

- Quivers, semicategories, acyclic categories
  (`GebLean.FiniteQuiver`, `GebLean.Semicategory`,
  `GebLean.AcyclicQuiver`, `GebLean.AcyclicCat`).
- Category-judgment encodings
  (`GebLean.CategoryJudgments`,
  `GebLean.DepCategoryJudgments`) and their equivalence.
- Polynomial / W- / M-types and PFunctors machinery.
- Profunctors and end machinery (`GebLean.HexagonCat`,
  profunctor utilities).
- Internal-presheaf Grothendieck equivalence
  (`PshInternalCat`, externalisation, comparison functor,
  Grothendieck construction integration).
- PshRelEdge and edge-of-presheaf machinery (endofunctor
  CCC, Yoneda extensions, Kan extensions).
- Tree calculus Phase 2 (polynomial combinators, two-sorted
  computation polynomial, PCA, confluence,
  primitive-recursive fragment status).
- K^sim hierarchy and ER ↔ K^sim_2 equivalence (Lawvere
  category construction, the `kToER` functor in flight,
  polynomial-bound infrastructure, KArith library,
  ER-A majorants). With literature citations to Tourlakis
  2018, Wagner-Wong, the Wikipedia elementary-recursive
  article.
- CSLib integration (peer dependency added; pin tracked in
  `lake-manifest.json`; usage discipline per
  `.claude/rules/lean-coding.md`).

The backfill is *adequate*, not *exhaustive*: enough that a
reader can find each major area and understand its
dependencies. Subsequent workstreams append entries on
completion; gaps fill in over time.

## docs/lean-resources.md

The mathlib / category-theory / CSLib / computability /
topos-theory link list lifted from the current `CLAUDE.md`
into a repository-internal reference document (available to
anyone with read access to the repository; no GitHub Pages
dependency). Topic-organised (the existing organisation in
`CLAUDE.md` is preserved). Linked from `CLAUDE.md`
§ Pointers and from `.claude/rules/lean-coding.md`.

## TODO.md format

```markdown
# TODO

Active workstreams in this repository. Hierarchical,
topological: parents listed first, children indented under
them. A workstream is removed from this file when its work
is complete or when it moves into the "to be done in
geb-mathlib" section. Completed content's documentation
lands in `docs/index.md`.

## Active in geb-lean

### <Workstream name>

- **Status**: <one phrase: planning | spec drafted | spec
  under review | plan drafted | plan under review | executing
  | waiting-on-X>
- **Spec**: `docs/superpowers/specs/<file>` (or "—" if not
  yet written)
- **Plan**: `plans/<file>` (or "—")
- **Scope**: <one or two sentences>
- **Next**: <the immediate next thing to do>

### <Sub-workstream of the above>

(Indented or sectioned under its parent — flexible per the
hierarchy. Children may inherit their parent's spec / plan
unless they have their own.)

## To be done in geb-mathlib (not pending here)

Items intentionally deferred until after migration to the
new repository, where the curated context there applies.
**None of the items in this section are pending in the
present repository.** Listed here so the work is not lost.

### <Item name>

- **Reason for deferral**: <why this is better done after
  migration>
- **Dependencies in geb-lean**: <what needs to be done
  here first, if anything>
- **Pointer**: <link to relevant existing material in this
  repository, if any>
```

The two-section division is structural, not just semantic:
anything in the second section is by construction not
pending here. Each entry stays small (≤ 8 lines); content
larger than this is hosted in a spec under
`docs/superpowers/specs/` and linked from the entry.

## Workstream triage method

Triage of the existing `.session/workstreams/*.md` files
(approximately 78 entries at the time of this writing) and
the related Claude-harness task list (approximately 533
numbered entries) constitutes **Milestone B**, executed after
Milestone A lands. See § Verification — definition of done
for the milestone split. Each workstream file is classified
with exactly one of these labels:

| Label | Meaning | Disposition |
| --- | --- | --- |
| `live` | Active work, currently being pursued or deliberately paused with intent to resume | Migrated to `TODO.md` § Active in geb-lean. Spec / plan / working-notes pointer preserved. |
| `live-deferred-to-geb-mathlib` | Real work better done after migration to the new repository's curated context | Migrated to `TODO.md` § To be done in geb-mathlib. |
| `completed` | Finished and merged work | Material described in `docs/index.md` if not already; `.session/` entry deleted. |
| `superseded` | Started a direction later abandoned in favour of another approach | `.session/` entry deleted. Notes on *why* superseded captured in the surviving approach's spec / plan if non-obvious. |
| `abandoned` | Explored and decided not to pursue | `.session/` entry deleted. |
| `unclear` | Cannot be classified from the entry's content alone (stale, vague, ambiguous) | Surfaced for explicit user decision; not auto-classified. |

The same scheme applies to the Claude-harness task list,
most of which rolls up into "child of workstream X (live)"
or "completed" once the workstream-level classifications are
fixed.

Triage is open-ended: each entry requires reading the file,
cross-referencing against `git log` and current source
state, and user surface-and-confirm. The plan does not bound
its duration. **Triage does not gate Milestone A** — see the
verification section's milestone split.

## Triage execution

The plan's triage block is structured as one task per
`.session/workstreams/` file, each task of the form:

> Triage `.session/workstreams/<name>.md`. Read the file.
> Cross-reference against `git log` for any commits
> referencing the workstream's topic, against current
> source-tree state, and against the Claude-harness task
> list. **Before deletion**: `grep -r '.session/<name>'`
> across `docs/superpowers/`, `docs/`, `README.md`, and
> `CLAUDE.md` to find inbound references; either update each
> reference to point at the new home (`TODO.md`,
> `docs/index.md`, the relevant
> `docs/superpowers/specs/<file>`, etc.) or migrate the
> referenced content first. Propose a classification (one of
> the six labels) with a one-sentence justification. Surface
> to user for confirmation. On confirmation: perform the
> disposition (migrate to `TODO.md`, fold into
> `docs/index.md`, or delete the `.session/` entry).

Triage is human-paced and auditable: each file gets a brief
surface-and-confirm rather than a bulk auto-classification.

## Transitional state during Milestone A → Milestone B

During the period after Milestone A and before Milestone B,
`.session/` and `TODO.md` coexist. `CLAUDE.md`'s
project-status section documents the transitional
arrangement: *"`TODO.md` is the source of truth for active
work under the new layout; `.session/workstreams/` holds
legacy entries pending triage."*

`.session/README.md` is amended once at Milestone A
completion to add a header pointer at the top of its
existing content:

```markdown
> **Note (post-Milestone-A)**: `TODO.md` at the repository
> root is now the source of truth for active work. The
> contents below are legacy entries pending triage. See
> `docs/process.md` § Workstream triage method for the
> migration scheme. The directory will be removed at
> Milestone B.
```

Once a workstream entry is triaged, it is dispatched per its
label (migrated to `TODO.md`, folded into `docs/index.md`,
or deleted) and its `.session/` file is removed
individually. When all entries have been dispatched, the
directory itself (including the amended `README.md`) is
deleted (Milestone B item B4).

The Claude-harness task list is treated similarly: tasks
that are children of a `live` workstream are implicitly
carried by that workstream's plan in
`plans/`; `completed` tasks are historical
only; `pending` or `in_progress` tasks under non-`live`
workstreams are surfaced during triage. Reset (Milestone B
item B5) keeps brainstorming-tracking tasks, the refactor's
plan tasks, and currently-`live` workstream tasks;
everything else is archived or deleted.

## README.md

The parent `geb/README.md` is **not rewritten** by this
refactor. It documents the broader project including the
Common Lisp implementation. The refactor adds a brief pointer
near the top of `geb/README.md` (placed after the title and
any tagline, before the first body section), of approximately
the following form:

> The Lean formalisation of this project lives in `geb-lean/`;
> see [`geb-lean/README.md`](geb-lean/README.md). The material
> below documents the original implementation; the geb-lean
> subproject is the active development home for the Lean
> formalisation of this project.

(Three to five lines; state the supersession-direction
without prescribing timing.)

A new `geb-lean/README.md` is authored fresh per the
following pattern: identity / status / dependencies /
licence / docs index / process index / contribution pointers
/ upstream pointers. It opens with a one-line framing that
geb-lean is a subproject of the geb/ monorepo and points at
`../README.md` and `../LICENSE`. Length target ~150 lines.
The README grows as content lands but only as an *index*; it
does not duplicate content from `docs/` or process files.

Concretely, sections in order:

1. Project name and one-paragraph identity.
2. Status (e.g. "Active experimentation; process refactor
   of 2026-05-09 in effect.").
3. Dependencies (mathlib + CSLib at the pinned versions;
   pointer to `lakefile.toml`).
4. Licence (GNU General Public License version 3; see
   `../LICENSE`).
5. Index of project documentation: links to `docs/index.md`,
   `docs/process.md`, `docs/lean-resources.md`, this
   refactor's spec and plan, and the workstream-specific
   specs / plans currently active.
6. Index of project processes: link to `CLAUDE.md`, brief
   listing of `.claude/rules/*.md` files with one-line
   descriptions.
7. Contribution pointers: how an external developer would
   start (clone, follow `CLAUDE.md`, brainstorm a
   workstream, write spec / plan, implement, push).
8. Pointers to the upstream / sibling target: link to
   `geb-mathlib` (with note on the migration-flow
   relationship), and to mathlib4 / CSLib for general
   dependency reference.

## Lakefile changes

Existing options preserved (verified against `lakefile.toml`):

- `moreLeanArgs = ["-DwarningAsError=true"]` — the
  load-bearing mechanism for the "no `sorry` in commits"
  rule. This Lean kernel-level flag promotes the
  `declaration uses 'sorry'` warning (and every other
  warning-class diagnostic) into a build error. The refactor
  preserves this setting; the spec's `sorry`-in-commits rule
  depends on it remaining live.
- `autoImplicit = false`, `relaxedAutoImplicit = false`.
- `pp.unicode.fun = true`, `pp.proofs = false`,
  `pp.showLetValues = false`, `pp.universes = false`.
- `weak.linter.mathlibStandardSet = true`.
- `maxSynthPendingDepth = 3`.
- `linter.hashCommand = false` for the `GebLeanTests`
  library.

Additions:

- `lintDriver = "batteries/runLinter"`. (Already added in
  `chore/process-refactor` commit 00284252; carried forward
  unchanged.) Verification-only check: confirm the line is
  present in `lakefile.toml` and that `lake lint` runs. The
  plan does not re-add the line.
- **`weak.linter.flexible = true` is deliberately NOT
  adopted** in this refactor, despite the `geb-mathlib`
  design including it. Rationale: the `flexible` linter
  flags overly-permissive tactic uses across substantial
  existing code; under the preserved
  `moreLeanArgs = ["-DwarningAsError=true"]` each warning
  becomes a build break. Adopting `flexible` here would
  almost certainly break the existing build. Adoption is
  deferred to a separate cleanup workstream that can survey
  the warnings and either fix or document each one.

The `weak.linter.style.header = false` skeleton-stage
setting from `geb-mathlib` does not apply: this repository's
existing files already have whatever header policy has been
established.

## CI changes

`lean_action_ci.yml` is promoted from
`geb-lean/.github/workflows/` to `geb/.github/workflows/`.
The promoted file gains:

- `paths: ['geb-lean/**']` filter on `push` /
  `pull_request` triggers.
- The `leanprover/lean-action@v1` step passes
  `lake-package-directory: geb-lean` (the action's
  documented input for specifying which subdirectory
  contains the Lake package; verified against the
  leanprover/lean-action README). `defaults.run.working-directory`
  in GitHub Actions applies only to `run:` shell steps, not
  to `uses:` action steps; the `lake-package-directory`
  input is the correct mechanism for this action.
- The `defaults.run.working-directory: geb-lean` setting is
  at the **workflow level** (top-level `defaults` key, not
  per-job). This applies to all `run:` steps across all jobs
  in the workflow. The `actions/checkout` step does not run
  a `run:` command — it is a `uses:` step — so it is
  unaffected by this setting and checks out at
  `$GITHUB_WORKSPACE` (the repo root) as expected. The
  `leanprover/lean-action@v1` step likewise is `uses:`, and
  uses its own `lake-package-directory: geb-lean` input. The
  `axiom_check` job's `run:` step inherits
  `working-directory: geb-lean` and so executes
  `bash scripts/check-axioms.sh ...` from `geb-lean/`.
- The new `axiom_check` job depends on the existing build
  job (`needs: [build]`) since the script reads compiled
  `.lake/` artefacts. It may run in parallel with other jobs
  that also declare `needs: [build]`, but it is not parallel
  to `build` itself. The job runs
  `bash scripts/check-axioms.sh GebLean/ test/`.

  Pre-Milestone-B (report-only mode): the CI step is
  `bash scripts/check-axioms.sh --exit-zero-on-findings
  GebLean/ test/` (the `--exit-zero-on-findings` flag,
  which is also accepted as `--report-only` — both are
  aliases implemented near the argument-parsing section
  near the top of `scripts/check-axioms.sh`). The report
  is captured as a GitHub Actions artefact via two steps:

  ```yaml
  - name: Run axiom check (report-only)
    run: |
      bash scripts/check-axioms.sh --exit-zero-on-findings \
        GebLean/ test/ \
        | tee axiom-check-report.txt
  - name: Upload axiom-check report
    uses: actions/upload-artifact@<SHA>
    with:
      name: axiom-check-report
      path: geb-lean/axiom-check-report.txt
      if-no-files-found: error
  ```

  The `tee` redirection makes the run-step's stdout visible
  in the Actions log while writing the intermediate file.
  Because `defaults.run.working-directory: geb-lean` applies
  to the `run:` step, `tee axiom-check-report.txt` writes to
  `geb-lean/axiom-check-report.txt` relative to the checkout
  root — inside `$GITHUB_WORKSPACE`. The upload step's
  `path:` references that file by its repo-root-relative
  path, satisfying `actions/upload-artifact`'s requirement
  that the path be within the workspace. This `path:`
  resolution depends on the workflow's `actions/checkout`
  step using the default destination (`$GITHUB_WORKSPACE`,
  the repository root). If a custom checkout `path:` input is
  set, the upload step's `path:` would need adjustment. The
  default destination is preserved by not specifying a
  `path:` input on the checkout step. The `<SHA>` placeholder
  is the exact commit hash of the `actions/upload-artifact@v4`
  release, resolved at workflow-authoring time.

  Post-Milestone-B (fail-mode): the `--exit-zero-on-findings`
  flag is removed; CI then fails on any non-allowlisted axiom
  (see Milestone B item B7).

  Rationale for report-only at first: CSLib (a peer
  dependency) and mathlib both transitively introduce
  `Classical.choice` into the closure of practically every
  GebLean declaration; flipping the job to fail-mode on day 1
  would break CI universally. Migration to fail-mode is a
  Milestone-B item (the per-touch annotation cadence matches
  Milestone B's triage rhythm): as individual files are
  touched, `AXIOM_ALLOW` comments are appended above each
  flagged declaration that legitimately depends on
  `Classical.choice` transitively. When the report-only
  output is empty, the job flips to fail-mode (failure
  condition: any non-allowlisted axiom — anything other than
  `propext`, `Quot.sound`, `quot.sound` — appears in the
  closure of any declaration without a matching `AXIOM_ALLOW`
  comment). The flip is recorded as Milestone B verification
  item B7. The job runs on every PR and every push to `main`
  or `integration`.

`update.yml` and `create-release.yml` remain inert at
`geb-lean/.github/workflows/`; they are not moved.

The `geb-lean/.github/workflows/markdown-lint.yml` file
landed in `chore/process-refactor` commit 3d27311f at the
wrong location; it is removed in the cleanup task that opens
the new plan. The parent-level workflow supersedes it.

`markdown-lint.yml` (new): lives at
`geb/.github/workflows/markdown-lint.yml`. Path filter:
`paths: ['geb-lean/**/*.md', 'geb-lean/.markdownlint-cli2.jsonc']`.
Action invocation uses a `run:` step to pass explicit globs
and suppress config-file glob expansion:

```yaml
- name: Install markdownlint-cli2
  run: npm install -g 'markdownlint-cli2@^0.18.0'
- name: markdownlint
  run: |
    markdownlint-cli2 \
      --config geb-lean/.markdownlint-cli2.jsonc \
      --no-globs \
      'geb-lean/**/*.md'
```

A `run:` step is used rather than the
`DavidAnson/markdownlint-cli2-action` action step because
the action does not expose a `--no-globs` equivalent input;
without `--no-globs`, the config's presence causes
additive glob expansion from the parent CWD, scanning
the entire monorepo. The `run:` form requires
`markdownlint-cli2` to be installed in the CI environment;
the install step above covers this since `markdownlint-cli2`
is not pre-installed on `ubuntu-latest`. The version pin
(`@^0.18.0`) is appropriate; the `--no-globs` flag was
introduced in markdownlint-cli2 v0.12.0 (the npm package
version, which is on the 0.x series); without it, older
versions do not recognize the flag.

This workflow contains no third-party `uses:` action
references; both steps are `run:` steps. The
`actions/checkout` step (added by `C-lean-action-ci-promote`
to the parent-level `lean_action_ci.yml`) and the
`actions/upload-artifact` step (in `lean_action_ci.yml`'s
`axiom_check` job) are the `uses:` references that carry
SHA-pins in this plan; all `uses:` action references in those
workflows are SHA-pinned (40-hex-char commit IDs, not tag
references); the plan author resolves SHAs at
workflow-authoring time via WebFetch against the action's
GitHub release page.

## .markdownlint-cli2.jsonc

The configuration starts close to markdownlint defaults,
with rule overrides accumulated as friction is encountered.
The target configuration (post-cleanup) exempts MD013
line-length checks for tables and code blocks (long lines in
those contexts are legitimate). It has only `config` and
`ignores` keys — no top-level `globs` key. (Per
markdownlint-cli2 behaviour, CLI glob arguments and a
config-file `globs` field are additive, not mutually
exclusive; omitting `globs` from the config prevents
unintended glob union when CLI globs are passed.) The
`ignores` array carries both unprefixed and `geb-lean/`-prefixed
forms for each generated directory:

```json
"ignores": [
  ".lake/**",
  "node_modules/**",
  ".session/**",
  ".claude/memory/**",
  ".claude/docs/**",
  ".claude/tools/**",
  "geb-lean/.lake/**",
  "geb-lean/node_modules/**",
  "geb-lean/.session/**",
  "geb-lean/.claude/memory/**",
  "geb-lean/.claude/docs/**",
  "geb-lean/.claude/tools/**"
]
```

`.jj/` is deliberately not listed: jj manages its own
git-visibility via the self-contained `.jj/.gitignore`
(`/*`) it creates at `jj git init --colocate`. Adding
`.jj/**` to markdownlint's ignores would override any
later jj decision to expose a markdown file under `.jj/`
(e.g. a commit-message template). In normal operation
`.jj/` contains no markdown files, so the absence of this
ignore entry is a no-op; if jj ever does expose a markdown
file, markdownlint will lint it like any other file rather
than silently skip it.

The unprefixed forms match when CWD is `geb-lean/` (the
`pre-push.sh` case); the `geb-lean/`-prefixed forms match
when CWD is `geb/` (the parent-CWD CI case). Each
invocation triggers exactly one of the two sets; the other
matches nothing (harmless). The configuration is **iterated
until clean against the refactor's own artefacts**; the
final set of overrides is recorded in `docs/process.md`
§ Markdownlint discipline so the rationale for each override
persists.

The file committed pre-refactor (introduced at `aeae31f9`)
carries a `"globs": ["**/*.md"]` key and `ignores` patterns
without the `geb-lean/` prefix, without the unprefixed
forms, and without `.session/**`.
Cleanup task C-markdownlint-config-rewrite rewrites the file
to the target configuration described above. The parent-level
CI workflow's `markdownlint-cli2 --no-globs` invocation reads
the post-cleanup config correctly; the pre-push invocation
in § Auxiliary scripts likewise uses `--no-globs`.

## .gitignore change at the parent

The parent `geb/.gitignore` currently contains `.claude`
(no slash, line 7), which blanket-ignores all `.claude/`
directories everywhere in the monorepo. This must be
modified to permit `geb-lean/.claude/{settings.json,
rules/}` to be tracked. The replacement:

```gitignore
/.claude/
geb-agda/.claude
geb-idris/.claude
/geb-lean/.claude/*
!/geb-lean/.claude/rules/
!/geb-lean/.claude/settings.json
```

This keeps the parent's own `.claude/` ignored, keeps the
sibling subprojects' `.claude/` ignored, but permits
`geb-lean/.claude/settings.json` and
`geb-lean/.claude/rules/` to be tracked. It is a minimal
change that permits the refactor without touching sibling
subprojects.

The existing in-flight commit `69123dd0` modified
`geb-lean/.gitignore` by adding `/.claude/*`,
`!/.claude/rules/`, and `!/.claude/settings.json`. Those
negation patterns are functionally inert because the parent
`geb/.gitignore` still has the blanket `.claude` pattern at
line 7, which overrides them (`git check-ignore` confirms
`geb-lean/.claude/settings.json` is ignored via
`geb/.gitignore:7`). After the cleanup task
`C-gitignore-revert`, `geb-lean/.gitignore` contains no
`.claude`-related patterns: all four currently present
(`/.claude/*`, `!/.claude/rules/`, `!/.claude/settings.json`,
`/docs/.claude`) are removed. The parent `geb/.gitignore` (per the
replacement above) becomes the only authoritative source for
`.claude/`-path ignore and unignore decisions. After both
`C-gitignore-revert` and the parent-`.gitignore` edit are
in place: `git check-ignore -v geb-lean/.claude/settings.json`
returns nothing (the path is not ignored); and
`git check-ignore -v geb-lean/.claude/settings.local.json`
identifies the path as ignored via the parent's
`/geb-lean/.claude/*` pattern, with no negation for
`.local.json`. These outcomes (plus a third: `geb-lean/.claude/rules/`
is not ignored) are confirmed by verification checklist item 10.

## jj setup

Performed once, as the first plan task that touches VCS:

1. `jj git init --colocate` in the **parent `geb/` root**.
   This creates `geb/.jj/` with a self-contained
   `geb/.jj/.gitignore` (containing `/*`), which excludes
   `.jj/` from git's view without modifying any `.gitignore`
   files. Verified empirically against jj 0.40 (initial) and
   re-verified against jj 0.41.0; the manual-conversion form
   of this exclusion is documented at
   <https://docs.jj-vcs.dev/latest/git-compatibility/>.
2. Set per-repo jj configuration via `jj config set --repo`,
   run at the parent root. In jj 0.38 and later, per-repo
   config is stored outside the repository (in a
   user-config-dir path keyed by repo hash) for security
   reasons; `.jj/repo/config.toml` is no longer used.
   `jj config edit --repo` and `jj config path --repo` are
   the canonical commands for inspecting and locating the
   file (verified against
   <https://docs.jj-vcs.dev/latest/config/>). New developers
   therefore do not author or commit a config file; they run:

   ```sh
   jj config set --repo git.private-commits 'conflicts()'
   jj config set --repo remotes.origin.fetch-tags \
     'glob:cutover-*'
   ```

   These are the project-level settings. The first refuses
   pushing commits in conflict state (see below). The second
   makes `jj git fetch --remote origin` mirror the cutover
   tag(s) automatically (new in jj 0.41 per
   <https://docs.jj-vcs.dev/latest/config/>: *"You can
   configure which bookmarks and tags to fetch by default per
   remote, using the
   `remotes.<name>.fetch-bookmarks`/`fetch-tags` config. The
   value is a string pattern that matches the names of the
   bookmarks and tags to fetch."*).

   **`fetch-tags` is documented as experimental** (verbatim
   from the same docs page: *"Note that
   `remotes.<name>.fetch-tags` is experimental"*). The spec
   uses it as the durable mechanism for ongoing cutover-tag
   mirroring: `git clone` mirrors all tags one-shot at clone
   time, so a developer who reaches the working tree via
   `git clone` already has the cutover tag locally; the
   `fetch-tags` config is what keeps later `jj git fetch`
   calls in sync if additional `cutover-*` tags appear (and
   covers the case of a working tree initialised in some
   other way, e.g. `jj git remote add` against an existing
   checkout). If the upstream feature is removed or its
   semantics change before jj 1.0, the fallback is to
   re-introduce the explicit
   `git fetch origin 'refs/tags/cutover-*:refs/tags/cutover-*'`
   form, add the corresponding `block-mutating-git` allowlist
   entry, and add an explicit step to the on-boarding
   sequence. This fallback is not the current path but is
   documented here as forward-protection.

   Per-developer settings (`user.name`, `user.email`, signing
   config) are set at the user level via
   `jj config set --user`; they are per-developer local and
   outside the project's purview.

   The `git.private-commits = "conflicts()"` setting refuses
   to push any commit (and its descendants) that currently
   has conflict state. **The behaviour we expect — and verify
   in the plan — is**: resolving a conflict locally and then
   pushing succeeds without `--allow-private`, since the
   offending commit is no longer in `conflicts()` at push
   time. The plan's smoke test exercises this flow
   (manufacture a conflict; resolve it; push) to confirm. If
   empirical verification shows different semantics, the rule
   wording in this spec and `docs/process.md` is amended.

   Two exemption conditions apply (per
   <https://docs.jj-vcs.dev/latest/config/>): commits already
   on the remote are exempt (verbatim quote: *"If a commit is
   in `git.private-commits` but is already on the remote,
   then it is not considered a private commit"*), and commits
   in the `immutable_heads()` revset are exempt. By default
   the immutable revset covers `trunk()` ancestors (i.e.
   ancestors of `main@origin`), so already-public commits
   are doubly-exempt. The two conditions are independent and
   a user can configure additional immutable heads (e.g.
   local release tags) which will then also be exempt.
   `private-commits = "conflicts()"` therefore prevents
   unintentional propagation of *in-flight* conflicts; it
   does not retroactively block already-public or immutable
   history.

`geb/.jj/` is git-ignored via its self-contained
`.gitignore`. The **`git clean -xdf` warning** — that
running this command from the parent `geb/` root would
delete `.jj/` because it is git-ignored — is documented in
`docs/process.md` § jj. (jj 0.40 used to print this as a
hint at colocate time; jj 0.41 dropped the hint, so the only
place the warning lives is the documentation. Verified
empirically against jj 0.41.0.)

`.session/` is left in place during the jj setup step;
Milestone B (below) clears it after triage.

**On-boarding for new developers**: a developer cloning the
repository performs the following sequence. Per-repo
configuration must be set *before* the first
`jj git fetch --remote origin` so the fetch applies
the `fetch-tags` pattern:

1. `jj git init --colocate` (in the cloned repository's
   working directory — the parent `geb/` root).
2. Set the project-level per-repo configuration:
   - `jj config set --repo git.private-commits 'conflicts()'`
   - `jj config set --repo remotes.origin.fetch-tags
     'glob:cutover-*'`
3. Set per-developer signing and identity (user level, not
   per-repo):
   - `jj config set --user user.name '<name>'`
   - `jj config set --user user.email '<email>'`
   - `jj config set --user signing.behavior 'own'`
   - `jj config set --user signing.backend 'gpg'` (or
     `'ssh'`)
   - `jj config set --user signing.key '<key id>'`
4. `jj git fetch --remote origin` to mirror bookmarks into
   jj's view. Tag mirroring depends on the entry path: a
   developer who reached the working tree via `git clone`
   already has all tags locally (git clone mirrors all tags
   one-shot by default), so the cutover tag is present
   irrespective of jj configuration; for that developer the
   fetch is functionally redundant for tag presence in this
   step but remains required to mirror bookmarks. Step 2's
   `remotes.origin.fetch-tags = 'glob:cutover-*'` setting is
   forward-protection: it ensures any *subsequent*
   `jj git fetch` continues to mirror new `cutover-*` tags
   as they appear, and it covers entry paths other than
   `git clone` (e.g. initialising via `jj git remote add`
   against an existing checkout). Earlier jj versions (0.40
   and prior) lack this setting; this spec assumes jj 0.41+
   for that reason.
5. `bash geb-lean/scripts/check-jj-setup.sh` to verify all
   of the above (described below).

The exact command sequence is reproduced in
`docs/process.md` § jj colocated mode. Failure mode if
signing is not configured: `jj` produces unsigned commits
silently, violating the project's signing convention but
not breaking the build. Three gates catch this: the
`check-jj-setup.sh` self-check (immediate, run by the
developer after the `jj config set` commands), the
`pre-push.sh` self-check (per-push), and the
`check-signing-key` SessionStart hook (per-session warning
if no signing config is found).

**`scripts/check-jj-setup.sh`** (lives at
`geb-lean/scripts/`): a one-shot verifier that uses
`jj root` (run with no arguments; walks up from CWD to
find `.jj/`; portable across whether `.jj/` is at the
parent or at geb-lean/) to validate the jj installation
before querying configuration. It then asserts:
(a) `jj config list --repo git.private-commits` outputs a
TOML line of the form
`git.private-commits = "conflicts()"`;
the script strips the TOML wrapper via `sed` to extract
the bare value and compares it to `conflicts()` exactly
(anchored string match, not substring; a configuration of
e.g. `conflicts() | description("private")` would
correctly fail this check);
(b) `jj config list --repo remotes.origin.fetch-tags`
outputs a TOML line of the form
`remotes.origin.fetch-tags = "glob:cutover-*"`;
the script similarly strips the TOML wrapper and compares
the bare value to `glob:cutover-*` exactly (anchored
string match; this forecloses unintentionally-broader
patterns like `glob:bug-cutover-*` that would silently
mirror unrelated tags);
(c) at least one of `jj config get signing.behavior` or
`git config --get commit.gpgsign` indicates signing is
active. Exits non-zero on any failure with a message
pointing the developer at `docs/process.md`
§ jj colocated mode. `scripts/pre-push.sh` invokes the
same checks at the top of its sequence so an unverified
setup fails before any push.

(The cutover tag's local presence is *not* a check in this
script: pre-cutover, the tag does not exist; gating on it
would forbid the very push that creates the cutover commit.
The cutover tag's integrity is protected by GitHub
repository protection rules — Milestone A item 17a — and
post-cutover clones fetch it explicitly via the on-boarding
step 2 above.)

## Branch model (forward-only)

| Prefix | Use |
| --- | --- |
| `main` | Append-only stable branch. Topic branches land via normal merge commits. Never force-pushed. |
| `integration` | Regenerated fan-in merge of `main` plus all currently-active topic branches. Force-pushed (lease-protected by jj 0.41+ default). |
| `feat/<topic>` | New content / new functionality. |
| `fix/<topic>` | Bug fixes. |
| `refactor/<topic>` | Restructuring without behaviour change. |
| `chore/<topic>` | Tooling, CI, scaffolding (the present refactor uses this prefix). |
| `docs/<topic>` | Documentation-only changes. |
| `bump/<dep>-<version>` | Toolchain, mathlib, or CSLib bumps; `<dep>` is `lean`, `mathlib`, or `cslib` (e.g. `bump/lean-v4.30.0-rc1`, `bump/mathlib-2026-04-01`, `bump/cslib-v4.30.0-rc2`). The explicit `<dep>` token disambiguates the bump target. |

**Releases**: tag-only. The existing `create-release.yml`
workflow fires on tag creation; no `release/` topic-branch
prefix exists. A release-notes change lands on a `chore/`
workstream before the tag is pushed.

**Forward-only adoption with cutover commit.** `main`'s
past commits are unchanged. The append-only rule applies
forward from the **cutover commit** — the merge commit on
`main` (parent repo's `main`) that lands the present
refactor's topic branch. The cutover commit's SHA is
recorded in `docs/process.md` § Branch model after the
merge. Verification of "append-only `main`" checks commits
whose first parent is at or after the cutover SHA: every
such commit must be either a fast-forward update of `main`
or a normal merge commit. Pre-cutover commits are exempt.

The branch-management operations are **canonical jj
one-liners** documented in `docs/process.md` § Branch model
rather than wrapper scripts. None of them justifies a
script:

- **Regenerate `integration`** (fan-in merge of `main`
  plus all active topic branches whose tips are not already
  reachable from `main`):

  ```sh
  jj git fetch --remote origin
  jj new \
    'main |
     (bookmarks(glob:"feat/*") ~ ::main) |
     (bookmarks(glob:"fix/*") ~ ::main) |
     (bookmarks(glob:"refactor/*") ~ ::main) |
     (bookmarks(glob:"chore/*") ~ ::main) |
     (bookmarks(glob:"docs/*") ~ ::main) |
     (bookmarks(glob:"bump/*") ~ ::main)' \
    -m "integration: fan-in @ $(date -I)"
  jj bookmark set integration -r @
  jj git push --remote origin -b integration
  ```

  The explicit `glob:` prefix is used defensively. jj's
  revset semantics treat unprefixed `"string"` as `glob:`
  by default (verified against
  <https://docs.jj-vcs.dev/latest/revsets/>), but jj is
  pre-1.0 and revset string-pattern semantics may change in
  later versions. Explicit `glob:` pinning is robust
  against silent default changes.

- **Mass-rebase active topic branches onto a new `main`**
  (after a toolchain bump merges):

  ```sh
  jj rebase -d main -s 'roots(
    bookmarks(glob:"feat/*") |
    bookmarks(glob:"fix/*") |
    bookmarks(glob:"refactor/*") |
    bookmarks(glob:"chore/*") |
    bookmarks(glob:"docs/*") |
    bookmarks(glob:"bump/*"))'
  ```

`jj git push` is lease-protected by default in current jj
versions (`--force-with-lease`-equivalent semantics;
verified against <https://docs.jj-vcs.dev/latest/bookmarks/>);
no explicit flag is required for `integration`'s
force-push.

**jj-version pinning of revsets**: the revset one-liners
above are verified against jj 0.41 only. jj is pre-1.0 and
revset syntax may evolve. On every toolchain bump, the bump
procedure re-verifies the one-liners against the new jj
version (a copy-paste sanity check; the revsets are short).

## Hooks

| Hook | Type | Path | Wired in |
| --- | --- | --- | --- |
| `block-mutating-git` | PreToolUse | `scripts/hooks/block-mutating-git.sh` | `geb-lean/.claude/settings.json` (committed) |
| `check-signing-key` | SessionStart | `scripts/hooks/check-signing-key.sh` | `geb-lean/.claude/settings.json` (committed) |

The wiring lives in `geb-lean/.claude/settings.json`
(committed) so both hooks apply for any developer working
in this repository. Claude sessions are opened with
`geb-lean/` as `CLAUDE_PROJECT_DIR`; hooks resolve to
`${CLAUDE_PROJECT_DIR}/scripts/hooks/<name>.sh`.
`.claude/settings.local.json` remains for personal-only
settings that do not bind others. The parent `geb/.claude/`
directory remains empty/unused.

`block-mutating-git.sh` follows a **default-deny** policy
with closed allowlists. It reads JSON from stdin; it checks
whether `jj root` (run with no arguments) exits 0 —
portable across whether `.jj/` is at the parent or at
geb-lean/ — and if so strips `jj git X` forms (so jj's
git interop still works) and applies the allowlists below.
If `jj root` exits non-zero (jj not installed, or the
working directory is outside any jj-initialised tree), the
hook does not strip `jj git X` invocations; default-deny
policy then applies. Concretely: in such an environment,
Claude attempting `jj git push` would be blocked because
`jj` is not a `git` subcommand and there is no `jj`
allowlist. This is the documented behaviour before A24
(before `jj git init --colocate` lands at the parent);
after A24 the `jj root` check succeeds in the project's
working tree and the strip-branch becomes reachable.
Developers running Claude in a non-jj environment after A24
(e.g., on a server where the working tree was provisioned
via raw git) need to either re-init jj or accept that jj
operations are out of scope until they do.
The existing `block-mutating-git.sh` (committed as
`125c6d4e` on `chore/process-refactor`) checks
`[[ -d $CLAUDE_PROJECT_DIR/.jj ]]` rather than invoking
`jj root`. The new plan's cleanup task amends this hook
script before task A27 wires it into
`.claude/settings.json`; until that amendment lands, the
hook would fail verification matrix item 12 case (b) when
`.jj/` is at the parent rather than at `geb-lean/`.
Anything not on an allowlist — including unrecognised
subcommands and user-defined aliases — is blocked.

**Scope.** As a Claude Code PreToolUse hook, the script
sees **only Claude's tool invocations** (Bash commands
Claude attempts to run). User-direct git operations in the
user's own terminal are out-of-scope and proceed without
hook interference. The hook protects against Claude making
mutating git commands; the project's "no `git push` without
user line-by-line review" hard rule (and the analogous
human-gate for any other production-impacting operation)
applies to user-direct invocations. Operations that are
deliberately user-manual (e.g. creating the cutover tag,
signing it, or invoking `git rebase -i`) are performed by
the user outside Claude Code and don't need allowlist
coverage.

**Read-only subcommand allowlist (closed)**: `status`,
`log`, `diff`, `show`, `blame`, `rev-parse`, `ls-files`,
`ls-tree`, `describe`, `cat-file`, `name-rev`, `reflog`,
`grep`, `shortlog`, `whatchanged`, `count-objects`,
`verify-pack`, `verify-tag`, `version`, `help`,
`remote -v`, `branch --list`, `tag --list`.

**`git config` allowlist (closed)**: only `git config
--get`, `git config --list`, and `git config --get-all` are
allowed. Every setter form (`git config <key> <value>`,
`--unset`, `--add`, `--replace-all`, `--rename-section`,
`--remove-section`) is blocked.

**`git fetch` allowlist (closed)**: bare `git fetch`;
`git fetch origin` (no extra arguments); and
`git fetch origin refs/pull/*/head:*` (the form `gh pr
checkout` uses). The cutover tag is mirrored by
`jj git fetch` itself via the per-repo
`remotes.origin.fetch-tags = 'glob:cutover-*'` setting
(jj 0.41+; see § jj setup), so no explicit raw-git
tag-fetch form is needed in the allowlist. Every other
`git fetch` invocation — including `--tags`, `--prune`,
`--prune-tags`, `--all`, arbitrary refspecs targeting local
refs, or `git fetch <other-url>` forms — is blocked. The
hook's stderr message directs the user to `jj git fetch`,
which covers most fetch operations through its own
bookmark-state update.

**`git clone` rule**: `clone` is allowed only when its
target argument resolves to an absolute path that does
**not** equal `$PWD` and does **not** have `$PWD` as a
prefix. So `git clone <url> <new-dir>` and
`git clone <url> ../sibling` work;
`git clone <url> .`, `git clone <url> ./subdir`,
`git clone . <other>` are blocked, since these forms could
clobber or duplicate the current working tree's `.jj/`.

**Default-deny rationale**: git has hundreds of subcommands
plus arbitrary user-defined aliases. An open list of
"blocked mutating subcommands" cannot be exhaustive;
default-deny with closed allowlists is maintainable. If a
developer needs an allowlist addition, the addition is
proposed in a refactor plan (spec / plan / adversarial
review) rather than landed silently.

**Why `--prune` is blocked** (a specific case worth calling
out): `git fetch --prune` deletes git's remote-tracking
refs in `.git/refs/remotes/`. jj's bookmark-tracking state
mirrors those refs in colocated mode; in-place pruning by
raw git can desync jj's view. `jj git fetch` performs its
own remote-tracking-state update on each invocation, so the
prune-equivalent effect is available through jj.

On block: prints a translation message to stderr (mapping
the blocked `git` command to its `jj` equivalent if one
exists, or otherwise advising "this `git` invocation is not
on the allowlist; if it should be, propose the addition in
a refactor plan") and exits 2.

**`gh` CLI commands are out of scope for this hook.**
`gh pr create`, `gh pr merge`, `gh pr close`,
`gh release create`, `gh issue create`, `gh issue close`,
etc. bypass local `git` mutation and write directly via the
GitHub API; the hook does not see them. The project's hard
rule "no push or external write without user line-by-line
review" applies symmetrically and is enforced by the
human-gate convention, not by the hook. `CLAUDE.md`'s
hard-rules section names `gh` write operations explicitly
under that rule.

**Tag operations are out-of-scope for the hook.** Tag
creation, signing, listing-for-verification, push, and
deletion are user-direct operations performed in the user's
own terminal (not by Claude). Per § Hooks Scope, the hook
only sees Claude's tool invocations; user-direct operations
proceed without hook interference. The project's hard rule
"no `git push` without user line-by-line review" applies as
the human-gate — and since signed-tag operations are
inherently tied to the user's gpg key and identity, those
operations are user-direct by construction. The hook
intentionally does **not** allowlist any tag-push or
tag-creation form: if Claude attempted such a command it
would be blocked, which is correct (Claude has no business
signing or pushing tags).

(jj 0.41 has no tag-push or tag-creation capability —
verified empirically against jj 0.41.0 via
`jj git push --help` (no `--tag` flag) and `jj git --help`
(no `tag` subcommand; `jj git` exposes only `clone`,
`fetch`, `init`, `push`, `remote`). The absence is
irrelevant given the user-direct framing above.)

**Short-form / long-form flag equivalence**: for git flag
pairs documented as short-form/long-form equivalents (e.g.
`-l` and `--list`, `-d` and `--delete`, appearing as either
top-level options or subcommand options), the hook's
literal-token rule treats short and long forms as the same
token after a canonicalisation pass. This is the single
exception to strict literal-token matching, justified by
the canonical equivalence being part of git's own CLI
contract. Refspec patterns themselves are not
canonicalised — `refs/heads/feat-*` and
`refs/heads/feat-foo` (illustrative, not in any allowlist)
would be distinct literal tokens regardless of glob meaning.

**Refspec matching semantics**: the allowlisted refspec
`refs/pull/*/head:*` is matched by the hook as a
**literal-token** equality after argv parsing. The `*`
characters in this token are part of git's refspec syntax
(interpreted by `git fetch` itself), not glob-matched by
the hook. Other refspecs that resemble the form but use
different patterns are not on the allowlist and are blocked.

`check-signing-key.sh` warms the signing agent at session
start. Because git's `commit.gpgsign` config and jj's
`signing.behavior` config are independent, the hook queries
**both** and warms the appropriate agent if either indicates
signing is active:

1. Query `git config --get commit.gpgsign`; if `true`,
   signing on the git side is active.
2. Query `jj config get signing.behavior` (which jj
   resolves from the user-level config); if it returns
   `own` or `force`, signing on the jj side is active.
3. If either is active, dispatch on the configured backend
   (`gpg`, `ssh`, etc.) and warm the appropriate agent.
   For `gpg`: query
   `gpg-connect-agent 'keyinfo --list' /bye | grep -q ' 1 '`;
   if not cached, run
   `echo warm | gpg --clearsign >/dev/null` to seed the
   cache via pinentry.
   For `ssh`: invoke `ssh-add -l`; if no keys are loaded,
   defer to the developer's local agent setup (the hook does
   not seed ssh-agent autonomously since key discovery is
   non-portable across ssh-signing configurations). The
   developer is expected to load their signing key via their
   normal ssh-agent workflow before signed commits. The hook
   emits an informational message to stderr if `ssh-add -l`
   reports no identities, then exits 0.
4. Exit 0 either way (never blocks session start).

This repository signs commits with gpg, so the hook is
expected to warm gpg-agent on every session. An ssh-signing
developer on-boards via `jj config set --user
signing.backend 'ssh'` (on-boarding step 3); the hook's
ssh path applies to that configuration.

## Auxiliary scripts

- `scripts/check-axioms.sh`: vendored derivative of the
  `lean4-skills` plugin's `check_axioms_inline.sh`. The
  vendored copy carries a header comment recording the
  upstream source URL, the lean4-skills plugin version
  string (e.g. `4.4.9`), the on-disk path of the upstream
  script, and instructions for re-vendoring by diffing
  against that path. (The lean4-skills plugin's manifest
  does not currently expose its source-commit SHA; if the
  plugin starts to expose one in a later version, the
  header should be updated to record it.) The header also
  records the local modifications, so on re-vendoring the
  header can detect drift. Allowlist customised: the
  allowlist is reduced to `propext`, `Quot.sound`,
  `quot.sound` (the `lean4-skills` default has
  `Classical.choice` in its allowlist; we remove it, with
  the effect that `Classical.choice` is *forbidden* by the
  script). The script flags every non-allowlisted axiom in
  the **closure** of every checked declaration — including
  transitively-introduced ones. The first-pass behaviour is
  "loud": every declaration that depends on
  `Classical.choice` (almost any mathlib-using declaration
  in our codebase) is flagged.

  **`AXIOM_ALLOW` comment syntax and layout**: a single-line
  `--` comment of the form
  `-- AXIOM_ALLOW: <axiom-name> (rationale text)`, placed
  before the declaration's docstring (if any), with no
  intervening blank lines between the AXIOM_ALLOW line, the
  docstring, and the declaration. The script scans up
  through `--` comment lines and through any preceding
  `/-- ... -/` docstring to find AXIOM_ALLOW attributions
  for the next top-level (column-0) declaration. Multi-line
  `--` comment blocks are permitted; the `AXIOM_ALLOW` line
  itself must be a single line, but adjacent `--` lines may
  carry additional rationale. Example:

  ```lean
  -- AXIOM_ALLOW: Classical.choice (transitive via
  --   Mathlib.CategoryTheory.Equivalence; required by
  --   mathlib's Equivalence.functor.PreservesLimits)
  /-- The `foo` theorem says that … -/
  theorem foo : … := …
  ```

  Once the axiom_check job is flipped to fail-mode at
  Milestone B, CI fails unless every flagged declaration has
  either an `AXIOM_ALLOW` comment or no axiom dependency
  outside the (reduced) allowlist. Direct `Classical.choice`
  use in our own code (i.e. without a matching `AXIOM_ALLOW`
  rationale) is forbidden.
- `scripts/pre-push.sh`: **manual** pre-push checklist
  runner. Invoked explicitly by the user before each push
  (e.g. `bash scripts/pre-push.sh && jj git push --remote
  origin -b <bookmark>`). No automatic-invocation hook is
  installed: jj 0.41 does not offer a documented
  `pre-push`-equivalent hook that fires on `jj git push`
  (verified against
  <https://docs.jj-vcs.dev/latest/cli-reference/> and
  empirically against jj 0.41.0). The script is
  by-convention only; the rule "run pre-push.sh before every
  push" is encoded in `CLAUDE.md` and `docs/process.md`.
  The script executes `lake test`, which builds the
  `GebLean` and `GebLeanTests` libraries (these are the
  inputs to `scripts/check-axioms.sh`). Running an explicit
  `lake build` before `lake test` would be redundant given
  current lakefile targets. **Should a lakefile addition
  introduce a target outside the test driver's dependency
  graph, this script must be amended to add `lake build`
  explicitly.** Then `lake lint`,
  `markdownlint-cli2 --config .markdownlint-cli2.jsonc
  --no-globs '**/*.md'` (the `--no-globs` flag suppresses
  any `globs` key in the config, matching CI behaviour and
  guarding against future config edits that inadvertently
  re-add a `globs` key; note: the single-quotes around
  `'**/*.md'` are load-bearing — without them, the shell
  would expand the glob before markdownlint-cli2 sees it,
  defeating `--no-globs`),
  `bash scripts/check-axioms.sh GebLean/ test/`.
  Note: the `lake lint` invocation depends on
  `lintDriver = "batteries/runLinter"` having been added to
  `lakefile.toml` (see Lakefile changes); the plan orders
  the lakefile change before `pre-push.sh` is authored.
  The script additionally surfaces user-driven gates as
  on-screen reminders rather than mechanical checks:
  `lean4:golf` and `lean4:review` ran on changed Lean code;
  user reviewed the diff line-by-line.
- `scripts/hooks/block-mutating-git.sh`,
  `scripts/hooks/check-signing-key.sh`: hook implementations
  (above).

The branch-management one-liners (regenerate `integration`;
mass-rebase topic branches) are documented in
`docs/process.md` § Branch model rather than packaged as
scripts; they reduce to single `jj` invocations.

## Adversarial review of specs and plans

After any spec or plan is committed, before downstream work
begins:

1. **Author commits** the spec or plan to its file under
   `docs/superpowers/specs/` (for specs) or `plans/`
   (for plans).
2. **Author runs spec-self-review or plan-self-review** as a
   brief inline check: placeholder scan, internal
   consistency, scope check, ambiguity check. Fixes are
   applied inline as further commits on the same branch.
3. **Author dispatches a fresh-context Agent** — a NEW Agent
   invocation (not `SendMessage` to a continuing agent),
   reading only the artefact at the given path, with
   adversarial review instructions: find every error,
   omission, vagueness, infelicity, internal contradiction,
   scope-creep, missing edge case, unstated assumption.
   Categorise each finding as **blocker** / **serious** /
   **minor** / **cosmetic-taste**. Reviewer is willing to
   say "the goal is unachievable" if true.
4. **Author responds in writing** to every finding: `fixed`
   / `deferred (with rationale)` /
   `rejected (cosmetic-taste)`. Responses materialise as
   commits on the same branch.
5. **Re-dispatch** to a fresh Agent. Loop.
6. **Termination**: all open findings are cosmetic-taste or
   rejected with rationale, OR the reviewer concludes the
   goal is unachievable (in which case the work pauses for
   user-level reframing).
7. **User review** follows adversarial-review termination.
   The user sees a version of the artefact that has already
   survived fresh-context attack.

For VCS / repo-layout / pervasive choices (which constitute
most spec and plan content for this repository), the
adversary specifically (a) checks primary sources for every
cited pattern; (b) searches for more standard alternatives
the author may have missed; (c) flags any "we'll write a
script for this" decision that could be a single command in
an existing tool.

**The rule binds every spec and every plan**, regardless of
size. The skipping question is "is the artefact small enough
that no spec/plan is needed at all?" — that is an upstream
decision; if a spec or plan exists, it is adversarially
reviewed.

**No fixed cycle cap.** Iteration continues until
convergence (termination as defined above) OR the author
concludes that convergence is likely impossible (e.g.
discovering during a cycle that something the spec relied on
is not true). If the latter, the author surfaces to the user
immediately with a plain account of what changed; the user
decides how to proceed. The author's
`rejected (cosmetic-taste)` is the author's call; reviewers
cannot re-raise the same finding twice across cycles. The
cycle count is whatever the spec needs — one is fine for a
small clean spec; ten or more is fine for a larger one.

**Where the rule lives**: as a hard rule in `CLAUDE.md`
(one bullet) → procedure in `docs/process.md`
§ Adversarial review → process self-update mechanism in
`docs/process.md` § Process self-update mechanism.

## Cleanup tasks (preceding the new plan's main sequence)

The following cleanup tasks must be completed at the opening of the new
plan, before the plan's main numbered sequence begins. Each is atomic and
self-contained. Ordering constraints are noted per task.

| Task | Description | Ordering constraint |
| --- | --- | --- |
| C-license-rm | Remove `geb-lean/LICENSE` (revert in-flight A5 commit). | Before any task that reads the file-layout as definitive. |
| C-workflow-rm | Remove `geb-lean/.github/workflows/markdown-lint.yml` (revert in-flight A4 file location; the parent-level workflow supersedes it). | Before A13 (parent-level workflow authoring). |
| C-lean-action-ci-promote | Move `geb-lean/.github/workflows/lean_action_ci.yml` to `geb/.github/workflows/lean_action_ci.yml` via `git mv`; add `paths: ['geb-lean/**']` filter on push/PR triggers; add `defaults.run.working-directory: geb-lean` at workflow level; add the `lake-package-directory: geb-lean` input to the `leanprover/lean-action@v1` step. (The `axiom_check` job addition is a main-plan task, not part of this cleanup.) | After C-workflow-rm; before the main plan's CI verification task. |
| C-gitignore-revert | Rewrite `geb-lean/.gitignore` so it contains no `.claude`-related patterns. Currently (at HEAD) it contains `/.claude/*`, `!/.claude/rules/`, `!/.claude/settings.json`, and `/docs/.claude`. Remove all of these. The parent `geb/.gitignore` (per § `.gitignore` change at the parent) becomes the only authoritative source for `.claude/`-path ignore and unignore decisions. After this task and the new plan's parent-`.gitignore` task, `git check-ignore -v geb-lean/.claude/settings.json` returns nothing (not ignored) and `git check-ignore -v geb-lean/.claude/settings.local.json` shows the path ignored via the parent's `/geb-lean/.claude/*` pattern. | Before the new plan's parent-`.gitignore` task. |
| C-markdownlint-config-rewrite | Rewrite `geb-lean/.markdownlint-cli2.jsonc`: (a) remove the top-level `globs` key, (b) replace all `ignores` patterns with both unprefixed forms (`.lake/**`, `node_modules/**`, `.session/**`, `.claude/memory/**`, `.claude/docs/**`, `.claude/tools/**`) and `geb-lean/`-prefixed forms (`geb-lean/.lake/**`, `geb-lean/node_modules/**`, `geb-lean/.session/**`, `geb-lean/.claude/memory/**`, `geb-lean/.claude/docs/**`, `geb-lean/.claude/tools/**`). `.jj/**` is deliberately omitted: jj manages its own git-visibility via the self-contained `.jj/.gitignore`, and adding it to markdownlint ignores would override any later jj decision to expose a markdown file. The unprefixed forms handle the `pre-push.sh` case (CWD is `geb-lean/`); the prefixed forms handle the parent-CWD CI case. The existing committed file (introduced at `aeae31f9`) carries a `"globs": ["**/*.md"]` key and ignores without either form. After this task, the config file matches the description in § `.markdownlint-cli2.jsonc` and both invocation contexts work correctly. | Before A2 (markdownlint verification). |
| C-hook-amend | Amend `geb-lean/scripts/hooks/block-mutating-git.sh` so its `.jj/` discovery uses `jj root` (exit 0 = jj is initialised somewhere up the tree) instead of `[[ -d $CLAUDE_PROJECT_DIR/.jj ]]`. After this task, the five `block-mutating-git.sh` smoke-test cases (originally Task A10 in the 2026-05-07 plan; the JSON-stdin payloads are: (a) `git commit -m '...'` → exit 2; (b) `jj git push --remote origin -b feat/x` → exit 0; (c) `git status` → exit 0; (d) `git checkout -b new-branch` → exit 2; (e) `git push origin 'refs/tags/v1.0.0:refs/tags/v1.0.0'` → exit 2) must be re-run after the amendment, and all five must produce the expected exits before A27 wires the hook into `.claude/settings.json`. | Precedes A27 (hook wiring into `.claude/settings.json`). Only after C-hook-amend lands and all five smoke-test cases pass may A27 proceed. |

## Order of artefact production

The order, which `docs/process.md` § 4 records explicitly,
is:

```text
brainstorm
  → write spec
  → spec self-review (inline; fixes commit on same branch)
  → spec adversarial-review cycle (loop until termination)
  → user spec review (loop with author until user approves)
  → write plan
  → plan self-review
  → plan adversarial-review cycle (loop until termination)
  → user plan review (loop with author until user approves)
  → execute the plan
```

The user-review step in this order is a
*post-adversarial-review* step: the user sees the artefact
only after self-review and adversarial review have already
converged. This shifts the brainstorming-skill default
(which is write → self-review → user review) by inserting
adversarial review between self-review and user review.

## Verification — definition of done

The refactor has **two milestones**:

- **Milestone A — Process bootstrap complete**: every
  structural change has landed and is verified. This
  milestone is bounded in scope and time-bounded by
  mechanical work.
- **Milestone B — `.session/` retired**: every legacy
  `.session/workstreams/` entry has been triaged, with
  `live` and `live-deferred-to-geb-mathlib` items migrated
  to `TODO.md` and the `.session/` directory removed.
  Triage is open-ended (78 entries plus harness tasks, each
  requiring user surface-and-confirm) and may take many
  sessions; Milestone B does not gate Milestone A.

During the period after Milestone A and before Milestone B,
`.session/` and `TODO.md` coexist; `CLAUDE.md` documents the
transitional arrangement.

### Milestone A — verification checklist

Mechanically checkable items (1–14) are confirmed by command;
interpretive items (15–17) are confirmed by user sign-off.

| # | Item |
| --- | --- |
| 1 | `lake build` and `lake test` succeed (no source-side breakage). |
| 2 | `markdownlint-cli2 --config geb-lean/.markdownlint-cli2.jsonc --no-globs 'geb-lean/**/*.md'` is quiet on the files newly authored or modified by this refactor: `geb-lean/CLAUDE.md`, `geb-lean/.claude/rules/*.md`, `geb-lean/docs/process.md`, `geb-lean/docs/index.md`, `geb-lean/docs/lean-resources.md`, `geb-lean/TODO.md`, `geb-lean/README.md`. Pre-existing markdown files outside this set are out of refactor scope. (The existing `.session/`, `docs/*.md`, `docs/research/*.md`, and `docs/superpowers/specs/*.review-*.md` files have markdownlint findings outside the refactor's scope; cleanup is a separate workstream after Milestone B's `.session/` retirement.) |
| 3 | `bash scripts/check-axioms.sh GebLean/ test/` runs to completion, produces output, and exits with a defined code. (In report-only mode, the script may report many flagged declarations because mathlib transitively introduces `Classical.choice`; this is the documented current state.) |
| 4 | `lake lint` is quiet on the current source AND, when a deliberate violation is introduced (e.g. an unused `set_option` or a `linter.unusedVariables`-tripping let-binding), `lake lint` flags it. The violation is then removed and `lake lint` returns to quiet. (Positive verification that `lintDriver = "batteries/runLinter"` is wired and active, not silently no-op.) |
| 5 | `geb-lean/CLAUDE.md` is under 200 lines and is markdownlint-clean. |
| 6 | `geb-lean/.claude/rules/lean-disciplines.md`, `lean-coding.md`, `markdown-writing.md`, `ci-and-workflow.md` exist and are markdownlint-clean. |
| 7 | `geb-lean/docs/process.md`, `docs/index.md`, `docs/lean-resources.md` exist and are markdownlint-clean. |
| 8 | `geb-lean/TODO.md` exists with both top-level sections; every entry follows the documented shape. |
| 9 | `geb-lean/README.md` exists and is authored in the new pattern; markdownlint-clean. Parent `geb/README.md` carries the brief pointer near the top. |
| 10 | `geb/.gitignore` is modified per the documented replacement in § `.gitignore` change at the parent; `geb-lean/.gitignore` contains no `.claude`-related patterns (none of the four currently present at HEAD: `/.claude/*`, `!/.claude/rules/`, `!/.claude/settings.json`, `/docs/.claude`). Verified by three `git check-ignore` tests run from the parent `geb/` root: (a) `git check-ignore -v geb-lean/.claude/settings.json` returns nothing (path not ignored); (b) `git check-ignore -v geb-lean/.claude/rules/lean-coding.md` returns nothing (path not ignored); (c) `git check-ignore -v geb-lean/.claude/settings.local.json` identifies the path as ignored via the parent's `/geb-lean/.claude/*` pattern (no negation for `.local.json`). |
| 11 | jj is initialised colocated at the parent `geb/` root; `geb/.jj/.gitignore` exists; `jj root` (run from any path under `geb/`) exits 0; `jj config list --repo git.private-commits` outputs a TOML line whose extracted bare value equals `conflicts()` exactly (anchored, not substring; `check-jj-setup.sh` strips the TOML wrapper via `sed` before comparing); `jj config list --repo remotes.origin.fetch-tags` outputs a TOML line whose extracted bare value equals `glob:cutover-*` exactly (anchored; same stripping); `jj config path --repo` prints a path in user-config-dir (per jj 0.38+'s config-relocation), not under `.jj/`. Per-developer signing and identity are set at user-level. |
| 12 | `geb-lean/.claude/settings.json` (committed) wires `block-mutating-git` (PreToolUse) and `check-signing-key` (SessionStart). The hook script is smoke-tested **by direct invocation** — feed synthesised JSON-stdin payloads representing tool invocations, assert the exit code (0 = allow, 2 = block). The synthesised JSON payloads themselves do not invoke `git` or `jj`; the hook script's own `jj root` (a read-only subprocess, no arguments) runs as a side effect of the hook's jj-detection logic. For case (b) to produce exit 0, the smoke test must run with the working directory inside a jj-initialised tree (e.g. `cd /path/with/.jj` first, or set `CLAUDE_PROJECT_DIR` to a directory with a `.jj/` subdirectory). The smoke test may therefore be deferred until after A24 (`jj git init --colocate` at the parent `geb/` root) so that the jj-initialised tree is available; alternatively the test can run immediately after C-hook-amend by using `CLAUDE_PROJECT_DIR` pointing to any `.jj/`-containing directory. Required cases: (a) `git commit -m '...'` returns 2 (blocked, exercising the default-deny default); (b) `jj git push --remote origin -b feat/x` returns 0 (allowed; `jj git X` forms are stripped from the hook's scope); (c) `git status` returns 0 (allowed read-only subcommand); (d) `git checkout -b new-branch` returns 2 (blocked mutating subcommand); (e) `git push origin 'refs/tags/v1.0.0:refs/tags/v1.0.0'` returns 2 (blocked — no tag-push allowlist entry exists; tag operations are user-direct per § Hooks). |
| 13 | `geb/.github/workflows/markdown-lint.yml` exists (at the parent level) and is path-filtered to `geb-lean/**`. `geb/.github/workflows/lean_action_ci.yml` exists (promoted) with `paths: ['geb-lean/**']` filter; the `leanprover/lean-action@v1` step passes `lake-package-directory: geb-lean`; the workflow carries a top-level (workflow-level) `defaults.run.working-directory: geb-lean` key so all `run:` steps in all jobs execute from `geb-lean/`; and the `axiom_check` job declares `needs: [build]` so it runs after the `build` job has populated `.lake/`. (Note: `defaults.run.working-directory` applies only to `run:` steps, not to `uses:` steps; `lake-package-directory` is the correct mechanism for the lean-action step; `actions/checkout` is a `uses:` step unaffected by `defaults.run.working-directory`.) |
| 14 | `geb-lean/scripts/check-axioms.sh`, `check-jj-setup.sh`, `pre-push.sh`, `hooks/block-mutating-git.sh`, `hooks/check-signing-key.sh` all exist, are executable, and pass a smoke-test invocation. `check-jj-setup.sh` returns non-zero for a deliberately-unconfigured fresh clone and zero after the on-boarding sequence completes. `check-signing-key.sh`: `bash scripts/hooks/check-signing-key.sh; echo "exit=$?"` returns exit=0; the script's stderr is empty unless a configured signing backend is unavailable (in which case the diagnostic message is informational and does not affect the exit code). |
| 15 | The refactor's spec and plan have each gone through fresh-context adversarial review until termination, where termination means every finding is cosmetic-taste, rationale-rejected, or fixed (no open blocker / serious / minor findings remain). |
| 16 | The user has reviewed the final state and confirmed Milestone A is complete. |
| 17 | The refactor's work has been performed on a topic branch (`chore/process-refactor`). The merge commit on the parent's `main` that lands this work is recorded as the **cutover commit**. The **primary record** of the cutover SHA is a signed git tag (e.g. `cutover-2026-MM-DD`) pushed to the remote. The signing and pushing of the cutover tag are user-manual operations performed in the user's own terminal outside Claude Code (per § Hooks); the user chooses an unambiguous push form, either `git push origin tag cutover-2026-MM-DD` (specific tag) or `git push origin 'refs/tags/cutover-*:refs/tags/cutover-*'` (wildcard refspec). The bare-name form `git push origin cutover-2026-MM-DD` is avoided because git would resolve `cutover-2026-MM-DD` against both branch and tag namespaces and refuse if both exist; using `tag` or the explicit refspec disambiguates. Before pushing, the user verifies the local `cutover-*` tag listing contains exactly one entry (`git tag --list 'cutover-*'` prints exactly one line); any stray tags from earlier attempts are resolved first. The tag is protected from deletion by the repository protection rules (item 17a). `docs/process.md` § Branch model carries the same SHA as a navigation aid only; the tag is authoritative. From the cutover commit forward, `git log --first-parent origin/main` (against the remote, not the local `main` or its reflog) shows only fast-forward updates and normal merge commits — no force-pushes. The append-only invariant binds commits whose first parent is at or after the cutover SHA; pre-cutover history is exempt. |
| 17a | GitHub repository protection rules are configured on the parent repo: on `main`, branch-protection rules forbid force-pushes and branch deletion; on tags matching `cutover-*`, a Ruleset (under Repository settings → Rulesets) forbids deletion. (Tag protection rules under Settings → Tags are a deprecated alternative still available on most repositories; either mechanism suffices, but the Ruleset is preferred.) This forecloses the path by which the cutover tag itself could be tampered with. |

### Milestone B — `.session/` retirement

| # | Item |
| --- | --- |
| B1 | Every `.session/workstreams/*.md` file has been triaged per the six-label scheme; each disposition has user confirmation. |
| B2 | `TODO.md` is populated with all `live` and `live-deferred-to-geb-mathlib` items. |
| B3 | `docs/index.md` carries entries for the major `completed` workstreams. |
| B4 | `.session/` directory (including its `README.md`) has been removed. |
| B5 | The Claude-harness task list has been reset: brainstorming-tracking tasks #534–#542, the plan's tasks, and any tasks of currently-`live` workstreams are kept; the rest are archived or deleted. |
| B6 | The user has reviewed the final state and confirmed Milestone B is complete. |
| B7 | `axiom_check` job has been flipped from report-only mode to fail-mode; report-only mode has been retired. After the flip, `bash scripts/check-axioms.sh GebLean/ test/` reports no non-allowlisted axioms (every flagged declaration carries an `AXIOM_ALLOW` comment). |

## Open questions / deferred decisions

- **`check-signing-key.sh` ssh-backend warm-correctness**: the
  ssh-backend warm path invokes `ssh-add -l` and exits 0 if
  any key is loaded. If the loaded keys do not include the
  developer's configured signing key (e.g., the developer has
  a non-signing-key loaded in ssh-agent), the hook reports
  success but the next signed commit will still fail.
  Resolution path: extend the hook to read the configured
  signing-key fingerprint (from git/jj config) and compare
  against `ssh-add -l` output; defer to a separate cleanup
  workstream once the ssh-signing flow is more thoroughly
  characterised.
- **`check-jj-setup.sh` signing.behavior verification scope**:
  assertion (c) accepts `signing.behavior = own` without
  verifying that `signing.key` (or the equivalent ssh-key
  path config) is populated and refers to a key the agent can
  access. A more thorough check would verify the signing
  key's existence and accessibility; deferred to a later
  cleanup workstream alongside the ssh-backend fix above.
- **Specific markdownlint rule customisations** in
  `.markdownlint-cli2.jsonc` (line length, MD013, link
  checking). The plan resolves these in response to
  false-positive friction encountered while authoring the
  refactor's artefacts; the spec fixes only the framework.
- **SHA-pinning sweep** of the existing workflow files'
  third-party action references. Performed opportunistically
  as the plan touches each workflow; not a hard verification
  gate.
- **Re-enabling commit signing on the existing remote** if
  any current divergence between local git signing config
  and the GitHub remote's expectations exists. The plan
  inspects and adjusts.
- **`scripts/hooks/tests/`** smoke-test infrastructure as
  in `geb-mathlib`'s design: deferred. The hook scripts
  themselves are exercised manually during refactor
  verification (item 12); a CI-runnable smoke test is a
  later addition if the hook implementations grow
  non-trivially.
- **Release-tag naming convention**: the spec preserves the
  existing `create-release.yml` workflow but does not fix a
  tag-naming convention. The convention can be fixed later
  without spec change since tag operations are user-direct
  (§ Hooks) and don't depend on hook allowlist entries. Once
  fixed, the convention is recorded in `docs/process.md`
  § Branch model.
- **Eventual standalone repo split-out**: when and how
  geb-lean may become its own git repo (rather than a
  subdirectory of geb/) is a deferred decision outside this
  refactor's scope.

## References

- `geb-mathlib` bootstrap design (in the sibling repository)
  at
  `docs/superpowers/specs/2026-05-04-geb-mathlib-bootstrap-design.md`.
- `geb-mathlib` bootstrap plan (in the sibling repository)
  at
  `docs/superpowers/plans/2026-05-04-geb-mathlib-bootstrap-plan.md`.
- 2026-05-07 process bootstrap design (superseded):
  `docs/superpowers/specs/2026-05-07-process-bootstrap-design.md`.
- jj v0.41 documentation:
  <https://docs.jj-vcs.dev/latest/git-compatibility/>,
  <https://docs.jj-vcs.dev/latest/config/>,
  <https://docs.jj-vcs.dev/latest/revsets/>.
- Anthropic `CLAUDE.md` documentation:
  <https://code.claude.com/docs/en/memory>.
- mathlib contributor guide:
  <https://leanprover-community.github.io/contribute/index.html>,
  <https://leanprover-community.github.io/contribute/doc.html>,
  <https://leanprover-community.github.io/contribute/commit.html>.
- `lean4-skills` `check_axioms_inline.sh` (vendored source).
- GNU General Public License version 3 (at parent
  `geb/LICENSE`): the governing file is `../LICENSE`.

### Empirical verifications

These claims in the spec are verified by running commands
and observing output, rather than by citation:

- `jj git init --colocate` creates `.jj/.gitignore` with
  contents `/*\n` (3 bytes). Verified by sandbox invocation
  against jj 0.40 (initial) and re-verified against jj
  0.41.0 in an empty git repository
  (`git init -q && jj git init --colocate`), followed by
  inspection of the resulting `.jj/.gitignore` contents
  (`xxd .jj/.gitignore` showed `2f2a 0a` = `/*\n`).
  Behaviour persists between 0.40 and 0.41. Should a later
  jj version change this behaviour, the manual fallback
  documented in the upstream colocated-conversion procedure
  (`echo '/*' > .jj/.gitignore`) remains applicable and is
  reproduced in `docs/process.md` § jj as a safety net.
- `jj git init --colocate` printed
  `Hint: Running 'git clean -xdf' will remove '.jj/'!` in
  jj 0.40, but **the hint was removed in jj 0.41** (verified
  empirically: jj 0.41.0's colocate output contains only
  "Done importing changes from the underlying Git repo." and
  "Initialized repo in '.'"). The `git clean -xdf` warning
  is therefore documented entirely in `docs/process.md`
  § jj rather than relying on jj's runtime hint.
- `lakefile.toml`'s `moreLeanArgs = ["-DwarningAsError=true"]`
  setting is currently in effect; the refactor preserves it.
- `jj root` (no arguments) walks up from CWD to locate
  `.jj/` and exits 0 when found. This is the portable
  mechanism used in `block-mutating-git.sh` and
  `check-jj-setup.sh` to detect jj availability regardless
  of whether `.jj/` is at the parent or at a subdirectory.

### jj 0.36–0.41 behavior changes affecting this spec

Verified against the jj release notes
(<https://github.com/jj-vcs/jj/releases>) and
<https://docs.jj-vcs.dev/latest/config/>. The spec assumes
jj 0.41+ as the project standard. Findings shaping spec
content:

- **v0.41**: New `remotes.<name>.fetch-bookmarks` and
  `remotes.<name>.fetch-tags` config options accepting
  string patterns (verbatim from the docs: *"You can
  configure which bookmarks and tags to fetch by default per
  remote, using the
  `remotes.<name>.fetch-bookmarks`/`fetch-tags` config. The
  value is a string pattern that matches the names of the
  bookmarks and tags to fetch."*). **`fetch-tags` is
  documented as experimental** (verbatim: *"Note that
  `remotes.<name>.fetch-tags` is experimental"*). The spec
  uses `remotes.origin.fetch-tags = 'glob:cutover-*'` to
  make `jj git fetch` mirror the cutover tag automatically;
  this obviates the explicit raw-`git fetch` refspec form
  (and its hook-allowlist entry) that earlier versions of
  this spec needed. **The spec's minimum jj version is 0.41
  for this reason.** If the experimental feature is removed
  or its semantics change, the fallback (re-introduce the
  explicit refspec form and its allowlist entry) is
  documented in § jj setup.
- **v0.38**: Per-repo and per-workspace config moved outside
  the repository for security reasons. `.jj/repo/config.toml`
  is no longer used. Canonical commands:
  `jj config edit --repo`, `jj config path --repo`, and
  `jj config set --repo <key> <value>`. The spec's jj setup
  uses these commands rather than a committable file
  template.
- **v0.36**: `git.push-new-bookmarks` and
  `git.auto-local-bookmark` deprecated in favour of
  `remotes.<name>.auto-track-bookmarks`. The spec does not
  use any of these, but contributors moving from older jj
  workflows should be aware.
- **v0.37**: String patterns in revsets, command arguments,
  and configuration are now parsed as globs by default.
  Explicit `glob:"…"` is therefore *redundant* in jj 0.41
  — the spec retains it for forward-protection (jj is
  pre-1.0; default semantics may change).
- **v0.38** (re-stated in v0.41 release notes):
  `jj git push --all`/`--tracked`/`-r REVSETS` no longer
  fails when revisions to push are private or have
  conflicts; ineligible bookmarks are skipped. Individual
  bookmark pushes are unaffected; `git.private-commits`
  continues to apply at push time per the docs.
