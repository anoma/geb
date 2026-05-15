# geb-lean process and conventions

This document records *why* each rule in `CLAUDE.md` and
`.claude/rules/*.md` exists. The rules themselves live in those
files; this document explains the motivation behind each. Read it
when you need to understand the reason for a rule, propose a
change, or weigh how to apply a rule in an unfamiliar situation.

## Sections

- [geb-lean process and conventions](#geb-lean-process-and-conventions)
  - [Sections](#sections)
  - [Repository structure](#repository-structure)
  - [Code is cost](#code-is-cost)
  - [Document only the persistent](#document-only-the-persistent)
  - [Illustrate only with the archetypal](#illustrate-only-with-the-archetypal)
  - [Avoid colloquialisms and metaphors](#avoid-colloquialisms-and-metaphors)
  - [Documentation under `docs/`](#documentation-under-docs)
  - [Adversarial review](#adversarial-review)
  - [Verify agent claims](#verify-agent-claims)
  - [main and integration](#main-and-integration)
  - [Markdownlint discipline](#markdownlint-discipline)
  - [No LLM-drafted user-facing text](#no-llm-drafted-user-facing-text)
  - [Generic user references](#generic-user-references)
  - [Fork–upstream relationship](#forkupstream-relationship)
  - [Phase-driven workflow](#phase-driven-workflow)
  - [`jj` colocated mode](#jj-colocated-mode)
  - [Process self-update mechanism](#process-self-update-mechanism)
  - [Literature-citation discipline](#literature-citation-discipline)
  - [Bottom-up named-composite discipline](#bottom-up-named-composite-discipline)
  - [Non-negotiable interfaces](#non-negotiable-interfaces)
  - [Relationship to geb-mathlib](#relationship-to-geb-mathlib)
  - [No per-file copyright or author headers](#no-per-file-copyright-or-author-headers)

## Repository structure

The repo is laid out narrow-and-deep: every directory has either a
small number of subdirectories or a small number of source modules,
with one indexing `.lean` file per directory. The path is itself
documentation. This policy resembles mathlib's.

## Code is cost

Every committed byte must be justified by a return greater than
its cost. Cost has several components:

- **Reader time and cognitive capacity.** Anyone reading the
  codebase — human or AI — pays attention to every file, every
  line, every comment.
- **Drift and obsolescence.** Code falls out of sync with the
  rest of the codebase as surrounding things change. Comments
  are particularly susceptible, being unverified by compilation.
- **Dependence pressure.** Code that depends on something else
  freezes that thing in place: changing the dependency requires
  changing the dependent. The more code depends on a given thing,
  the harder that thing is to change.
- **Process overhead.** Every line lengthens build time, commit
  diffs, code-review time, search results, and AI-context
  consumption.

## Document only the persistent

A direct corollary of "Code is cost". Comments and committed text
should describe what is enduring about the code as it is — its
purpose, contracts, and non-obvious external constraints.
They should not describe transient process artifacts such as:

- **History.** "Previously this used X; now it uses Y."
  "Refactored from a different shape." How the code arrived at
  its current form belongs in commit messages, not in the code.
- **Testing process.** "Verified by testing." "This caused a
  build failure that was fixed by...." How something was
  discovered belongs in the project-internal findings log,
  not in the code.
- **Project-management artifacts.** "Required by spec § X.Y."
  Tasks and plan numbers are ephemeral — they exist during a
  discrete project phase and lose meaning afterward; readers of
  the code should not need to consult an external document just
  to understand the comments.
- **In-progress notes.** "TODO: rewrite this when we have time."
  "Try this approach if X fails." Active work belongs in
  `TODO.md` or the workstream's spec/plan, not in code comments.

What's persistent and worth documenting:

- The code's purpose at the namespace / module / declaration
  level (its contract).
- Non-obvious external constraints.
- Cross-references to specific external documentation (mathlib's
  contribute pages, jj's documentation), where the cross-reference
  saves a reader from re-deriving the constraint.

The principle is: when this codebase is years old, the comments
should still read as useful context. Anything that won't survive
that test belongs elsewhere.

## Illustrate only with the archetypal

A corollary of "Document only the persistent". When a rule or
explanation needs an illustration, the example should be
archetypal — a timeless mathematical or physical concept that
cannot become obsolete. Incidental examples (a particular task,
test artifact, or transient project state) consume reader
attention with trivialities and rot as the codebase evolves; an
archetypal example continues to teach the rule years later.

## Avoid colloquialisms and metaphors

Only standard technical terms are precise and universal enough
for our purposes. The rule binds all committed text; the rule
statement lives in `CLAUDE.md` § Style guidelines.  Examples
(where not specific technical terms) include "land", "gap",
and "gate".

## Documentation under `docs/`

`docs/index.md` is the project's reader-facing description: the
directory layout and a topological narrative of the implemented
content. Each entry covers the source-tree paths it touches, the
central concepts it introduces, and its dependencies (other
entries here, or specific external modules). Documentation is
updated in concert with any code change that introduces new
content appropriate to document, such as the formalisation of a
new mathematical concept.

`docs/process.md` (this file) contains the rationale for each
rule that binds development; `docs/lean-resources.md` catalogues
external library and mathematical references organised by topic.
Both are reader-facing alongside `docs/index.md`.

## Adversarial review

Specs and plans go through fresh-context adversarial review until
convergence (no blockers, no serious findings). The reviewer is a
NEW general-purpose `Agent` invocation per round (not
`SendMessage` to a continuing agent), reading only the artifact at
the given path. Findings are categorised blocker / serious / minor
/ cosmetic-taste; the author responds in writing to every finding
(fix / defer with rationale / reject as cosmetic-taste). The
discipline catches bugs the author cannot see; the fresh context
ensures the reviewer is not subject to the author's blind spots.

### Reviewer protocol

The reviewer reads the artefact at the given path, its cited
sources, and any additional file or read-only remote resource
needed to verify a factual claim the artefact makes. Each
round's reviewer is fresh so that it is not anchored to the
previous round's findings or to the author's framing of fixes.
The procedure is the same for spec documents and plan documents.

The reviewer may invoke read-only operations to verify
claims: file reads, read-only `git` (e.g. `git remote -v`,
`git log`), read-only `jj` (e.g. `jj git remote list`,
`jj config list`), read-only `gh` (e.g. `gh api <path>`,
`gh repo set-default --view`), tool `--help` invocations,
and read-only MCP queries. The reviewer must not invoke
mutating operations of any kind: no commits, pushes, fetches
that alter the working copy, file writes, `gh` write commands,
or shell commands that mutate filesystem state outside the
working copy. The reviewer's output is the only artefact it
creates; the author is responsible for writing it to disk.

### Defect categorisation

Every defect the reviewer reports is one of four severities:

| Severity | Definition | Examples |
| --- | --- | --- |
| Blocker | The artefact cannot be implemented as written, or if implemented would violate a project rule (`CLAUDE.md` § Rules). | A factual error in a command form; a precondition that makes an operation fail in a real case; a direct contradiction with a project rule. |
| Serious | The artefact admits an interpretation that produces a wrong result, or omits a case that is in scope. | Ambiguity readable two ways; missing handling of a flow the artefact implicitly requires; under-specification that forces the implementer to guess. |
| Minor | Imprecise prose, redundancy, or organisation that does not affect implementability. | A heading that duplicates information; an inefficient ordering of bullets; a citation that could be more specific. |
| Cosmetic-taste | Typography, line wrapping, register-list word choice, or other surface concerns that do not affect meaning. | Markdownlint violations; whitespace; choice between two equally clear phrasings. |

The reviewer assigns exactly one severity per defect. Severity
labels follow the same definitions across rounds and across
workstreams.

### Author response

For every finding, the author records a one-line response in
the defect's entry, choosing one of:

- **fix**: applied inline to the artefact, with the corrected
  text or a pointer to the resulting edit. The author re-runs
  markdownlint and the register sweep on the artefact after
  the fix.
- **defer-with-rationale**: recorded as explicit out-of-scope,
  with a one-sentence reason. Blocker- and serious-severity
  findings cannot be deferred without a recorded out-of-scope
  rationale (and that rationale must itself withstand a later
  adversarial review).
- **reject-as-cosmetic-taste**: limited to cosmetic-taste
  findings; the response sentence states why the surface
  concern is not adopted.

Minor and cosmetic-taste findings may be fixed, deferred, or
rejected at the author's discretion.

### Convergence criterion

A round **converges** when its reviewer reports zero blocker and
zero serious findings. Minor and cosmetic-taste findings are not
a barrier to convergence and may remain open at termination.

### Loop

After each round, the author applies responses, and a new
fresh-context reviewer is dispatched for the next round. Each
round is recorded in a numbered review file alongside the
artefact (e.g.
`docs/superpowers/specs/<topic>.review-1.md`,
`docs/superpowers/specs/<topic>.review-2.md`). The loop
terminates when a round meets the convergence criterion. The
terminating round's review file is the convergence record.

### Formatting

Adversarial review files are markdownlint-clean against
`.markdownlint-cli2.jsonc` (line length 80; tables and fenced
code blocks exempt) and follow the register rules in
`.claude/rules/markdown-writing.md`. The author edits the
reviewer's output as needed to meet these constraints; this
editing is not a substantive change to the findings and does
not require re-dispatch.

## Verify agent claims

Any factual claim about an external system (mathlib, Lean,
third-party tools, jj, GitHub conventions, library APIs) is
provisional until verified against authoritative sources.
Committed artifacts include the citation alongside the claim.
Adversarial reviewers explicitly check for unverified claims. AI-agent memory
is unreliable for facts about external systems; verification at
use time keeps committed content trustworthy.

## main and integration

`main` is append-only stable history; never force-pushed. Topic
branches are merged without force-pushing.
`integration` is the regenerated fan-in merge view of `main` plus
active topic branches; force-pushed (lease-protected by default)
as topic-branch tips move. The split keeps `main` fork-friendly
(clones never see force-pushed history) while giving us a single
working view of all in-flight work.

Topic branches use prefix-by-purpose names (`feat/`, `fix/`,
`refactor/`, `chore/`, `docs/`, `bump/`) and carry their
workstream's spec, plan, and code together until the branch lands
on `main`.

## Markdownlint discipline

Every Markdown document passes `markdownlint-cli2` against
`.markdownlint-cli2.jsonc` (shared with VSCode extension).
`.remember/` is intentionally not excluded; non-compliant remember
output is edited locally. The discipline keeps documentation
uniformly readable; sharing the config with VSCode means the
editor catches violations as we type.

The config's `ignores` array (e.g. `.session/**`,
`docs/superpowers/plans/**`, etc.) suppresses files in glob
expansion AND in explicit-path arguments. To lint a single file
that lives in an ignored directory, use the `:` literal-path
prefix documented by `markdownlint-cli2 --help`:

```sh
markdownlint-cli2 ':.session/README.md'
```

The leading `:` marks the argument as a literal path that
bypasses both the config's `globs` and `ignores` matching;
`--no-globs` alone does not bypass `ignores` (it suppresses
only the `globs` key).

## No LLM-drafted user-facing text

PR descriptions, GitHub issue/PR comments are user-authored.
Mathlib's policy is unconditional ("use your own words").
Multi-layered enforcement: hard rule in `CLAUDE.md`, pre-push
reminder in `scripts/pre-push.sh`, PR template checkbox,
user-review-before-push gate. The redundancy is intentional.
Claude may produce drafts marked "for paraphrasing"; the posted
text is the user's own writing.

## Generic user references

"the user" / "they" / "them" generically in committed text. No
first names, email, or autobiographical detail. Committed content
should make sense to any contributor; specific identities make it
read as a single author's project. Per-developer local state,
including user-level `jj config` for `user.name`, `user.email`,
and `signing.*`, lives outside the repository per jj 0.38+'s
config-location model and is exempt from this rule.

## Fork–upstream relationship

The local working copy is a clone of the fork at
`rokopt/geb` ("origin"), itself a fork of the canonical
repository at `anoma/geb` ("upstream"). Both are
administered by the same operator. Daily work pushes to
the fork; upstream receives commits only through merged
pull requests opened from the fork.

### Remote roles

| Remote | URL | Role |
| --- | --- | --- |
| origin | `ssh://git@github.com/rokopt/geb` | Daily fork; push target for topic branches. |
| upstream | `git@github.com:anoma/geb.git` | Canonical repository; PR target only. |

### Invariants

The fork-first push rule, the no-direct-push-to-upstream
rule, the merge-commit-strategy-on-synchronising-PRs
rule, the append-only-on-both-default-branches rule, and
the lockstep-after-merge rule are recorded in directive
form in `.claude/rules/fork-upstream-flow.md`. The
mechanical denial of direct upstream pushes lives in
`scripts/hooks/block-mutating-git.sh`.

## Phase-driven workflow

Each chunk of work passes through brainstorm, spec, plan, and
execute phases. Skills load on demand at the phase they apply
to (`superpowers:brainstorming`, `superpowers:writing-plans`,
`superpowers:executing-plans`, the `lean4:*` family, and so on);
`CLAUDE.md` and the unscoped `.claude/rules/*.md` files load at
session start.

Each workstream proceeds: brainstorm, then spec, then spec
self-review, then spec adversarial review (looped to
convergence), then user spec review, then plan, then plan
self-review, then plan adversarial review (looped to
convergence), then user plan review, then execute. Specs and
plans co-evolve with code on the same topic branch; the
brainstorm output, spec, plan, and review iterations are all
commits on that branch.

Three MCP servers attach at the session level rather than
per-skill:

- `arxiv-mcp-server` — search, download, and read papers when a
  workstream cites external mathematical sources.
  Upstream: <https://github.com/blazickjp/arxiv-mcp-server>.
- `memory` — graph-shaped scratchpad that persists session-level
  observations across restarts.
  Upstream:
  <https://github.com/modelcontextprotocol/servers/tree/main/src/memory>.
- `MCP Solver` — constraint and SAT solving via Python bindings,
  used for combinatorial side-conditions.
  Upstream: <https://github.com/szeider/mcp-solver>.

## `jj` colocated mode

`geb-lean/` is a subdirectory of the `geb/` monorepo, not a
standalone repository. The version-control root, hooks, CI
workflows that touch `geb-lean`, and the parent `LICENSE` all
live one directory up. Repository-scoped hooks live at
`geb-lean/scripts/hooks/`. CI workflows that touch `geb-lean`
live at the parent `geb/.github/workflows/`. The pre-push hook
is `geb-lean`-scoped: it builds and tests only `geb-lean`
artefacts.

`jj` runs in colocated mode at the parent `geb/` root, not at
`geb-lean/`. A single `jj git init --colocate` step at the
parent populates `geb/.jj/`. `jj` writes
`geb/.jj/.gitignore` containing `/*`, which makes `.jj/` invisible
to git via self-exclusion; the project does not need to add
`.jj/` to the parent `.gitignore`. `git clean -xdf` would delete
`.jj/` and so must not be run on this tree; routine cleanups use
narrower targets.

A new developer onboards with this exact sequence, run from the
parent `geb/` root. The sequence assumes the working copy was
created by `git clone ssh://git@github.com/rokopt/geb.git geb`,
which registers `origin` as a git remote pointing at
`rokopt/geb` and places `geb/` as the parent of `geb-lean/`. If
`origin` is absent, register it with `git remote add origin
ssh://git@github.com/rokopt/geb` before continuing. Users who
prefer `jj git clone --colocate` arrive at an equivalent state
but skip step 1 (`jj git init --colocate`) and continue from
step 2. Per-repo configuration is set before the first
`jj git fetch --remote origin` so the fetch applies the
`fetch-tags` pattern:

1. `jj git init --colocate`.
2. Per-repo configuration:
   - `jj config set --repo git.private-commits 'conflicts()'`
   - `jj config set --repo remotes.origin.fetch-tags
     'glob:cutover-*'`
   - `jj config set --repo remotes.upstream.fetch-tags
     'glob:cutover-*'` (recommended; mirrors the origin
     entry for a later cutover-tag propagation. Not
     enforced by `check-jj-setup.sh`.)
3. Per-developer signing and identity (user-level, not
   per-repo):
   - `jj config set --user user.name '<name>'`
   - `jj config set --user user.email '<email>'`
   - `jj config set --user signing.behavior 'own'`
   - `jj config set --user signing.backend 'gpg'` (or `'ssh'`)
   - `jj config set --user signing.key '<key id>'`
4. `jj git fetch --remote origin` to mirror bookmarks into jj's
   view.
5. `gh repo set-default rokopt/geb` to direct `gh` default-base
   commands at the fork.
6. `bash geb-lean/scripts/check-jj-setup.sh` to verify the
   configuration.

The `remotes.origin.fetch-tags` setting is documented as
experimental in jj 0.41+. If a later jj release removes the
setting, the explicit fallback is to add
`git fetch origin 'refs/tags/cutover-*:refs/tags/cutover-*'`
to the on-boarding sequence in place of step 4's tag-mirroring
behaviour. The repository assumes jj 0.41+.

## Process self-update mechanism

When a session uncovers a missing rule, an underspecified
rule, or a contradiction between rules, the corrective edit
to `CLAUDE.md`, `.claude/rules/*.md`, or this file is part of
the workstream that uncovered it. Rule edits are reviewed by
the same brainstorm-spec-plan-execute pipeline as Lean code
edits. The rationale layer here is updated in lock-step with
the rule text it explains.

## Literature-citation discipline

Some workstreams in this repository transcribe published
mathematics rather than introducing original constructions; the
`ER` to `K^sim_2` equivalence is the present example.
In transcription workstreams, every planned function,
definition, or theorem in a plan document carries a reference
to the literature proposition, theorem, or in-codebase lemma
it corresponds to, and every implemented function, definition,
or theorem includes the literature reference in its docstring.
Citations are specific (e.g.
"Tourlakis 2018 §0.1.0.27 (3)") and reference the project's
research documents in `docs/research/`. Original-content
workstreams (the broader categorical-foundations material) are
not bound by this discipline; citations are encouraged where
applicable but not required. The rule lives in `CLAUDE.md`
§ Rules.

## Bottom-up named-composite discipline

When building a new categorical structure to be related by an
equivalence or functor to an existing one, no constructor is
added to the new category before its image in the target
category exists as a named `def` (with a `@[simp]` interpretation
lemma) built bottom-up from the target's atomic generators. If
a proposed construct cannot be expressed as a composition of
the target's generators, that absence is a signal not to add
the construct. The discipline preserves the equivalence by
construction at every incremental step. The rule lives in
`.claude/rules/lean-coding.md`.

## Non-negotiable interfaces

When a workstream formalises a specific external mathematical
object, the interface of the resulting Lean category — its
objects, primitive constructors, and generators — is fixed by
the external source. Implementation strategies (proof tactics,
auxiliary inductives, choice of named composites) are free to
change as better routes appear; interface changes are not a
valid response to an implementation that fails to close. If an
implementation does not close, the corrective moves are
strengthening supporting infrastructure, re-examining the
proof strategy, or surfacing the obstruction for discussion —
not weakening the interface. The rule lives in
`.claude/rules/lean-coding.md`.

## Relationship to geb-mathlib

`geb-mathlib` is a separate repository for content that meets
mathlib's contribution standards. `geb-lean` is the
experimentation counterpart: original research, exploratory
category theory, and material that is not yet upstreamable.
`TODO.md` entries marked "to be done in geb-mathlib" denote
material that is intended for the curated repository once it
stabilises here; migration happens by extracting the stabilised
module to `geb-mathlib`, replacing the local copy with an import,
and removing the `TODO.md` entry. This repository does not adopt
a `Mathlib/` versus `Internal/` split: `geb-mathlib` plays the
curated role, so a sub-tree boundary inside `geb-lean` would
duplicate that distinction without adding information.

## No per-file copyright or author headers

`.lean`, `.md`, and other text files in this repository do not
carry per-file copyright or author headers for original content.
The repository-level `LICENSE` at the parent `geb/` root (GNU
General Public License version 3) covers all original GebLean
code; GPLv3 does not require per-file headers for original
work. Vendored upstream content (for example, files copied
from mathlib or `lean4-skills`, which carry Apache 2.0
notices) preserves any per-file notices it carries verbatim per
those upstream licences' requirements. The divergence from
mathlib's per-file `Authors:` template is a deliberate stylistic
choice rather than an oversight.
