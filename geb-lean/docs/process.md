# geb-lean process and conventions

This file is the rationale layer for the conventions that govern
work in `geb-lean/`. The mechanical rules live in `CLAUDE.md` and
in path-scoped files under `.claude/rules/`. Each section below
links those rule files to the reasoning behind them and to the
spec at
`docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`.

## Repository structure

`geb-lean/` is a subdirectory of the `geb/` monorepo, not a
standalone repository. The version-control root, hooks, CI
workflows that touch `geb-lean`, and the parent `LICENSE` all
live one directory up. `jj` is colocated at the parent `geb/`
root. Repository-scoped hooks live at `geb-lean/scripts/hooks/`.
CI workflows that touch `geb-lean` live at the parent
`geb/.github/workflows/`. The pre-push hook is `geb-lean`-scoped:
it builds and tests only `geb-lean` artefacts.

## Phase-driven workflow

Each chunk of work passes through brainstorm, spec, plan, and
execute phases. Skills load on demand at the phase they apply
to (`superpowers:brainstorming`, `superpowers:writing-plans`,
`superpowers:executing-plans`, the `lean4:*` family, and so on);
`CLAUDE.md` and the unscoped `.claude/rules/*.md` files load at
session start. Three MCP servers attach at the
session level rather than per-skill:

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

The same list appears in `CLAUDE.md` § Tooling; the two must be
kept in sync.

## Adversarial review of specs and plans

Specs and plans are reviewed in a fresh-context adversarial pass
before user approval, distinct from the author's self-review.
The adversarial reviewer reads only the artefact under review
plus its cited sources, and produces a numbered list of
defects. Authoring iterates against the review until convergence.
The procedure is the same for spec documents and plan documents.
Adversarial reviews must themselves be markdownlint-clean, since
they are committed to the tree alongside the artefacts they
review.

## Order of artefact production

Each workstream proceeds: brainstorm, then spec, then spec
self-review, then spec adversarial review (looped to
convergence), then user spec review, then plan, then plan
self-review, then plan adversarial review (looped to
convergence), then user plan review, then execute. Specs and
plans co-evolve with code on the same topic branch; the
brainstorm output, spec, plan, and review iterations are all
commits on that branch.

## Verify agent claims against authoritative sources

When an agent (sub-agent or otherwise) reports a fact about the
codebase, the build state, or the literature, the receiving
party verifies it directly against the named source before
acting. Build claims are verified by re-running `lake build` and
`lake test`; literature claims are verified by reading the cited
passage; codebase claims are verified by reading the named file.
This rule applies symmetrically to claims made by Claude and
claims made by the user.

## Constructive-only Lean code

Committed Lean code does not import or `open` `Classical`, does
not use the `classical` tactic attribute, and does not use
`noncomputable` or `axiom`. `Quotient` and `Quot` are used via
their constructive API (`mk`, `lift`, `ind`, `sound`); `Quot.out`
and `Quotient.out` are excluded because they require
`Classical.choice`. The `scripts/check-axioms.sh` script flags
non-allowlisted axioms in pre-push and CI. The full statement
of this rule lives in `.claude/rules/lean-disciplines.md`.

## `main` / `integration` / topic-branch model

`main` is append-only and protected: history is never rewritten,
and direct pushes are forbidden. `integration` is a regenerated
fan-in view rebuilt from the active topic branches; it is not a
source of truth and may be reset. Topic branches use
prefix-by-purpose names (`feat/`, `fix/`, `refactor/`, `chore/`,
`docs/`, `bump/`) and carry their workstream's spec, plan, and
code together until the branch lands on `main`.

## `jj` colocated mode

`jj` runs in colocated mode at the parent `geb/` root, not at
`geb-lean/`. A single `jj git init --colocate` step at the
parent populates `geb/.jj/`. `jj` writes
`geb/.jj/.gitignore` containing `/*`, which makes `.jj/` invisible
to git via self-exclusion; the project does not need to add
`.jj/` to the parent `.gitignore`. `git clean -xdf` would delete
`.jj/` and so must not be run on this tree; routine cleanups use
narrower targets.

A new developer onboards with this exact sequence, run from the
parent `geb/` root. Per-repo configuration is set before the
first `jj git fetch --remote origin` so the fetch applies the
`fetch-tags` pattern:

1. `jj git init --colocate`.
2. Per-repo configuration:
   - `jj config set --repo git.private-commits 'conflicts()'`
   - `jj config set --repo remotes.origin.fetch-tags
     'glob:cutover-*'`
3. Per-developer signing and identity (user-level, not
   per-repo):
   - `jj config set --user user.name '<name>'`
   - `jj config set --user user.email '<email>'`
   - `jj config set --user signing.behavior 'own'`
   - `jj config set --user signing.backend 'gpg'` (or `'ssh'`)
   - `jj config set --user signing.key '<key id>'`
4. `jj git fetch --remote origin` to mirror bookmarks into jj's
   view.
5. `bash geb-lean/scripts/check-jj-setup.sh` to verify the
   configuration.

The `remotes.origin.fetch-tags` setting is documented as
experimental in jj 0.41+. If a later jj release removes the
setting, the explicit fallback is to add
`git fetch origin 'refs/tags/cutover-*:refs/tags/cutover-*'`
to the on-boarding sequence in place of step 4's tag-mirroring
behaviour. The repository assumes jj 0.41+.

## Comment and docstring style

Comments and docstrings describe the code as it stands. They
do not narrate the development history, refer to prior states
of the code, or announce work yet to be done; that material
belongs in commit messages, review threads, and the `.session/`
directory. Mathematical context that is not visible from the
code itself is appropriate, and so are pointers to other parts
of the codebase or to literature. The full register rule lives
in `.claude/rules/markdown-writing.md` and applies to comments
in code by reference.

## Markdownlint discipline

Every committed `.md` file passes `markdownlint-cli2` against
`.markdownlint-cli2.jsonc`. The pre-push hook runs the same
check locally before a push completes; CI repeats it. Tables and
fenced code blocks are exempt from the 80-character line limit
via `MD013` configuration; all other prose obeys it. The
authoritative statement is in `.claude/rules/markdown-writing.md`.

## No LLM-drafted user-facing text

Pull request descriptions, GitHub issue and comment threads, and
any other external-facing message are authored by the user.
Claude may produce drafts marked "for paraphrasing"; the posted
text is the user's own writing. This rule preserves the user's
voice in public communication and avoids attributing
hallucinations to the project.

## Generic user references

Committed prose refers to "the user", "they", or "them"; it does
not embed first names, email addresses, or autobiographical
material. Per-developer local state, including user-level `jj
config` for `user.name`, `user.email`, and `signing.*`, lives
outside the repository per jj 0.38+'s config-location model and
is exempt from this rule.

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
applicable but not required. The rule lives in
`.claude/rules/lean-disciplines.md`.

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
`.claude/rules/lean-disciplines.md`.

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
`.claude/rules/lean-disciplines.md`.

## Relationship to geb-mathlib

`geb-mathlib` is a separate repository for content that meets
mathlib's contribution standards (see its specification at
`docs/superpowers/specs/2026-05-04-geb-mathlib-bootstrap-design.md`).
`geb-lean` is the experimentation counterpart: original
research, exploratory category theory, and material that is not
yet upstreamable. `TODO.md` entries marked "to be done in
geb-mathlib" denote material that is intended for the curated
repository once it stabilises here; migration happens by
extracting the stabilised module to `geb-mathlib`, replacing the
local copy with an import, and removing the `TODO.md` entry.
This repository does not adopt a `Mathlib/` versus `Internal/`
split: `geb-mathlib` plays the curated role, so a sub-tree
boundary inside `geb-lean` would duplicate that distinction
without adding information.

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
