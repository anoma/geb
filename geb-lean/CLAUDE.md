# geb-lean

A Lean 4 + mathlib experimental formalisation hub for Geb. See
`README.md` for the project's identity and `docs/process.md`
for the rationale behind each rule below.

## Project status

Active experimentation; the curated counterpart `geb-mathlib`
holds upstream-eligible material. Active development happens on
topic branches; `main` is the append-only public-facing trunk;
`integration` is the regenerated fan-in view of `main` plus
active topic branches.

## Rules

- **No `jj git push` without user line-by-line review.** This includes
  first-creation pushes, force-pushes, branch-deletes, tag-pushes.
- **No direct push to `upstream`.** `upstream` receives commits
  only through merged pull requests opened from `origin`. The
  same human-gate rule applies to `gh` write operations. The
  mechanical denial of direct upstream pushes lives in
  `scripts/hooks/block-mutating-git.sh`; see
  `.claude/rules/fork-upstream-flow.md`.
- **No LLM-drafted text in user-facing channels.** PR
  descriptions, GitHub issue/PR comments are user-authored.
- **No raw mutating `git` subcommands.** The PreToolUse hook at
  `scripts/hooks/block-mutating-git.sh` is an allow-list of read-only
  forms; mutating forms (and unknown forms) trigger a permission
  prompt. Use `jj` for state-mutating operations.
- **One concern per branch.** Refactoring is encouraged; when you
  find code worth refactoring outside the current branch's scope,
  create a separate branch for it rather than bundling it with
  unrelated work.
- **Pre-commit Lean triad.** Before any commit that touches a
  `.lean` file, run `bash scripts/pre-commit.sh` (`lake test` and
  `lake lint`; `lake build` is currently subsumed by `lake test`'s
  dependency graph per `scripts/pre-push.sh`'s rationale). This
  catches lint regressions at commit time rather than push time.
  `scripts/pre-push.sh` remains the full superset (markdownlint,
  doctoc, axiom check, user-driven gates) and is mandatory before
  every push. See `.claude/rules/ci-and-workflow.md` § Pre-commit
  checklist.
- **Generic user references in committed text.** "the user" /
  "they" / "them"; no first names, email, or autobiographical
  detail.
- **No `noncomputable` anywhere; `Classical.choice` accepted in
  proofs.** See Constructive-only Lean code below.
- **Code is cost.** Every committed byte must be justified by a
  return greater than its overhead (reader time, AI context, build
  time, freezing surrounding code in place). Code that meets the
  bar is written in small, reusable chunks so its cost is paid
  once. See `docs/process.md` § Code is cost.
- **Reuse existing process code.** We do not invent build,
  version-control, or CI machinery: anything we need is assumed
  to already exist somewhere. Find code to reuse; if none exists,
  find a concept to reuse. See `docs/process.md` § Code is cost.
- **Reuse existing abstractions.** Before defining a new
  mathematical concept, check whether it already exists in
  mathlib, CSLib, or elsewhere in this repository. Instantiate
  the existing abstraction rather than defining a parallel
  concept. See `docs/process.md` § Code is cost.
- **Avoid the ad-hoc.** Geb is built entirely out of precise,
  universal mathematics. Any data structure should correspond to
  a known formal concept; innovation proceeds in single steps,
  each composed from two concepts already established (in formal
  mathematics or built in Geb by this discipline). See
  `docs/process.md` § Code is cost.
- **Cite the literature when transcribing.** Every definition or
  theorem taken from published mathematics carries a literature
  reference with a searchable identifier in its plan, spec, and
  Lean source. Each workstream's brainstorming-phase spec marks
  each definition as transcription or novel. In `.lean` files,
  citations live in the module docstring's `## References`
  section or inside the declaration's `/-- ... -/` docstring.
- **Document only the persistent.** Comments and committed text
  describe what is enduring about the code as it is — its purpose,
  its contracts, non-obvious external constraints. They do not
  describe transient process artifacts: how the code used to be,
  what testing iteration discovered an issue, which task in our
  plan produced a file, or similar. See `docs/process.md`
  § Document only the persistent.
- `.remember/*.md` must be markdownlint-clean; clean up after each
  `remember`-skill invocation (the plugin emits non-clean markdown).
  Rationale and operational details: see `docs/process.md`
  § Markdownlint discipline.

## Phase-driven workflow

| Phase | Always-on skill | Helper |
| --- | --- | --- |
| Brainstorming | `superpowers:brainstorming` | `sequential-thinking`; Lean helpers as needed |
| Writing-plan | `superpowers:writing-plans` | `sequential-thinking`; Lean helpers as needed |
| Executing-plan | `superpowers:executing-plans` (or `superpowers:subagent-driven-development`) | phase-relevant Lean skills |
| Lean code work | `lean4` umbrella (sub-skills below) | `lean-lsp`, `serena` MCPs |
| Mathlib search | `lean-lsp` (`leansearch`, `loogle`, `local_search`, `hammer_premise`) | — |
| Pre-commit | `superpowers:verification-before-completion` | `scripts/pre-commit.sh` (`.lean`-touching commits) |
| Receiving review | `superpowers:receiving-code-review` | — |

`lean4` sub-skill mapping by activity (drafting, proving, filling
`sorry`, golfing, porting, review, exploration, diagnosis,
checkpointing) lives in `.claude/rules/lean-coding.md` § `lean4`
sub-skill mapping.

Each phase produces an artifact. Specs and plans are
adversarially-reviewed before execution begins (see
`docs/process.md` § Adversarial review). Verify agent claims
against authoritative sources before committing them to artifacts;
include citations.

## Repo structure (one-line)

`GebLean/*` Lean source under root namespace `GebLean`;
`GebLean/Utilities/*` shared helpers; `GebLeanTests/*` `lake test`
targets. Narrow-and-deep dirs with one indexing file per
directory. `main` = append-only stable; `integration` =
regenerated fan-in view; topic branches per PR-candidate.

`geb-lean/` is a subdirectory of the `geb/` monorepo. CI
workflows, the parent `.gitignore`, the colocated `jj` init,
and GitHub Rulesets live at the parent level; code and
per-project content are scoped to `geb-lean/`.

## Style guidelines

Formal, precise, mathematical, dry, unopinionated.
Cite known mathematics where applicable; reference standard
notation. No emojis. No all-caps words unless they are acronyms.
Be wary of value-laden adjectives ("key" / "important" / "core"
/ "elegant" etc.), state-judgment words ("blocked" / "issue" /
"challenge" etc.), and conversational fillers ("yes" / "wait" /
"hmm" / "careful" / "actually"). Avoid markup for emphasis;
save it for delineation (e.g. of book names, links, and words
being defined).  See also `.claude/rules/markdown-writing.md`.

**Avoid colloquialisms and metaphors.** Only standard technical
terms are precise and universal enough for our purposes.
See `docs/process.md` § Avoid colloquialisms and metaphors.

**Style rules apply forward-only.** Pre-existing code that does
not match these rules is not retroactively reformatted; the
rules bind new code, new edits, and code touched in progress on
a branch.

## Mathlib upstream guides

Binding for all `.lean` content and all commit messages:

- Contributing index:
  `https://leanprover-community.github.io/contribute/index.html`
- Commit messages:
  `https://leanprover-community.github.io/contribute/commit.html`
- Coding style:
  `https://leanprover-community.github.io/contribute/style.html`
- Naming conventions:
  `https://leanprover-community.github.io/contribute/naming.html`
- Documentation:
  `https://leanprover-community.github.io/contribute/doc.html`

Bullet-point highlights and adversarial-reviewer instructions
are in `.claude/rules/lean-coding.md`. Re-fetch the guides on
every adversarial-review round; they are subject to upstream
revision.

## Constructive-only Lean code

- No `noncomputable` anywhere. This is the operative constructive
  guarantee: Lean forces `noncomputable` on any definition whose
  body uses `Classical.choice`, and `lake build` (under
  `-DwarningAsError`) rejects it. Every Geb computational object
  therefore executes, and no `Classical.choice` reaches executable
  content.
- `Classical.choice` is accepted in proofs. Mathlib is classical
  from its foundations up — even the primitives this project
  builds on carry it (`Nat.unpair_left_le` / `Nat.unpair_pair`
  underpinning Gödel numbering; `NatTrans.id` / `Functor.comp` via
  `aesop_cat`; `Fin.lastCases_castSucc`) — so forbidding it is
  unachievable while building on mathlib. Because the
  `noncomputable` ban confines all `Classical.choice` to proofs,
  where it has no bearing on computation, accepting it costs the
  project nothing it can actually keep. Ground-up per-axiom
  vetting (including `Classical.choice`) is the job of the
  public-facing `geb-mathlib` port, where the line-by-line rebuild
  makes that discipline tractable from the start.
- `scripts/check-axioms.sh` (vendored from `lean4-skills`) is part
  of the pre-push checklist and runs in CI. It rejects `sorryAx`
  and any non-standard axiom; `propext`, `Quot.sound`, and
  `Classical.choice` are accepted. The lighter pre-commit
  checklist (`scripts/pre-commit.sh`) does not run the axiom
  check; see Rules above.

## `sorry`, `admit`, and underscores

- **`sorry`** is permitted between commits as a stand-in while
  working with skills that need it (e.g.,
  `lean4:sorry-filler-deep`, `lean4:autoprove`). It is never
  permitted in committed code.
- **`admit`** is never permitted, not even between commits.
  Use `sorry` (audited as above) when a placeholder is needed.
- When no skill specifically requires `sorry` and we just need
  a placeholder for an unfilled term or hypothesis, use an
  underscore (`_`). Underscores are considered errors by elaboration,
  highlighting what is missing.

## Specs and plans live on the feature branch

Each feature's spec, plan, and code co-evolve on the same topic
branch. Spec at
`docs/superpowers/specs/<date>-<topic>-design.md`; plan at
`docs/superpowers/plans/<date>-<topic>-plan.md`. Adversarial-review
iterations on spec and plan are commits on the same branch. Merge
to `main` brings spec, plan, and code together.

## Tooling

- VCS: `jj` v0.41+ in colocated mode at the parent `geb/` root;
  lease-protected pushes.
- Build: `lake build`, `lake test`.
- CI: `lean_action_ci.yml` and `markdown-lint.yml` at the parent
  level (the parent monorepo runs CI for `geb-lean/`).
- Linters: `markdownlint-cli2`, `lake lint`,
  `scripts/check-axioms.sh`.
- Skills: `superpowers:*`, `lean4:*`, `claude-md-management:*`,
  `code-review:*`, `pr-review-toolkit:*`, `commit-commands:*`,
  `security-review`; plus `dispatching-parallel-agents`,
  `systematic-debugging`, `test-driven-development`, `remember`,
  `session-report`, `fewer-permission-prompts`,
  `claude-automation-recommender` (one-shot).

## When to consider creating a project-specific skill

If recurring patterns accumulate that don't fit `CLAUDE.md` or
`docs/process.md`, use `skill-creator:skill-creator` to generate a
`geb-development` skill. Default is to wait for friction.

## References

- Process rationale: `docs/process.md`.
- Workstream-by-workstream narrative: `docs/index.md`.
- Mathematical / library references catalog: `docs/lean-resources.md`.
- Rules in `.claude/rules/` (in particular
  `lean-coding.md` for Lean source rules,
  `fork-upstream-flow.md` for fork-upstream invariants,
  `markdown-writing.md` for `.md`,
  `ci-and-workflow.md` for CI / scripts).
