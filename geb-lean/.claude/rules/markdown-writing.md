---
paths:
  - "**/*.md"
---

# Markdown writing conventions

Applies to all `.md` files.

## Markdownlint cleanliness

Every Markdown document we author passes `markdownlint-cli2`
against `.markdownlint-cli2.jsonc` (shared with the VSCode
markdownlint extension). If an automated process (such as
Claude Code's `remember` plugin) emits non-compliant output,
fix the offending files locally (or establish another
automated process to do so).

Run `markdownlint-cli2 '**/*.md'` before each commit step that
touches Markdown.

## Tables of contents

Every committed Markdown document with more than one `##`
heading carries an auto-maintained table of contents at the top.
We use `doctoc` (`<!-- START doctoc -->` / `<!-- END doctoc -->`
markers). The pre-push checklist verifies the in-place TOCs are
up to date (`doctoc --dryrun --update-only .`, which exits
non-zero if any existing TOC would change and skips files
without markers); regenerate locally with
`doctoc --update-only .` and re-commit. To add a TOC to a file
that doesn't yet have one, run `doctoc <file>` once to insert the
markers, then commit.

## Link conventions

- Internal links use repo-relative paths
  (`[name](docs/foo.md)`), not absolute or local-machine paths.
- External links use full URLs.
- Dead-link checks are not currently automated; verify manually
  when adding links to external resources.

## Prose style

- Formal, precise, mathematical, dry, unopinionated.
- Avoid value-laden adjectives ("key", "important", "crucial",
  "elegant", "beautiful", "neat", "clever", "powerful",
  "interesting", "insight" used as labels).
- Generic user references ("the user" / "they" / "them"); no
  first names, email, or autobiographical detail.

See `docs/process.md` § Style guidelines for full rationale.

## No nested CLAUDE.md files

The repository has exactly one `CLAUDE.md`, at the repository
root. Per-area instructions live in `.claude/rules/<name>.md`
with a `paths:` frontmatter entry that scopes the rule to the
files it governs. Do not create additional `CLAUDE.md` files in
subdirectories.
