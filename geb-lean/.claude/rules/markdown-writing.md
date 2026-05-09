---
paths:
  - "**/*.md"
---

# Markdown writing rules

These rules apply to every committed Markdown file in the
repository. They restate guidance from `CLAUDE.md` § Style
guidelines so it is colocated with the files it governs.

## Markdownlint cleanliness

Every `.md` file must pass `markdownlint-cli2` against
`.markdownlint-cli2.jsonc`. CI enforces this; the pre-push hook
runs the same check locally before a push completes.

## Prose register

Use a formal, mathematical, dry, unopinionated register suitable
for a published mathematical paper. Refer to "the X-Y theorem",
not "the seminal X-Y theorem". Avoid value-laden adjectives and
authorial enthusiasm. As a non-exhaustive list of words to
rephrase rather than use: fundamental, actually, key, insight,
core, advanced, complex, complicated, simple, advantage, benefit,
important, challenge, yes, wait, hmm, careful, difficult,
blocked, incomplete, future, issue, problem, block. The list in
`CLAUDE.md` is authoritative; this restatement is for ease of
reference.

## No development-history references

Committed prose (specs, plans, README, docs, code comments) does
not refer to prior states of the code, to currently in-progress
work, or to planned future work. Such history belongs in commit
messages and review threads, not in the tree. Comments in code
describe the code as written, not how it came to be written.

## Generic user references

Refer to "the user", "they", or "them". Do not embed first
names, email addresses, or autobiographical details in committed
text. Per-developer local state (for example, user-level `jj
config` for `user.name`, `user.email`, or `signing.*`) is stored
outside the repository per jj 0.38+'s config-location model and
is exempt from this rule.

## No LLM-drafted user-facing text

Pull request descriptions, GitHub issue and comment threads, and
any other external-facing message must be authored by the user.
Claude may produce a draft clearly marked "for paraphrasing";
the posted text is the user's own writing.

## Line length

Wrap lines at 80 characters or fewer. This is stricter than
mathlib's 100-character limit. Enforcement is via
`markdownlint-cli2`'s MD013 rule, configured in
`.markdownlint-cli2.jsonc`. Tables and fenced code blocks are
exempt; the exemption is recorded in `.markdownlint-cli2.jsonc`.

## No emojis

Do not use emoji in committed Markdown. Their omission preserves
the dry register described above.

## Link conventions

Link to other files in the repository by relative path. Place
external links inline at the point of reference rather than
collecting them in a separate references section.

## No nested CLAUDE.md files

The repository has exactly one `CLAUDE.md`, at the repository
root. Per-area instructions live in `.claude/rules/<name>.md`
with a `paths:` frontmatter entry that scopes the rule to the
files it governs. Do not create additional `CLAUDE.md` files in
subdirectories.
