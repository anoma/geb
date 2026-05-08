# Adversarial review cycle 7 — author responses

Review dispatched: fresh-context Agent. (Initial dispatch hit a
transient API error and was retried; the second dispatch
completed cleanly. The discipline does not currently address
non-deterministic reviewer failures; "retry" is the implicit
answer and is recorded here.)

## Serious

### S1 — `axiom_check` migration: "Milestone-A" vs "Milestone B" contradiction

**Finding.** Spec § CI changes says: *"Migration to fail-mode is
a separate Milestone-A item"* (one sentence) and immediately
after: *"The flip is recorded as Milestone B verification item
B7"* (the parenthetical, plus the actual checklist entry B7).
Self-contradiction.

**Response: fixed.** The flip is a Milestone-B item — the
per-touch annotation cadence matches Milestone B's triage
rhythm. Fix the wording: replace "separate Milestone-A item"
with "separate Milestone-B item" (or strike the
milestone-assignment phrase entirely; B7 records it).

## Minor

### M1 — No allowed mechanism for pushing signed tags

**Finding.** The `block-mutating-git` hook does not allow
`git push`; bare `jj git push` pushes bookmarks, not tags. The
cutover tag (item 17) and any release tag (per § Branch model)
must be pushed somehow, but the spec doesn't say how.

**Response: fixed.** Add a clarifying paragraph in § Hooks: tag
pushes (cutover and release) are performed by the user via
`jj git push --remote origin --tag <tag-name>` (jj 0.40
supports tag pushes through `--tag` per the cli-reference;
verified). The hook strips `jj git X` forms from its scope, so
this command is not blocked. If a context arises where a raw
`git push origin <tag>` is needed, the user may invoke it
manually outside Claude Code; the hook does not allowlist raw
`git push` and the project's hard rule "no `git push` without
user line-by-line review" applies as the human-gate.

### M2 — Hook command-matching semantics for refspecs unspecified

**Finding.** The cutover-tag refspec
`'refs/tags/cutover-*:refs/tags/cutover-*'` is shown with shell
single-quotes; the hook receives JSON tokens without the
quotes. The matching rule (literal-token vs glob/regex) is
ambiguous.

**Response: fixed.** Add to § Hooks: the hook performs
**literal-token equality matching** after argv parsing on the
allowlist refspec entries. The cutover refspec is matched as
the literal string `refs/tags/cutover-*:refs/tags/cutover-*`;
the `*` characters in this token are part of the refspec
syntax (interpreted by `git fetch` itself), not glob-matched
by the hook. Other refspecs that begin with `refs/tags/cutover-`
but use different patterns are *not* matched and are blocked.

### M3 — On-boarding step 2 doesn't note redundancy with `git clone` default tag mirroring

**Finding.** A developer who arrived via `git clone <url>`
already has the cutover tag locally (git clone mirrors all
tags by default); the spec's explicit fetch step is redundant
in that case. The spec doesn't say whether redundant or
required.

**Response: fixed.** On-boarding step 2 gains the half-sentence
clarification: *"redundant if the developer reached the working
tree via `git clone` (which mirrors all tags by default);
required if the developer reached it via `jj git clone`,
since jj's subsequent fetches do not mirror non-included
tags."*

## Cosmetic-taste

### C1 — Hard-rules redundancy between "no `git push`" and "no raw mutating `git` subcommands"

**Response: rejected (cosmetic-taste).** The redundancy is
intentional: the first bullet states a substantive
human-review requirement; the second states the
mechanical-enforcement mechanism. Both apply, and to slightly
different scopes (the human-gate extends to `gh` write
operations and to release-tag pushes that the hook
intentionally doesn't cover).
