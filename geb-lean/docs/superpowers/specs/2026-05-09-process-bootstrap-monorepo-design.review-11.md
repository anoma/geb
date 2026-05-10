# Adversarial review — cycle 11

**Spec**: `2026-05-09-process-bootstrap-monorepo-design.md`\
**Date**: 2026-05-09\
**Reviewer**: fresh-context agent

## Status

No blockers. No serious findings. One minor finding. No cosmetic findings
worth reporting.

**Finding counts**: B 0 / S 0 / M 1 / cosmetic 0

## Finding

### M-1 — Minor: path-scoped rule load trigger described with wrong mechanism

**Location**: § `.claude/rules/lean-coding.md`, first paragraph:
"Loaded automatically when Claude reads a `.lean` file (per
`https://code.claude.com/docs/en/memory`: path-scoped rules
trigger on Read tool calls matching the pattern)."

**Finding**: The Anthropic memory documentation (verified at
`https://code.claude.com/docs/en/memory`) says:
"Path-scoped rules trigger when Claude reads files matching the
pattern, not on every tool use."
It does **not** say "Read tool calls". The trigger is described
as file-reading in general, not as specifically the `Read`
built-in tool. This distinction matters for implementation
expectations: if a future client surfaces path-scoped rules on
any file-reading operation (not just the `Read` tool), the
spec's "Read tool calls" language would mislead an implementer
auditing which operations trigger rule loads. The citation is
also incorrect: the docs do not use the phrase "trigger on
Read tool calls matching the pattern" — that phrasing was
introduced by the spec itself.

**Consequence**: an implementer or auditor reading the spec who
expects rule loads to be strictly tied to the `Read` built-in
tool would have an incorrect mental model of the trigger
boundary. Not a blocker because the observable behaviour in
practice is the same (Claude reading a `.lean` file via `Read`
is the dominant case), but the claim misstates what the cited
source actually says.

**Suggested fix**: replace "trigger on Read tool calls matching
the pattern" with "trigger when Claude reads a file matching the
pattern (per the Anthropic documentation)".

## Overall assessment

The spec is substantially converged. All prior findings have
been addressed. M-1 is a single citation-accuracy issue with no
implementation-correctness consequence in normal use. If the
author accepts the fix, the spec is ready for user review.
