# Adversarial review cycle 11 — author responses

Review dispatched: fresh-context Agent.

## Blocker

### B1 — Throwaway-tag remote cleanup forbidden by item 17a

**Finding.** Item 12(c)'s smoke test, as written, pushes a
`cutover-test` tag to the remote and then "removes" it
afterwards. But item 17a configures GitHub branch-protection
to forbid tag deletion. The cleanup cannot succeed; the
`cutover-test` tag would pollute the remote permanently.

**Response: fixed (with a deeper reframe).** The underlying
confusion was in conflating two distinct test surfaces:

1. **The hook script's behaviour given synthetic input** — what
   exit code does the script return for various JSON-stdin
   payloads? This is a unit-test of the hook itself.
2. **End-to-end git/jj operations against the real remote** —
   does a real `jj git push` succeed? A real `git commit` get
   blocked? This is an integration test.

Item 12's smoke tests were drifting toward (2), but for
hook-allowlist correctness only (1) is what matters. The hook
is a single shell script reading JSON on stdin; we can test
it in isolation with synthetic inputs, never invoking git or
touching the remote.

**Reframe**: item 12's smoke tests run the hook script
*directly* with synthesised JSON-stdin payloads representing
the various invocations, asserting the exit code (0 = allow,
2 = block). No real git or jj commands run; no remote
pollution; no need for tag creation, deletion, or cleanup.

This eliminates B1 (no remote cleanup needed since no remote
push happened) and implicitly resolves S1 and M1 (no local tag
creation or deletion needed for the smoke test).

## Serious

### S1 — Creating a local tag isn't allowlisted

**Finding.** `git tag <name>` (creating a local tag) is not on
the closed allowlist; item 17 (production cutover-tag
creation) and item 12(c) (smoke-test setup) both require it.

**Response: fixed (with scope clarification).** The hook is a
PreToolUse hook in Claude Code's settings; it intercepts
**Claude's tool invocations** only. User-direct git operations
in the user's own terminal are out-of-scope and proceed
without hook interference. The project's "no `git push`
without user line-by-line review" hard rule applies as the
human-gate for user-direct operations.

Practical implication for item 17: tag creation
(`git tag -s -m '...' cutover-2026-MM-DD <ref>`) is a
**user-manual operation**, performed by the user in their own
terminal outside Claude Code. The hook does not need to
allowlist it because the hook does not see it.

This scope clarification is added to § Hooks and § CLAUDE.md
hard rules.

For item 12 specifically: smoke tests under the reframe (B1
above) don't invoke real git anyway, so this is moot for the
verification surface.

### S2 — `git tag -l` vs `git tag --list` ambiguity under literal-token matching

**Finding.** Item 17 instructs `git tag -l 'cutover-*'` while
the allowlist has `tag --list`. Literal-token matching makes
the equivalence ambiguous.

**Response: fixed.** Two changes:

1. Item 17 is updated to use the canonical long-form:
   `git tag --list 'cutover-*'`. This matches the allowlist
   verbatim.
2. The "Refspec matching semantics" paragraph in § Hooks gains
   one sentence: *"For top-level git option flags, the hook's
   literal-token rule treats short-form and long-form
   equivalents (`-l` and `--list`, `-d` and `--delete`, etc.)
   as the same token after canonicalisation. This is the
   single exception to strict literal-token matching, justified
   by the canonical equivalence being part of git's own CLI
   contract."*

(Even with the user-direct-out-of-scope clarification from S1,
the `tag --list` form remains useful for Claude to check tag
presence as a read-only operation, e.g. when implementing
`scripts/check-jj-setup.sh` or other internal tooling.)

## Minor

### M1 — Local cleanup `git tag -d` not allowlisted

**Response: fixed (rolled into B1's reframe).** The smoke
test no longer creates a local tag, so no local cleanup is
needed. For real-world local tag deletion (separate from the
spec's smoke tests), this is a user-manual operation outside
the hook's scope, per S1.
