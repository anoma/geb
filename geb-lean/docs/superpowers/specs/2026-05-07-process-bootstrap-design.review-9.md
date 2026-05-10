# Adversarial review cycle 9 — author responses

Review dispatched: fresh-context Agent.

## Serious

### S1 — Required cutover-tag push command form is undocumented; only the wildcard refspec form survives the allowlist

**Finding.** The literal-token matching for the allowlisted
`git push origin refs/tags/cutover-*:refs/tags/cutover-*`
entry means the user/Claude must invoke `git push` with the
*wildcard* refspec form even for a single specific tag. The
natural forms (`git push origin <tag-name>`,
`git push origin tag <tag-name>`,
`git push origin refs/tags/<specific-name>:refs/tags/<specific-name>`)
are all blocked by the closed allowlist. Item 17 says only "a
signed git tag pushed to the remote"; it doesn't document the
required form. Additionally, the wildcard form pushes every
local `cutover-*` tag — including any from botched earlier
attempts.

**Response: fixed.** Two changes:

1. Item 17 is amended to specify the exact command:
   *"...the cutover commit is recorded as a signed git tag
   (e.g. `cutover-2026-MM-DD`) pushed to the remote via
   `git push origin 'refs/tags/cutover-*:refs/tags/cutover-*'`
   (the wildcard form is mandated by the
   `block-mutating-git` hook's allowlist; see § Hooks).
   Before pushing, verify that the only `cutover-*` tag in the
   local repo is the intended one (`git tag -l 'cutover-*'`
   should print exactly one line); otherwise resolve any
   stray tags first to avoid pushing unintended history."*
2. The "Refspec matching semantics" paragraph in § Hooks gains
   the note: *"Pushers must use the wildcard form even for a
   single specific tag; the natural specific-name forms are
   blocked. Pre-push verification of the local
   `git tag -l 'cutover-*'` listing is the user's
   responsibility (called out in Milestone A item 17)."*

The alternative (broaden the allowlist with non-trivial
parser logic to recognise `git push origin <tag>` where
`<tag>` matches `cutover-*`) is rejected as more complex than
the user-side discipline of pre-push verification.

## Minor

### M1 — Quoting inconsistency between fetch and push allowlist entries

**Finding.** The fetch entry is shown single-quoted; the push
entry is shown unquoted. The literal-token matching makes them
equivalent after argv parsing, but the inconsistent
presentation invites implementation confusion.

**Response: fixed.** Single-quote both entries for consistency
(real shell invocations need to quote the `*` character
anyway). The push entry becomes
`git push origin 'refs/tags/cutover-*:refs/tags/cutover-*'`.

### M2 — Tag-push allowlist entry not exercised by Milestone A smoke tests

**Finding.** Verification item 12 smoke-tests `git commit`
(blocked) and `jj git push` (allowed) but does not exercise
the new tag-push allowlist branch. A hook regression would go
undetected until item 17's one-shot tag-push attempt.

**Response: fixed.** Verification item 12 is amended to
include positive and negative smoke tests for the tag-push
form: (a) `git push origin
'refs/tags/cutover-test:refs/tags/cutover-test'` against a
throwaway local `cutover-test` tag succeeds; (b)
`git push origin 'refs/tags/v1.0.0:refs/tags/v1.0.0'` (a
non-`cutover-*` tag-push form) is blocked.
