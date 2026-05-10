# Adversarial review cycle 12 — author responses

Review dispatched: fresh-context Agent.

## Serious

### S1 — Tag-push scope contradiction: allowlist entry vs. user-manual framing

**Finding.** Cycle 11's reframe declared cutover-tag signing
and pushing as "user-manual operations performed in the user's
own terminal outside Claude Code" (item 17), but the § Hooks
section still describes a tag-push allowlist entry justified
by "tag pushes go through raw `git push` because jj 0.40 has
no tag-push capability" — implying Claude might push tags. If
push is genuinely user-direct, the allowlist entry and item
12(c) test an unreachable branch.

**Response: fixed (with model resolution).** Pick model (a) —
tag operations are inherently user-direct — and propagate
consistently:

1. **Drop the tag-push allowlist entry** from § Hooks.
2. **Drop smoke-test cases 12(c), (d), (e)** (the
   tag-push positive and negative tests) — there's no
   tag-push allowlist branch to verify.
3. **Add to § Hooks** an explicit note: tag operations
   (creation, signing, listing for verification, push,
   deletion) are user-direct under the hook's scope (per
   item 17 and the human-gate rule). The hook intentionally
   does not allowlist them; if Claude attempted a tag push
   it would be blocked, which is correct: Claude has no
   business pushing signed tags.

The "tag-push allowlist entry" was a misconceived solution
to cycle-7's M1 finding ("no allowed mechanism for pushing
signed tags"), introduced before cycle 11's scope
clarification revealed the right answer (it's not the hook's
job).

The smoke-test set is reduced to the original three cases:
(a) `git commit` returns 2; (b) `jj git push` returns 0;
plus negative tests of two non-tag git mutations
(`git checkout`, `git rebase`) returning 2 to exercise the
default-deny default.

## Minor

### M1 — Canonicalisation paragraph misclassifies subcommand flags as top-level flags

**Finding.** Spec says "for top-level git option flags, the
hook's literal-token rule treats short-form and long-form
equivalents (e.g. `-l` and `--list`, `-d` and `--delete`)..."
The cited examples are *subcommand* flags
(`git tag --list`, `git tag -d`), not top-level git option
flags (which appear before the subcommand, e.g. `git --no-pager`).

**Response: fixed.** Rewrite the canonicalisation paragraph:
"For git flag pairs documented as short-form/long-form
equivalents (e.g. `-l` and `--list`, `-d` and `--delete`,
appearing as either top-level options or subcommand options),
the hook's literal-token rule treats the short and long forms
as the same token after a canonicalisation pass."

### M2 — Item 12(c) test of unreachable branch

**Response: rolled into S1.** With the tag-push allowlist
entry dropped, item 12(c) goes away; nothing further needed.
