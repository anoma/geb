# Adversarial review cycle 16 — author responses

Review dispatched: fresh-context Agent over the spec
post-jj-0.41 update. Prior research log:
`design.review-jj-0.41.md`. Reviewer was briefed on the v0.41
release notes, the `remotes.<name>.fetch-tags` config, and
the cycle-15 convergence baseline.

## Serious

### S1 — On-boarding step ordering bug

**Finding.** The on-boarding sequence as written had developers
run `jj git fetch --remote origin` before
`jj config set --repo remotes.origin.fetch-tags 'glob:cutover-*'`,
so the very first fetch missed the tag-fetch configuration and
would have to be re-run after step 5.

**Response: fixed.** Reordered:

1. `jj git init --colocate`
2. `jj config set --repo git.private-commits 'conflicts()'`
   and `jj config set --repo remotes.origin.fetch-tags
   'glob:cutover-*'`
3. Per-developer signing/identity via `jj config set --user`
4. `jj git fetch --remote origin` (now applies fetch-tags)
5. `bash scripts/check-jj-setup.sh`

### S2 — `remotes.<name>.fetch-tags` is marked experimental

**Finding.** The v0.41 docs flag the new
`remotes.<name>.fetch-bookmarks`/`fetch-tags` config as
experimental. The spec presented it without that caveat,
risking silent reliance on a flag that may change shape before
it stabilizes.

**Response: fixed.** Added an experimental-flag note at the
fetch-tags section; documented the fallback path (an explicit
`git fetch origin 'refs/tags/cutover-*:refs/tags/cutover-*'`
if the config is removed or renamed upstream); recorded the
exact docs URL and version where the config is documented in
the empirical-verifications appendix.

## Minor

### M1 — Stale "jj 0.40" reference

**Finding.** Line 1386 still read "jj 0.40 behavior" while the
rest of the empirical-verifications appendix had been
converted to the 0.36–0.41 range.

**Response: fixed.** "0.40" → "0.41" at line 1386. The
appendix-section title now reads "§ jj 0.36–0.41 behavior
checks".

### M2 — `check-jj-setup.sh` does not assert fetch-tags

**Finding.** With on-boarding now setting fetch-tags, the
verification script should assert it the same way it asserts
`git.private-commits`. Without that assertion, a developer
who ran step 4 before step 2 (or skipped step 2 entirely)
would pass the script but silently miss tag fetches.

**Response: fixed.** Extended the script's assertion list:

- (a) `git.private-commits` is set to `conflicts()`
- (b) `remotes.origin.fetch-tags` is set to a glob containing
  `cutover-*` (regex match: `glob:.*cutover-\*`)
- (c) signing.behavior or commit.gpgsign is set to a truthy
  value

Renumbered the existing (b) and (c) accordingly. Verification
item 11 of the master verification list extended in parallel.

### M3 — Truncated docs-quote loses context

**Finding.** The docs quote in the research log read just
*"The value is a string pattern that matches the names of the
bookmarks and tags to fetch."* — the antecedent was missing.
A reader landing on this paragraph cold cannot tell what
"the value" refers to.

**Response: fixed.** Quote expanded to include the
antecedent: *"You can configure which bookmarks and tags to
fetch by default per remote, using the
`remotes.<name>.fetch-bookmarks`/`fetch-tags` config. The
value is a string pattern that matches the names of the
bookmarks and tags to fetch."*

## Cosmetic-taste

### C1 — Vestigial `refs/tags/cutover-*` example

**Finding.** The "Refspec matching semantics" paragraph still
illustrated raw-git refspec form using
`refs/tags/cutover-*:refs/tags/cutover-*`, which is no longer
the canonical example after cycle 12 dropped the
corresponding allowlist entry. A reader could mistake the
example for current guidance.

**Response: fixed.** Replaced the illustrative example with
`refs/heads/feat-*:refs/heads/feat-*`, which is neutral and
does not collide with any allowlisted refspec.

## Lint

One MD013 line-length error appeared at line 1081 after the
fixes (the line had grown to 97 chars while editing). Wrapped
to fit the 80-char limit. `markdownlint-cli2` on the spec
file is now clean.

## Convergence assessment

The cycle-16 fixes are material — both serious findings shift
behavior visible to a developer running on-boarding cold —
and they were applied to the spec after cycle 15 had declared
convergence. Per the spec's own discipline (no fixed cap;
iterate until convergence after material edits), one further
fresh-context cycle is appropriate before resurfacing to the
user.

Cycle 17 to be dispatched against the post-cycle-16 spec.
