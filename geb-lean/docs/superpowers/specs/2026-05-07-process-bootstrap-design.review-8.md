# Adversarial review cycle 8 — author responses

Review dispatched: fresh-context Agent.

## Blocker

### B1 — `jj git push --tag <tag-name>` is not a valid command in jj 0.40

**Finding.** My cycle-7 response to M1 (signed-tag pushing
mechanism) asserted the command form
`jj git push --remote origin --tag <tag-name>`. The cycle-8
reviewer verified empirically against local jj 0.40.0 (`jj git
push --help`) that `jj git push` has no `--tag` flag and that
`jj git` has no `tag` subcommand. jj 0.40 has no tag-push
capability whatsoever.

This was an **unverified agent claim** — exactly the failure
mode the spec's "verify agent claims against authoritative
sources" rule is designed to catch. I asserted a command that
does not exist.

**Response: fixed (with apology).** Tag pushes go through raw
`git push`. The `block-mutating-git` allowlist gains a
narrowly-scoped `git push` entry for tag pushes. The
on-boarding section is updated to reflect this.

The new allowlist entry:
`git push origin refs/tags/cutover-*:refs/tags/cutover-*`
(parallel to the existing cutover-tag fetch entry; the literal
refspec form is matched by the hook).

If the project later adopts a release-tag naming convention
(e.g. `v*`), an analogous allowlist entry is added at that
time, recorded in the open-questions section.

The non-cutover tag-push case (release tags) remains
human-gated per the project's hard rule: any push under the
allowlisted forms still requires user line-by-line review.
