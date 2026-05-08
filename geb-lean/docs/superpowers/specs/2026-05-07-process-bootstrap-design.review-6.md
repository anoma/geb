# Adversarial review cycle 6 — author responses

Review dispatched: fresh-context Agent reading only the spec.

## Serious

### S1 — Bootstrap paradox: cutover-tag check in `check-jj-setup.sh`

**Finding.** The (c) check in `scripts/check-jj-setup.sh`
(`git tag -l 'cutover-*'` non-empty) cannot pass during the
refactor's own development phase, since the cutover tag is
created only when the merge commit on `main` lands (Milestone A
item 17). `pre-push.sh` invokes `check-jj-setup.sh` at the top of
its sequence, so the very push that lands the refactor would be
gated by a check requiring the artefact that push creates.
Milestone A item 14 also fails ("script returns zero after
on-boarding completes") since on-boarding completes before item
17 lands.

**Response: fixed.** The (c) check is **removed** from
`check-jj-setup.sh`. The cutover tag's integrity is protected by
GitHub branch-protection rules (Milestone A item 17a: no tag
deletion); the on-boarding sequence's tag-fetch step (step 2)
ensures developers cloning *after* cutover have the tag locally;
but `check-jj-setup.sh` does not gate on the tag's local
presence. Pre-cutover the script would fail vacuously; post-
cutover the tag is mirrored by `jj git fetch` per the resolved
hedge below (S2). The simpler design is cleaner: `check-jj-setup.sh`
verifies (a) `git.private-commits` is set per-repo and (b)
signing is configured per-user; the cutover tag is verified by
item 17 directly, not by re-checking via the script.

### M1 (now S2) — On-boarding tag-fetch hedge resolvable from primary docs

**Finding.** Per
<https://docs.jj-vcs.dev/latest/cli-reference/> (`jj git clone`
section): *"Unless otherwise specified, the initial clone will
fetch all tags, while all subsequent fetches will only fetch
included tags."* The on-boarding sequence uses `jj git init
--colocate` + `jj git fetch` (not `jj git clone`), so the
"initial-clone tag fetch" does not apply. Tags are fetched only
if "included" — which for an arbitrary cutover tag they will not
be. The spec's "verify empirically" hedge is unnecessary; the
docs settle the question.

**Response: fixed.** Resolve the hedge: on-boarding uses an
explicit refspec form to fetch the cutover tag. Add the form
`git fetch origin 'refs/tags/cutover-*:refs/tags/cutover-*'` to
the `block-mutating-git` `git fetch` allowlist with documented
rationale ("explicitly fetches the project's cutover tags from
origin into the local refs/tags/ namespace; needed because
`jj git fetch` does not mirror non-included tags").

The on-boarding step 2 is rewritten to issue this explicit
form. The allowlist is updated. The empirical-verification
hedge is removed.
