# Adversarial review — cycle 7

**Spec**: `2026-05-09-process-bootstrap-monorepo-design.md`
**Date**: 2026-05-09
**Reviewer**: fresh-context agent

---

## Summary

Findings: **0 blockers / 1 serious / 2 minor / 0 cosmetic-taste**.

---

## Findings

### S-1 — Serious: `check-axioms.sh` capture mechanism uses wrong action

**Section**: § CI changes, paragraph on `--exit-zero-on-findings`
(around line 1159–1163).

The spec says the script's stdout is captured via
`actions/upload-artifact@<SHA>` so the report is available for review.
`actions/upload-artifact` captures files by path, not by capturing a
command's stdout inline. To capture a script's stdout into an artefact
the CI step must first redirect the output to a file
(e.g. `bash scripts/check-axioms.sh ... > axiom-report.txt`) and then
a separate `uses: actions/upload-artifact` step uploads that file. The
spec does not show the redirection, does not name the intermediate file,
and does not show the upload step's `with.path` input. As written, the
claim that stdout is "captured via `actions/upload-artifact`" is
incoherent: `actions/upload-artifact` has no mechanism to intercept
a prior step's stdout directly.

The resulting workflow would either silently discard the report or
require an undocumented intermediate step. The plan will need to add
the redirection + filename and the upload step's `with.path` value.

---

### M-1 — Minor: `.markdownlint-cli2.jsonc` ignores do not cover `tools/`

**Section**: § `.markdownlint-cli2.jsonc` (around line 1239–1266).

The ignore list covers `.claude/memory/**` and `.claude/docs/**` but
not `.claude/tools/**`. The directory layout in § New file and
directory layout (line 253) lists `geb-lean/.claude/tools/` as
`(existing; unchanged)`. If `tools/` contains any `.md` files,
they are scanned by both invocation contexts (pre-push and CI)
without being ignored. The parallel `geb-lean/.claude/tools/**` and
`.claude/tools/**` entries are absent from both the unprefixed
and `geb-lean/`-prefixed halves of the ignore list. The spec should
either add those entries or explicitly state that `tools/` contains no
markdown files that need to be excluded.

---

### M-2 — Minor: `check-signing-key.sh` signing-backend dispatch is underspecified

**Section**: § Hooks, `check-signing-key.sh` description
(around lines 1764–1784).

Step 3 says "dispatch on the configured backend (`gpg`, `ssh`, etc.)
and warm the appropriate agent." The `gpg` case is fully specified:
query `gpg-connect-agent`, then `echo warm | gpg --clearsign >/dev/null`.
The `ssh` case is named only as "etc." — no equivalent `ssh-add -l`
presence check, no `ssh-add` invocation or agent-wake path is given.
The spec states "This repository signs commits with gpg, so the hook is
expected to warm gpg-agent on every session," which implies the `ssh`
path is dead code in the current configuration. Nevertheless the
`jj config set --user signing.backend 'ssh'` option is offered to
new developers (on-boarding step 3, line 1446), making the `ssh` branch
reachable. The omission means an `ssh`-signing developer would get a
hook that does nothing useful for their backend. Either the `ssh` path
should be specified or the on-boarding instructions should be narrowed
to `gpg` only (matching the repository's actual practice), with a
forward-deferred note for `ssh` support.

---

## Items confirmed resolved since prior cycles

The following categories of finding that appeared in earlier cycles
were not re-found in this reading:

- `.jj/` self-exclusion mechanism and git-ignored status: fully
  specified with `geb/.jj/.gitignore` containing `/*`.
- `jj root` portability for hook discovery: correctly specified.
- `defaults.run.working-directory` scope: correctly documented as
  workflow-level, with `uses:` step exemption noted.
- `lake-package-directory` input: present and attributed.
- Doubled `.markdownlint-cli2.jsonc` ignore patterns: the
  unprefixed + `geb-lean/`-prefixed scheme is fully described.
- `git.private-commits` semantics and exemption conditions: fully
  specified.
- `fetch-tags` experimental status: acknowledged and documented.
- `block-mutating-git.sh` `jj root` vs directory-check: the
  C-hook-amend cleanup task addresses this.
- Licence coherence: GPLv3 at `../LICENSE`; no `geb-lean/LICENSE`;
  Apache 2.0 vendored content preserves upstream notices; the
  in-flight A5 `geb-lean/LICENSE` (Apache 2.0) is removed by
  C-license-rm.
- Verification matrix items: each has a concrete artefact and a
  passing condition. Item numbering is internally consistent
  (1–17, 17a, B1–B7).
- `--no-globs` flag usage in pre-push and CI: both invocation
  contexts use it.
- Cleanup tasks: each has a name, body, and ordering constraint.
- `C-hook-amend` smoke-test cases: five cases listed with JSON-stdin
  payloads and expected exits.
