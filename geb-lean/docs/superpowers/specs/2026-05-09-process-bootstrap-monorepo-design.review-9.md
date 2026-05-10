# Adversarial Review — Cycle 9

**Spec**: `2026-05-09-process-bootstrap-monorepo-design.md`
**Reviewer**: fresh-context agent, no access to prior review logs
**Date**: 2026-05-09

---

## Finding counts

- Blockers: 0
- Serious: 1
- Minor: 4
- Cosmetic-taste: 0

---

## Findings

### S-1 — Serious: `--no-globs` glob quoting underdefined

In § .claude/rules/ci-and-workflow.md (item 2) and in
§ Auxiliary scripts, the pre-push invocation is:

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  --no-globs '**/*.md'
```

The shell glob `'**/*.md'` is single-quoted here, which
prevents shell expansion and passes the literal token to
`markdownlint-cli2`. That is the intended behaviour. However,
the spec does not state this quoting requirement anywhere as
a rule or note. In `scripts/pre-push.sh` the quoting will be
in the script body, where it is visible; but
`ci-and-workflow.md` (which humans read as a rule file) shows
the invocation as prose, and the quoting convention is not
explained. If someone copies the invocation without the
single quotes — which is the natural mistake when using the
invocation interactively — the shell will expand `**/*.md`
before `markdownlint-cli2` sees it, defeating `--no-globs`.
The spec should note that the single quotes are load-bearing
(prevent shell glob-expansion) wherever this invocation is
written as a rule or reference.

### M-1 — Minor: `--no-globs` flag introduced in markdownlint-cli2 v3

The spec uses `markdownlint-cli2 --no-globs` as a
load-bearing mechanism (§ .markdownlint-cli2.jsonc, §
Auxiliary scripts). The `--no-globs` flag was introduced in
markdownlint-cli2 v3.0.0. The spec records no minimum version
requirement for `markdownlint-cli2`, either in the install
step in `markdown-lint.yml` (`npm install -g
markdownlint-cli2` pins no version) or in on-boarding
documentation. If a developer or the CI runner gets an older
version, `--no-globs` is silently unrecognised or causes an
error. The spec should state a minimum version (≥ 3.0.0) and
pin it in the `npm install` step (e.g. `npm install -g
markdownlint-cli2@3`).

### M-2 — Minor: `check-signing-key.sh` ssh path gap not acknowledged

In § Hooks, for the ssh signing case, the spec says: "if no
keys are loaded, defer to the developer's local agent setup
(the hook does not seed ssh-agent autonomously since key
discovery is non-portable across ssh-signing
configurations)." No exit condition or minimum check is
specified for the case where `ssh-add -l` succeeds but the
listed key is not the configured `signing.key`. The hook as
described would exit 0 even if the loaded keys do not include
the developer's signing key, giving a false sense of
readiness. This is acknowledged in the Open questions section
only implicitly (the signing-key path is not mentioned
there). The spec should either explicitly acknowledge this
gap as a known limitation with a deferred-decision note, or
tighten the check to compare `ssh-add -l` output against
`jj config get signing.key`.

### M-3 — Minor: `check-jj-setup.sh` signing check is too coarse

In § jj setup (the `check-jj-setup.sh` description), check
(c) is: "at least one of `jj config get signing.behavior` or
`git config --get commit.gpgsign` indicates signing is
active." `jj config get signing.behavior` returns `own`,
`force`, `drop`, or `disabled`. The spec treats a non-zero
exit code (key absent) as "not active" and a returned value
of `own` or `force` as "active". However, `jj config get
signing.behavior` may return `own` even when `signing.key`
is not set (the key field may be absent or empty), which
means the check reports "signing active" when it is actually
misconfigured. The spec does not instruct the script to
verify `signing.key` is populated when `signing.behavior`
indicates signing. This leaves a gap in the on-boarding
verifier: a developer can pass `check-jj-setup.sh` with a
signing behaviour set but no key configured.

### M-4 — Minor: `upload-artifact` path depends on unstated invariant

In § CI changes, the upload step:

```yaml
path: geb-lean/axiom-check-report.txt
```

The spec reasons: "`defaults.run.working-directory: geb-lean`
applies to the `run:` step, so `tee axiom-check-report.txt`
writes to `geb-lean/axiom-check-report.txt` relative to the
checkout root." This reasoning is correct only if
`actions/checkout` checks out to `$GITHUB_WORKSPACE` (the
repo root) and `defaults.run.working-directory: geb-lean`
offsets from there. That is standard behaviour when no
`path:` is given to `actions/checkout`. However, if a future
plan edit adds `with: path: ...` to the checkout step, the
`tee` destination and the upload path would desync silently.
The spec should note this dependency explicitly (the upload
path's correctness depends on `actions/checkout` using the
default `$GITHUB_WORKSPACE` destination with no `path:`
override), so a future editor knows the invariant to
preserve.

---

## Summary

One serious finding (S-1): the quoting requirement for
`--no-globs '**/*.md'` is load-bearing but unexplained,
creating a copy-paste failure mode in the rule files and
on-boarding documentation.

Four minor findings (M-1 through M-4): no minimum version
pinned for `markdownlint-cli2`; the ssh signing path in
`check-signing-key.sh` does not verify that the loaded key
matches `signing.key`; `check-jj-setup.sh`'s signing check
does not verify `signing.key` is populated; the
`upload-artifact` path correctness depends on an unstated
invariant about `actions/checkout`.

No blockers. No cosmetic-taste findings.
