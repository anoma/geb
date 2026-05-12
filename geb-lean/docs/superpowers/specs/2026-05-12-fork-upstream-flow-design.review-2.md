# Adversarial review of fork-upstream flow spec (round 2)

## Scope

Round 2 reviews only the `gh repo set-default` additions
introduced after round 1. Out-of-scope passages were not
re-examined.

## Summary

Eight defects identified: one factual inaccuracy, one internal
inconsistency, four missing cases, and two under-specifications
or ambiguities. The additions broadly track `gh` CLI behaviour;
the defects concentrate on ordering of onboarding steps, on the
load-bearing-but-untested claim that Op 1's command defaults to
a fork-internal PR, and on framing of the new pre-spec
bullet.

## Defects

### 1. Onboarding ordering not specified

**Where**: spec lines 402–408 (§ Per-clone `gh` configuration)
and lines 448–453 (§ Documentation changes,
`docs/process.md` bullet).

**Defect**: `gh repo set-default rokopt/geb` succeeds only
when the working copy has a `git` remote whose URL resolves
to the named repository. `docs/process.md` § jj colocated
mode (lines 115–135) does not currently include a step
that adds the `origin` git remote (it begins at
`jj git init --colocate`, then jumps to per-repo `jj config`
and `jj git fetch --remote origin`). The spec adds
`gh repo set-default rokopt/geb` as a new onboarding step
but does not state where in the sequence it lands, nor does
it require that the `origin` remote be present and pointing
at `rokopt/geb` first. A new developer running the steps in
order would hit a `gh` failure or an interactive prompt.

**Suggested fix**: pin the step's position (after the
`origin` remote URL is in place and after the first
`jj git fetch --remote origin`) and state the prerequisite
explicitly.

### 2. Pre-spec bullet's narrowing claim is wrong

**Where**: spec lines 32–34 and lines 78–84
(§ State at spec time).

**Defect**: The § State at spec time preamble says items
prefixed "Pre-spec" describe behaviour "that the spec's Hook
and configuration changes section narrows." The new Pre-spec
bullet at lines 78–84 closes with "§ Per-clone `gh`
configuration installs a workaround", but § Per-clone `gh`
configuration explicitly states (lines 428–432) that the
setting "does not affect the 'Create a pull request' URL
that GitHub prints in its push response … that link
continues to default to upstream." The configuration does
not narrow or modify the push-response URL; it replaces the
operator's command path. Either the preamble's "narrows"
contract is violated, or the bullet's "installs a
workaround" claim is mismatched with what § Per-clone
in fact does.

**Suggested fix**: rephrase the bullet to say that
§ Per-clone `gh` configuration introduces an alternative
PR-creation path that the operator uses instead of the
printed URL, rather than that it narrows or works around the
GitHub-side URL.

### 3. T10 does not verify the load-bearing Op 1 claim

**Where**: spec lines 168–170 (Op 1) and lines 579–589 (T10).

**Defect**: Op 1's documentation asserts that, with
`gh repo set-default rokopt/geb` configured,
`gh pr create --base main --head <branch>` "defaults to a
fork-internal PR against `origin/main`." T10 only checks
that `gh repo set-default --view` prints `rokopt/geb`. It
does not exercise the inferred consequence on
`gh pr create`'s target. Since `gh pr create` is excluded
from the acceptance test by the "destructive subset"
carve-out at lines 591–594, the spec contains no mechanical
verification that the configuration produces the documented
Op 1 behaviour.

**Suggested fix**: add a dry-run-style probe (for example,
`gh pr create --dry-run --base main --head HEAD` against a
throwaway branch or an existing topic branch, asserting that
the printed target is `rokopt/geb`) or note explicitly that
the Op 1 default-target claim is unverified by the
acceptance suite.

### 4. T10 expected-output match is under-specified

**Where**: spec lines 581–589 (T10).

**Defect**: T10's expected output is `rokopt/geb`, but the
test does not specify the matching mode (substring, exact
line, exit-code-plus-stdout), does not show what
`gh repo set-default --view` emits on stdout when a default
is set (the CLI prints `rokopt/geb` followed by a newline;
no other formatting), and does not specify the exit code.
The prose says "If empty, … is the corrective", implying
that empty stdout is the unset case; verified behaviour is
that `--view` exits 0 with empty stdout when
unset, which T10 does not record. A reader cannot tell from
T10 alone what `--view` outputs on `BASE` matches versus
`HEAD/BASE` configurations or what to expect on multiple
defaults.

**Suggested fix**: specify exit code 0 and exact stdout
`rokopt/geb\n`, and note that empty stdout indicates the
unset state.

### 5. Stored config entry wording diverges from git surface

**Where**: spec lines 410–411 (§ Per-clone `gh`
configuration).

**Defect**: The spec says `gh repo set-default rokopt/geb`
"writes `gh-resolved = base` into `.git/config` for the
`origin` remote." The full git config name is
`remote.origin.gh-resolved`, with literal value `base`.
Someone grepping `.git/config` or `git config` output for
`gh-resolved` (without the `remote.origin.` prefix) may
find it, but a reader who treats the spec's wording as a
literal `[gh-resolved]` section or a top-level entry will
be misled. Additionally, the value `base` is the gh CLI's
sentinel meaning "use the resolved repo of the named remote
URL"; the spec does not explain that this is why a later
change to the `origin` URL would silently retarget `gh`.

**Suggested fix**: name the entry as
`remote.origin.gh-resolved` and explain the `base` sentinel
in one sentence.

### 6. Stale `gh-resolved` if `origin` URL is rewritten

**Where**: spec lines 418–420 (§ Per-clone `gh`
configuration, "Properties to note").

**Defect**: The properties list does not record that
`remote.origin.gh-resolved = base` resolves through the
`origin` remote URL at command time. If a later operation
rewrites `origin`'s URL (for example,
`git remote set-url origin <other-fork>`), `gh` will
silently retarget every default-base command to the new URL
without `gh-resolved` being touched. The spec offers no
probe or invariant for this case.

**Suggested fix**: add a property noting that
`gh-resolved = base` follows the live `origin` URL, and a
corresponding gate (operator-level reminder or T10 sibling
test) that the `origin` URL still points at `rokopt/geb`.

### 7. Multi-account `gh auth` interaction unaddressed

**Where**: spec lines 410–432 (§ Per-clone `gh`
configuration).

**Defect**: `gh-resolved` selects the target repository for
`gh` commands, but capability against that target depends
on the active `gh auth` account. The spec does not state
which authenticated account is assumed, nor what happens
when the user runs `gh auth switch` and the new account
lacks access to `rokopt/geb`. T8 partially addresses the
upstream side (Op 4 / Op 5 permissions probe) but the
fork-default path has no equivalent.

**Suggested fix**: state the assumed `gh auth` account in
the onboarding section, or add a single-line property that
the active `gh` account must have write access to
`rokopt/geb` for Op 1's PR-creation command to succeed.

### 8. Overbroad "redirects every `gh` command" claim

**Where**: spec lines 420–421 (§ Per-clone `gh`
configuration, second bullet of "Properties to note").

**Defect**: The bullet states "It redirects every `gh`
command in this clone, not only `gh pr create`." Commands
that do not consult the default base repository (for
example, `gh auth status`, `gh config`, `gh api` with an
explicit path, `gh repo view <owner>/<repo>` with an
explicit argument) are unaffected by `gh-resolved`. The
"every" wording overstates the scope.

**Suggested fix**: replace "every `gh` command" with "every
`gh` subcommand that resolves a default base repository"
or list the affected families (`pr`, `issue`, `release`,
`workflow`, `secret`) explicitly.

## Confirmed-correct claims (sample)

- `gh repo set-default --view` exits 0 with `rokopt/geb`
  when set and exits 0 with empty stdout when unset:
  verified by direct invocation.
- `gh repo set-default --unset` is the documented reversal:
  verified via `gh repo set-default --help`.
- The fork-parent linkage `rokopt/geb` →
  `parent.full_name = "anoma/geb"` holds: verified via
  `gh api repos/rokopt/geb --jq '.parent.full_name'`.
- `origin` URL is `ssh://git@github.com/rokopt/geb`,
  matching the `rokopt/geb` argument to `gh repo
  set-default`: verified via `git remote -v`.
- `gh repo set-default` stores its result in `.git/config`
  rather than the user-level `gh` config: verified via
  `gh repo set-default --help` and the help's prose about
  "the locally cloned repository."
- The `--repo anoma/geb` override path documented for Op 4
  is the correct way to bypass the configured default for a
  cross-repository `gh pr create`: matches `gh` CLI
  semantics.
- In-scope passages contain no MD013 line-length violations
  against the 80-character limit configured in
  `.markdownlint-cli2.jsonc`: verified by per-line scan.
