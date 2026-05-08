# Adversarial review cycle 4 — author responses

Review dispatched: fresh-context Agent reading only the spec.
Cycle 4 returned 0 blockers, 8 serious, 11 minor, 4 cosmetic.

## Serious

### S1 — `private-commits` push-time semantics not in primary docs

**Response: fixed.** The spec's claim is hedged: rather than
asserting jj evaluates the revset at push time, the spec now
states the *behaviour we want and the implementation plan
verifies* — namely, that resolving a conflict locally and then
pushing succeeds without `--allow-private`. The plan's smoke
test exercises exactly this flow (manufacture a conflict; resolve
it; `jj git push`); if the behaviour differs from expectation,
the plan adjusts the rule wording. Spec text now says: "The
behaviour we expect — and verify in the plan — is that resolving
a conflict locally and then pushing succeeds, since the
offending commit is no longer in `conflicts()` at push time. If
empirical verification shows otherwise, the rule is amended."

### S2 — `revsets.string-pattern` config option does not exist

**Response: fixed.** Drop the cited mechanism. Keep defensive
`glob:` prefix with revised rationale: "jj is pre-1.0; revset
string-pattern semantics may change in future versions. Explicit
`glob:` is robust against silent default changes."

### S3 — `lake test` → `lake build` implication is fragile

**Response: fixed.** Rephrase: `pre-push.sh` runs `lake test`,
which builds the `GebLean` and `GebLeanTests` libraries (which
are the inputs to `scripts/check-axioms.sh`). If a future
lakefile addition introduces a target outside the test driver's
dependency graph, the pre-push script must be amended to add
`lake build` explicitly. Until then, `lake build` is implied by
`lake test`.

### S4 — `block-mutating-git` allowlist is not closed (default-deny)

**Response: fixed.** Redesign the hook policy as **default-deny**
with closed allowlists. The spec is rewritten to:

1. Allow only the explicitly enumerated read-only subcommands.
2. Allow only the explicitly enumerated `git fetch` forms.
3. Allow `clone` only when the target argument resolves to a
   directory not containing `$PWD`.
4. Block everything else, including unrecognised subcommands and
   user-defined aliases. The translation message in stderr says:
   "this `git` invocation is not on the allowlist; if it has a
   `jj` equivalent, use that; if it should be allowlisted, propose
   the addition in a refactor plan."

For `git config`: only `git config --get`, `git config --list`,
and `git config --get-all` are allowed; `git config <key>
<value>` (any setter form) is blocked.

### S5 — Verification "item 18" referenced but doesn't exist

**Response: fixed.** The promised item is added: Milestone B item
B7 ("`axiom_check` job has been flipped from report-only mode to
fail-mode; report-only mode has been retired"). The flip
naturally lands at Milestone B because it depends on every
existing flagged declaration having an `AXIOM_ALLOW` annotation
or no axiom dependency outside the reduced allowlist — same
per-touch cadence as triage. The spec's reference at
`axiom_check` description is updated to point at item B7
instead of the non-existent "item 18."

### S6 — AXIOM_ALLOW comment vs `/-- ... -/` docstring layout unspecified

**Response: fixed.** Specify the canonical layout: AXIOM_ALLOW
comment lines are placed *before* the docstring (if any), with
no blank line between them or between the docstring and the
declaration. The script scans up through `--` comment lines and
through any preceding `/-- ... -/` docstring to find AXIOM_ALLOW
attributions for the declaration. Example:

```lean
-- AXIOM_ALLOW: Classical.choice (transitive via
--   Mathlib.CategoryTheory.Equivalence)
/-- The `foo` theorem says ... -/
theorem foo : … := …
```

### S7 — `gh` CLI commands are not addressed by `block-mutating-git`

**Response: fixed.** Add an explicit policy in the hook spec and
in `CLAUDE.md`'s hard-rules section: `gh` CLI write operations
(`gh pr create`, `gh pr merge`, `gh pr close`, `gh release
create`, `gh issue create`, `gh issue close`, etc.) are
**outside the hook's scope** because they bypass local `git`
mutation, but the project's hard rule "no push or external
write without user line-by-line review" applies symmetrically.
The hook does not block `gh`; the human-gate rule does. The
hook's stderr translation message points the user at the
`gh`-policy paragraph in `CLAUDE.md`.

### S8 — Cutover-SHA primary record clarification

**Response: fixed.** Clarify that the primary record of the
cutover SHA is the **signed git tag** (e.g. `cutover-2026-MM-DD`)
pushed to the remote and protected from deletion by the branch-
protection rules. `docs/process.md` § Branch model carries the
same SHA as a navigation aid only; the tag is authoritative.
This is restated in verification item 17 and item 17a.

## Minor (consolidated edits)

### M1 — `.jj/.gitignore` jj-version note

**Response: fixed.** Empirical-verifications appendix gains
"verified against jj 0.40 specifically; if the hint text changes
in a later jj release, `docs/process.md` § jj is updated
accordingly."

### M2 — Line-budget table 50-line spacing allowance unaudited

**Response: rejected (cosmetic-taste).** The 50-line allowance is
explicitly conservative; verification item 5 catches any overrun
mechanically. The budget table's purpose is feasibility evidence,
not a contract.

### M3 — `check-signing-key.sh` gpg cache-check fragile

**Response: fixed.** Replace the brittle `grep -q ' 1 '` check
with the always-warm fallback: invoke `echo warm | gpg
--clearsign >/dev/null` unconditionally if signing is enabled.
The command is idempotent if the agent is already cached and
prompts pinentry only on the first invocation.

### M4 — `docs/process.md` sections authoritative-vs-summary unmarked

**Response: fixed.** Each section in the
`docs/process.md` index gains a tag: `[authoritative]` for
sections whose canonical text is in `docs/process.md` itself, or
`[index — full text in <path>]` for sections that summarise
content canonical elsewhere.

### M5 — `.markdownlint-cli2.jsonc` iteration is circular

**Response: fixed.** The spec's
`.markdownlint-cli2.jsonc` section is amended:
*"Rule overrides require a one-line rationale recorded in
`.markdownlint-cli2.jsonc` (as JSON-line comments). Rule disables
that hide rather than encode discipline are forbidden — if a rule
is disabled, the rationale must explain *why* the rule does not
apply to this project, not "we couldn't be bothered to comply.""*

### M6 — `bump/<lean-version>` is ambiguous between Lean / mathlib / CSLib

**Response: fixed.** Branch-prefix table is amended: the bump
prefix is `bump/<dep>-<version>` (e.g. `bump/lean-v4.30.0-rc1`,
`bump/mathlib-2026-04-01`, `bump/cslib-v4.30.0-rc2`). The
explicit `<dep>` token disambiguates.

### M7 — Release-branch prefix unspecified

**Response: fixed.** Add a sentence: "Releases are tag-only (the
existing `create-release.yml` workflow fires on tag creation);
no `release/` topic-branch prefix exists. Tag creation itself is
a `chore/` workstream that lands a release-notes change before
the tag is pushed."

### M8 — `.session/`-referencing in-flight artefacts

**Response: fixed.** Triage-execution sub-section is amended:
"Before deleting a `.session/<name>.md` file, `grep -r
'.session/<name>'` across `docs/superpowers/`, `docs/`,
`README.md`, and `CLAUDE.md` to find inbound references; either
update each reference to point at the new home (`TODO.md`,
`docs/index.md`, etc.) or migrate the referenced content first."

### M9 — Adversarial-review loop has no termination cap

**Response: fixed.** Add a paragraph: "If the cycle count
reaches three without convergence, the author surfaces the open
findings to the user with the author's proposed disposition, and
the user decides whether to continue iterating, accept the
remaining findings as cosmetic-taste-rejected, or revise the
spec at a higher level. The author's
`rejected (cosmetic-taste)` is the author's call; reviewers
cannot re-raise the same finding twice across cycles."

### M10 — `docs/process.md` § Comment and docstring style — index vs authoritative

**Response: fixed (rolled into M4).** Same authoritative/index
tagging applies.

### M11 — `clone` rule path-resolution semantics under-specified

**Response: fixed.** Replace "non-`.` path" with the precise
rule: "the target argument resolves to an absolute path that
does not equal `$PWD` and does not have `$PWD` as a prefix."

## Cosmetic-taste

### C1 — Mid-sentence interpretation (false alarm)

**Response: noted.** The reviewer self-withdrew this finding
("False alarm; ignore."). No change required.

### C2 — "Date drafted: 2026-05-07"

**Response: rejected (cosmetic-taste).** Standard frontmatter for
spec docs; preserved.

### C3 — "Index-shaped at first" is informal

**Response: fixed.** Replace with "structured as an index, not
as authoritative text."

### C4 — "Universally-applicable parts" is opinionated

**Response: fixed.** Replace with "the parts of the
`geb-mathlib` design that do not depend on upstream-eligibility
infrastructure."
