# Adversarial review cycle 1 — 2026-05-09 process-bootstrap monorepo plan

**Reviewer**: fresh-context Agent.
**Plan under review**:
`plans/2026-05-09-process-bootstrap-monorepo-plan.md`.
**Convergence threshold**: zero blocker / serious / minor findings
(cosmetic-taste excluded).

## Summary

The plan is broadly well-structured and aligns with the spec on
architecture, task ordering, and verification design. Four defects
require fixes before implementation begins. One is a blocker (C6
silently produces an incomplete commit). Two are serious: a SHA
verification gate in A4 that false-passes when file paths are wrong,
and A27's missing JSON skeleton for `settings.json`, leaving the hook
wiring unverifiable from the plan alone. One minor finding: the A22
verification uses `~170 lines` where the spec says `~150 lines`. An
additional minor finding is that B1's markdownlint step silently skips
the file it is meant to lint. Two further minor findings concern the
spec divergence on `git mv` versus `git rm` + create (C6), and the
awkward placement of the no-nested-`CLAUDE.md` rule inside the
link-conventions item of A16.

## Blocker findings

### B-1: C6 Step 5 silently omits staging the new parent-level workflow file

**Task C6**, Step 5 (`Commit both changes together`):

```sh
git commit -m \
  "ci: promote lean_action_ci.yml to parent with geb-lean path filter"
```

Step 2 runs `git rm .github/workflows/lean_action_ci.yml` from
`geb-lean/`, which auto-stages the deletion in the single shared
git repo. Step 3 creates
`geb/.github/workflows/lean_action_ci.yml` — a new untracked file.
**No `git -C .. add` step stages this new file before Step 5's
commit.** An implementer following the plan literally commits only the
deletion; the promoted file is left as an untracked working-tree
artefact. The resulting commit is wrong and the verification
condition (`geb/.github/workflows/lean_action_ci.yml` exists) cannot
pass after a checkout of that commit.

**Fix**: insert between Step 4 and Step 5:

```sh
git -C .. add .github/workflows/lean_action_ci.yml
```

## Serious findings

### S-1: A4 Step 2 SHA verification has wrong paths and broken logic

**Task A4**, Step 2:

```sh
! grep '<SHA>' ../geb/.github/workflows/markdown-lint.yml \
  2>/dev/null || \
! grep '<SHA>' geb/.github/workflows/markdown-lint.yml
```

The plan's CWD throughout Milestone A is `geb-lean/`. From that
directory `../geb/.github/` resolves to a path that does not exist
(it would require a `geb/geb/` directory); the correct path is
`../.github/workflows/markdown-lint.yml`. The second path
`geb/.github/workflows/markdown-lint.yml` is also wrong from
`geb-lean/` (it resolves inside `geb-lean/geb/` which does not
exist).

The `||` operator makes the check a logical OR: if the first `!
grep` exit-0 (because the file at path 1 does not exist and
`2>/dev/null` silences the error, making grep return 1, and `!`
inverts to 0), the check passes via short-circuit without examining
the actual workflow file. An implementer can ship a workflow that
still contains `<SHA>` and this step reports success.

**Fix**: replace the step with a single, unambiguous check from the
plan's CWD:

```sh
! grep '<SHA>' ../.github/workflows/markdown-lint.yml
```

### S-2: A27 settings.json — no JSON skeleton provided

**Task A27**, Step 1 instructs the implementer to "author the
settings file" and names the two hooks (`PreToolUse`,
`SessionStart`) but provides no JSON structure. The verification
step (`json.load(...)`) only checks that the file is
JSON-parseable, not that it uses the correct Claude Code hook-wiring
schema. If the implementer writes an invalid schema (wrong key
names, wrong event-name strings, wrong path format), the hooks
never fire, and the A28 smoke-test for item 12 is the only safety
net — but that test feeds payloads directly to the hook script
executable, bypassing the settings-wiring entirely, so it would
still pass.

Neither the plan nor the spec shows the JSON skeleton. The spec
§ Hooks states that hooks resolve to
`${CLAUDE_PROJECT_DIR}/scripts/hooks/<name>.sh` but does not show
the `settings.json` format.

**Fix**: add a concrete JSON skeleton to Step 1, for example:

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command":
              "${CLAUDE_PROJECT_DIR}/scripts/hooks/block-mutating-git.sh"
          }
        ]
      }
    ],
    "SessionStart": [
      {
        "hooks": [
          {
            "type": "command",
            "command":
              "${CLAUDE_PROJECT_DIR}/scripts/hooks/check-signing-key.sh"
          }
        ]
      }
    ]
  }
}
```

(Exact field names should be verified against the Claude Code
`settings.json` documentation before committing. The plan's
verification step should be extended to also check that both event
names and at least one path are present in the loaded JSON.)

## Minor findings

### M-1: A22 verification relaxes the spec's README line-length target

**Task A22a** Step 3 verification says `geb-lean/README.md` "is
under ~170 lines". The spec § `README.md` sets the target at
`~150 lines`. The plan silently raises the threshold by 20 lines
with no stated justification.

**Fix**: change the verification criterion to `~150 lines` (matching
the spec), or document the deviation with a rationale.

### M-2: B1 markdownlint step silently skips `.session/README.md`

**Task B1**, Step 2 runs:

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  --no-globs '.session/README.md'
```

The config rewritten at C4 lists `.session/**` in its `ignores`
array. `markdownlint-cli2` honours the ignores even for explicitly
named CLI arguments, so the command exits 0 without linting the
file. The step provides false verification confidence.

**Fix**: either drop the markdownlint step from B1 (accepting that
`.session/README.md` is exempt from lint since it is imminently
deleted), or suppress the ignore for this one invocation via
`--ignore-path /dev/null` or similar.

### M-3: C6 deviates from the spec's "via `git mv`" description

The spec's cleanup-task table (§ Cleanup tasks) describes
`C-lean-action-ci-promote` as moving the file "via `git mv`".
The plan instead uses `git rm` (Step 2) and creates a new file
(Step 3). Both approaches produce identical commit content, but the
plan diverges from the spec's stated mechanism without acknowledging
it. (A true cross-directory `git mv` from the repo root is feasible
since `geb-lean/` and `geb/` share a single git repo.)

**Fix**: either add a note in C6 acknowledging the deviation and its
rationale, or rewrite C6 Steps 2–3 to use
`git mv .github/workflows/lean_action_ci.yml ../.github/workflows/lean_action_ci.yml`
followed by editing the promoted file in place.

### M-4: A16 item 8 mislocates the no-nested-`CLAUDE.md` rule

**Task A16**, Step 1 appends "no nested `CLAUDE.md` files are
permitted" as an addendum to item 8 (Link conventions). This rule
has no semantic relationship to link conventions. The spec
§ `CLAUDE.md` content says the rule is "replicated in
`.claude/rules/markdown-writing.md`" but does not assign it to
item 8. An implementer following the plan will embed an unrelated
rule inside a different rule's body rather than as a standalone item.

**Fix**: list the no-nested-`CLAUDE.md` rule as a separate
standalone item in `markdown-writing.md`, outside the link-
conventions item.

## Cosmetic-taste (NOT counted toward convergence; report only if obvious)

None.
