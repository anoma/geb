# Adversarial review — cycle 3

**Artefact reviewed:**
`plans/2026-05-09-process-bootstrap-monorepo-plan.md`

**Cross-referenced against:**
`docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`

Findings: 0 Blocker / 1 Serious / 2 Minor / 0 Cosmetic-taste

---

## S1 — B1 step 3: file edit precedes `jj new`, so edit lands on wrong change

**Location:** Task B1, Step 3 (≈ line 2463).

**Finding (Serious):**

Step 1 edits `.session/README.md` while `@` is whatever
change the implementer enters Milestone B on. Step 3 then
runs:

```sh
jj new -r main
jj bookmark create docs/session-milestone-a-note -r @
jj describe -m "..."
```

`jj new -r main` creates a new empty change whose parent is
`main` and sets `@` to it. The working-copy snapshot of
the edit is already recorded in the *previous* `@` change
(whatever `@` pointed at before `jj new`). The new `@`
change has an empty diff; the `.session/README.md` edit is
absent from it. `jj describe` then produces a commit with
no content change on `docs/session-milestone-a-note`.

Compare B4 step 2, which correctly runs `jj new -r main`
*before* `rm -rf .session/`; B4's edit therefore lands on
the new change.

**Required fix:** in B1 step 3, move the file edit to occur
*after* `jj new -r main`, not before it. The corrected
sequence is:

```sh
jj new -r main
jj bookmark create docs/session-milestone-a-note -r @
# (edit .session/README.md here)
jj describe -m "doc(session): add post-Milestone-A transitional note"
```

Step 1 of B1 should be moved inside step 3 (after `jj new`),
or step 3 should be restructured to make the ordering
unambiguous.

---

## M1 — A12 / A28: `git check-ignore -v` exits 1 on not-ignored paths

**Location:** Task A12, Step 2 (≈ line 1106); Task A28,
Step 1, item 10 (≈ line 2117).

**Finding (Minor):**

`git check-ignore -v` exits with code 0 when the path is
ignored, and with code 1 when the path is not ignored.
Both A12 step 2 and A28 item 10 include the calls:

```sh
git check-ignore -v geb-lean/.claude/settings.json
git check-ignore -v geb-lean/.claude/rules/lean-coding.md
```

for paths that are expected to be NOT ignored after A12
lands. These calls exit 1, which is the correct signal for
"not ignored" — but the plan presents them as unguarded
commands in a shell block without noting the non-zero exit
expectation. An implementer scripting the checklist (e.g.,
with `set -e` or sequential `&&` chaining) will see the
first call abort the block as a failure even when the path
is correctly not ignored.

The third call (`geb-lean/.claude/settings.local.json`,
expected to be ignored) exits 0 and presents no issue.

**Suggested fix:** prefix the two "not ignored" calls with
negation or add an explicit note:

```sh
! git check-ignore -v geb-lean/.claude/settings.json
! git check-ignore -v geb-lean/.claude/rules/lean-coding.md
git check-ignore -v geb-lean/.claude/settings.local.json
```

Or document that exit code 1 is the expected success
condition for the first two calls.

---

## M2 — B1 step 2: inaccurate explanation of `--config` omission

**Location:** Task B1, Step 2 (≈ line 2453).

**Finding (Minor):**

The step states: "No `--config` flag: the bare invocation
applies only the built-in defaults." This is inaccurate.
`markdownlint-cli2` auto-discovers `.markdownlint-cli2.jsonc`
from the CWD and applies it even without `--config`. The
config IS loaded; it is not "built-in defaults."

The command still works correctly regardless: when a path is
passed explicitly via `--no-globs`, `markdownlint-cli2`
lints the file even if it appears in the `ignores` array of
the auto-discovered config. Empirically verified: running
`markdownlint-cli2 --no-globs '.session/README.md'` from
`geb-lean/` (where `.markdownlint-cli2.jsonc` is
auto-discovered) lints the file (1 file, 0 errors), despite
`.session/**` being in `ignores`.

The accurate explanation is: "The `ignores` array in
`.markdownlint-cli2.jsonc` lists `.session/**`, but paths
passed explicitly via `--no-globs` bypass the `ignores`
filter, so `.session/README.md` is linted regardless of the
config."

The inaccurate explanation could mislead an implementer into
thinking they must omit `--config` for the command to work
(it would work identically with `--config`).
