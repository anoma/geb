#!/usr/bin/env bash
# pre-push.sh — manual pre-push checklist runner.
#
# Invoked explicitly by the user before each push, e.g.:
#   bash scripts/pre-push.sh && jj git push --remote origin -b <bookmark>
#
# jj 0.41 does not provide a documented pre-push hook that fires on
# `jj git push`, so this script is by-convention only. The "run
# pre-push.sh before every push" rule is recorded in CLAUDE.md and
# docs/process.md.
#
# The script halts on the first failed mechanical step. Steps 1–6 are
# mechanical checks; step 7 prints reminders for user-driven gates that
# cannot be mechanised.
#
# See .claude/rules/ci-and-workflow.md § Pre-push checklist.

set -euo pipefail

step() { printf '\n==> %s\n' "$1"; }

# Step 1: jj setup sanity.
step "Step 1: scripts/check-jj-setup.sh"
bash scripts/check-jj-setup.sh

# Step 2: build and test.
#
# `lake test` builds the GebLean and GebLeanTests libraries via the
# test driver's dependency graph, so a separate `lake build` would be
# redundant given current lakefile targets.
#
# If a subsequent lakefile addition introduces a target outside the
# test driver's dependency graph, add `lake build` explicitly before
# `lake test`.
step "Step 2: lake test"
lake test

# Step 3: lint (depends on lintDriver = "batteries/runLinter" in lakefile.toml).
step "Step 3: lake lint"
lake lint

# Step 4: doctoc TOC check.
#
# The rule (auto-maintained TOCs in `.md` files with multiple `##`
# headings) lives in .claude/rules/markdown-writing.md § Tables of
# contents. Skipped if doctoc is not installed.
step "Step 4: doctoc --check '**/*.md'"
if command -v doctoc >/dev/null 2>&1; then
  doctoc --check '**/*.md' \
    || { echo "doctoc TOCs out of date; run 'doctoc \"**/*.md\"' and re-commit." >&2; exit 1; }
else
  echo "doctoc not installed; skipping TOC check." >&2
fi

# Step 5: markdown lint.
#
# The single quotes around '**/*.md' are load-bearing: without them,
# the shell expands the glob before markdownlint-cli2 sees it,
# defeating --no-globs.
step "Step 5: markdownlint-cli2"
markdownlint-cli2 --config .markdownlint-cli2.jsonc --no-globs '**/*.md'

# Step 6: axiom check. A non-allowlisted axiom dependency fails the
# push.
step "Step 6: scripts/check-axioms.sh"
bash scripts/check-axioms.sh GebLean/ GebLeanTests/

# Step 7: user-driven gates (reminders, not mechanical checks).
step "Step 7: user-driven gates (reminders)"
cat <<'EOF'
Confirm before pushing:
  - lean4:golf and lean4:review ran on changed Lean code.
  - User reviewed the diff line-by-line.
  - The push target is `origin`, not `upstream`. Upstream
    receives commits only via PRs from origin
    (see .claude/rules/fork-upstream-flow.md § Operations).
EOF

printf '\npre-push: all mechanical steps passed.\n'
