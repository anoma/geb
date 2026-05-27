#!/usr/bin/env bash
# pre-commit.sh — Lean-triad pre-commit check.
#
# Invoked explicitly before each commit that touches a `.lean` file,
# e.g.:
#   bash scripts/pre-commit.sh && jj commit -m '<message>'
#
# Runs the subset of checks whose results can change as a consequence
# of Lean edits. For commits that touch only Markdown, scripts, or
# other non-Lean files, this script is not required; the full
# `scripts/pre-push.sh` superset (markdownlint, doctoc,
# check-axioms.sh, user-driven gates) is still mandatory before push.
#
# See .claude/rules/ci-and-workflow.md § Pre-commit checklist.

set -euo pipefail

step() { printf '\n==> %s\n' "$1"; }

# `lake test` builds the GebLean and GebLeanTests libraries via the
# test driver's dependency graph, so a separate `lake build` is
# redundant given current lakefile targets. Mirrors pre-push.sh's
# Step 2 by design: if a subsequent lakefile addition introduces a
# target outside the test driver's dependency graph, add `lake build`
# explicitly here and in pre-push.sh in lockstep.
step "Step 1: lake test"
lake test

# Lint (depends on lintDriver = "batteries/runLinter" in lakefile.toml).
step "Step 2: lake lint"
lake lint

printf '\npre-commit: Lean triad passed.\n'
