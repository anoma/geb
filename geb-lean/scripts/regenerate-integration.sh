#!/usr/bin/env bash
#
# scripts/regenerate-integration.sh
#
# Regenerate the `integration` bookmark as a fan-in merge of `main`
# plus the tips of all currently-active topic branches whose
# changes are not already reachable from `main`.
#
# The integration bookmark is force-pushed to origin; main is never
# touched.
#
# Idempotent: running twice with no topic-branch changes produces
# the same integration commit.

set -euo pipefail

# Refresh lease state before touching the remote. Requires the
# `origin` remote to be configured; without it, the fetch fails
# loudly and the script aborts before any local rewrite.
jj git fetch --remote origin

# Guard against unborn `main` (e.g., on a freshly init'd repo
# before any commits land on main). The fan-in revset's
# `~ ::main` clauses depend on `::main` being a non-empty set;
# if main is unborn, this script's behaviour is undefined.
if [ -z "$(jj log -r main --no-graph -T 'change_id ++ "\n"' 2>/dev/null)" ]; then
  echo "regenerate-integration: 'main' bookmark unborn or missing; nothing to fan in" >&2
  exit 1
fi

# Revset contract: select topic-branch tips whose changes are not
# yet reachable from `main`:
#
#   main | bookmarks(glob:"feat/*") ~ ::main
#        | bookmarks(glob:"fix/*") ~ ::main
#        | ...
#
# jj revset operator precedence (per
# https://docs.jj-vcs.dev/latest/revsets/, "Operators" table):
# `~` (set difference) binds tighter than `|` (union), so the
# above parses as
#   main | (bookmarks(glob:"feat/*") ~ ::main) | ...
# The explicit-parenthesis form is used below for clarity.
#
# Build the merge-arg list using bookmark names directly, matching
# the canonical form `jj new b1 b2 b3 ... bN -m`.
# Empty-glob handling: jj evaluates `bookmarks(glob:"X/*") ~ ::main`
# as the empty revset when no matching bookmarks exist; jj's
# argument expansion of an empty revset is a no-op. The minimal
# fan-in is just `main` if no topic branches are active.

# shellcheck source=scripts/lib/topic-revset.sh
. "$(dirname "$0")/lib/topic-revset.sh"

revset="main | $TOPIC_TIPS_NOT_ON_MAIN_REVSET"

# Resolve the revset to commit IDs to pass to `jj new`. Using
# commit_id rather than change_id (jj new accepts either, but
# commit_id is more stable for scripts that may be retried).
parents=$(jj log -r "$revset" -T 'commit_id ++ " "' --no-graph)

if [ -z "$(echo "$parents" | tr -d '[:space:]')" ]; then
  echo "regenerate-integration: empty revset (no main? misconfiguration)" >&2
  exit 1
fi

# Fan-in merge into a new commit.
# shellcheck disable=SC2086  # parents must word-split into args
jj new $parents -m "integration: fan-in @ $(date -I)"

# Move the bookmark to the new fan-in commit. Each regeneration
# produces a new fan-in that is a sibling of the previous one
# (not its descendant — the old fan-in is intentionally orphaned
# and garbage-collected). `--allow-backwards` permits jj to move
# the bookmark to a non-descendant revision; without it, jj
# refuses with "Refusing to move bookmark backwards or sideways"
# on every regeneration after the first.
jj bookmark set integration -r @ --allow-backwards

# Move @ off the fan-in commit. Without this, the working copy is
# integration: jj's snapshot-on-every-command would amend the
# fan-in in place, and the bookmark (anchored to @) would silently
# follow. Returning @ to main matches the semantics that
# regeneration is a side operation that doesn't belong to any
# topic branch.
jj new main

# Push (lease-protected; jj uses git's force-with-lease semantics
# and has no separate --force flag). First-time push auto-tracks
# `integration` via the local remotes.origin.auto-track-bookmarks
# setting; the -b <name> form also auto-tracks on first push
# without that setting.
jj git push --remote origin -b integration
