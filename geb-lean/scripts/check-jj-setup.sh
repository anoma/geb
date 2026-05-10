#!/usr/bin/env bash
# check-jj-setup.sh — verify jj colocated configuration matches the
# project's expectations. Each failure prints a diagnostic naming
# docs/process.md § jj colocated mode and exits non-zero.

set -u
fail() { printf 'check-jj-setup: %s\n' "$1" >&2; printf '  see docs/process.md § jj colocated mode\n' >&2; exit 1; }

# Precondition: jj is on PATH and the repo is jj-initialised.
command -v jj >/dev/null 2>&1 || fail "'jj' not found on PATH"

# Confirm jj sees this directory as a repo.
jj root >/dev/null 2>&1 || fail "this directory is not a jj repository (run 'jj git init --colocate' first)"

# (a) git.private-commits = conflicts()
priv=$(jj config list --repo git.private-commits 2>/dev/null) \
  || fail "'jj config list --repo git.private-commits' failed"
# `jj config list` prints e.g. `git.private-commits = "conflicts()"`.
# Anchor: extract the right-hand side and require equality with conflicts().
priv_value=$(printf '%s\n' "$priv" | sed -n 's/^git\.private-commits *= *"\(.*\)"$/\1/p')
[[ "$priv_value" == "conflicts()" ]] \
  || fail "git.private-commits is not exactly \"conflicts()\" (got: $priv)"

# (b) remotes.origin.fetch-tags = glob:cutover-*
tags=$(jj config list --repo remotes.origin.fetch-tags 2>/dev/null) \
  || fail "'jj config list --repo remotes.origin.fetch-tags' failed"
tags_value=$(printf '%s\n' "$tags" | sed -n 's/^remotes\.origin\.fetch-tags *= *"\(.*\)"$/\1/p')
[[ "$tags_value" == "glob:cutover-*" ]] \
  || fail "remotes.origin.fetch-tags is not exactly \"glob:cutover-*\" (got: $tags)"

# (c) signing is active (jj signing.behavior OR git commit.gpgsign).
sig_jj=$(jj config get signing.behavior 2>/dev/null || true)
sig_git=$(git config --get commit.gpgsign 2>/dev/null || true)
case "$sig_jj" in
  own|force) signing_ok=1 ;;
  *)
    if [[ "$sig_git" == "true" ]]; then signing_ok=1; else signing_ok=0; fi
    ;;
esac
(( signing_ok )) || fail "signing not active (jj signing.behavior is '$sig_jj', git commit.gpgsign is '$sig_git')"

echo "check-jj-setup: OK"
