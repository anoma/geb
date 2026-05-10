#!/usr/bin/env bash
# check-signing-key.sh — SessionStart hook.  Warms the gpg-agent / ssh-agent
# if commit signing is configured on either git's or jj's side.  Never
# blocks; exit 0 in all paths.

set -u

# Determine if signing is active on either side.
git_signing=""
if command -v git >/dev/null 2>&1; then
  git_signing=$(git config --get commit.gpgsign 2>/dev/null || true)
fi

jj_signing=""
if command -v jj >/dev/null 2>&1; then
  jj_signing=$(jj config get signing.behavior 2>/dev/null || true)
fi

active=0
case "$git_signing" in true) active=1 ;; esac
case "$jj_signing" in own|force) active=1 ;; esac

(( active )) || exit 0

# Determine the signing backend.  jj's signing.backend takes precedence if
# set; otherwise git's gpg.format (the user-level git config) drives it.
backend=""
if command -v jj >/dev/null 2>&1; then
  backend=$(jj config get signing.backend 2>/dev/null || true)
fi
if [[ -z "$backend" ]]; then
  fmt=$(git config --get gpg.format 2>/dev/null || true)
  case "$fmt" in
    ssh) backend=ssh ;;
    *)   backend=gpg ;;  # default to gpg if unset or 'openpgp'
  esac
fi

case "$backend" in
  gpg)
    if command -v gpg-connect-agent >/dev/null 2>&1; then
      if ! gpg-connect-agent 'keyinfo --list' /bye 2>/dev/null | grep -q ' 1 '; then
        # Cache miss: prompt pinentry by performing a small no-op signature.
        echo warm | gpg --clearsign >/dev/null 2>&1 || true
      fi
    fi
    ;;
  ssh)
    # ssh-agent priming.  If SSH_AUTH_SOCK is set, list keys; if empty, the
    # user's ssh-agent setup is local-policy and we don't try to seed it.
    if [[ -n "${SSH_AUTH_SOCK:-}" ]] && command -v ssh-add >/dev/null 2>&1; then
      ssh-add -l >/dev/null 2>&1 || true
    fi
    ;;
esac

exit 0
