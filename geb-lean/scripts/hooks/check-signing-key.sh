#!/usr/bin/env bash
# check-signing-key.sh — SessionStart hook.  If commit signing is configured
# on either git's or jj's side and the signing key is not ready (gpg-agent
# cache miss, or ssh-agent without identities), emits a hook-JSON note.
# Never blocks; exit 0 in all paths.

set -u

# Emit a Claude Code hook JSON document carrying $1 as both a user-visible
# note (systemMessage) and session context (additionalContext).  $1 must
# not contain JSON-significant characters (double quotes, backslashes).
note() {
  printf '{"systemMessage": "%s", "hookSpecificOutput": {"hookEventName": "SessionStart", "additionalContext": "%s"}}\n' "$1" "$1"
}

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
    command -v gpg >/dev/null 2>&1 || exit 0
    command -v gpg-connect-agent >/dev/null 2>&1 || exit 0

    # The configured signing key; jj's signing.key takes precedence, then
    # git's user.signingkey.  Empty selects all local secret keys.
    key=""
    if command -v jj >/dev/null 2>&1; then
      key=$(jj config get signing.key 2>/dev/null || true)
    fi
    if [[ -z "$key" ]]; then
      key=$(git config --get user.signingkey 2>/dev/null || true)
    fi

    # Keygrips of the sign-capable components of the signing key (of all
    # secret keys when no key is configured): a grp record carries the grip
    # of the immediately preceding sec/ssb record, whose field 12 holds the
    # per-key capability letters (lowercase s = sign).
    grips=$(gpg --with-colons --list-secret-keys ${key:+"$key"} 2>/dev/null \
      | awk -F: '$1 == "sec" || $1 == "ssb" { cap = $12 }
                 $1 == "grp" && cap ~ /s/ { print $10 }')
    if [[ -z "$grips" ]]; then
      note "Note: gpg commit signing is configured but no sign-capable secret key matches the configured signing key, so any commit attempt will fail to sign."
      exit 0
    fi

    # Keygrips whose passphrase gpg-agent currently caches: KEYINFO cached
    # flag, field 7 of gpg-connect-agent's 'S KEYINFO <grip> ...' lines.
    cached=$(gpg-connect-agent 'keyinfo --list' /bye 2>/dev/null \
      | awk '$2 == "KEYINFO" && $7 == "1" { print $3 }')
    for grip in $grips; do
      if grep -qxF "$grip" <<<"$cached"; then
        exit 0
      fi
    done
    note "Note: gpg commit signing is configured but the signing key is not cached, so any automated commit attempt will block."
    ;;
  ssh)
    # If SSH_AUTH_SOCK is set, check that the agent has identities; if unset,
    # the user's ssh-agent setup is local-policy and we don't inspect it.
    if [[ -n "${SSH_AUTH_SOCK:-}" ]] && command -v ssh-add >/dev/null 2>&1; then
      if ! ssh-add -l >/dev/null 2>&1; then
        note "Note: ssh commit signing is configured but ssh-agent reports no usable identities, so commit attempts may fail to sign."
      fi
    fi
    ;;
esac

exit 0
